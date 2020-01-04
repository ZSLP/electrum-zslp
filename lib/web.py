
# Electrum - lightweight Bitcoin client
# Copyright (C) 2011 Thomas Voegtlin
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation files
# (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge,
# publish, distribute, sublicense, and/or sell copies of the Software,
# and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
# BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
# ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from decimal import Decimal
import os
import re
import shutil
import urllib
import threading

from .address import Address
from . import bitcoin
from . import constants
from .util import format_satoshis_plain, bh2u

mainnet_block_explorers = {
    'zeltrez.io': ('https://explorer.zcl.zeltrez.io/',
                        {'tx': 'tx/', 'addr': 'address/'})
}

testnet_block_explorers = {
    'testnet.z.cash': ('https://explorer.testnet.z.cash/',
                       {'tx': 'tx/', 'addr': 'address/'}),
    'system default': ('blockchain:/',
                       {'tx': 'tx/', 'addr': 'address/'}),
}

def block_explorer_info():
    from . import constants
    return testnet_block_explorers if constants.net.TESTNET else mainnet_block_explorers

def block_explorer(config):
    return config.get('block_explorer', 'zeltrez.io')

def block_explorer_tuple(config):
    return block_explorer_info().get(block_explorer(config))

def block_explorer_URL(config, kind, item):
    be_tuple = block_explorer_tuple(config)
    if not be_tuple:
        return
    kind_str = be_tuple[1].get(kind)
    if not kind_str:
        return
    url_parts = [be_tuple[0], kind_str, item]
    return ''.join(url_parts)

# URL decode
#_ud = re.compile('%([0-9a-hA-H]{2})', re.MULTILINE)
#urldecode = lambda x: _ud.sub(lambda m: chr(int(m.group(1), 16)), x)

def parse_URI(uri, on_pr=None):
    from .bitcoin import COIN

    if ':' not in uri:
        Address.from_string(uri)
        return {'address': uri}

    if 'zclassic' not in uri and constants.net.SLPADDR_PREFIX not in uri:
        raise Exception("Not a URI starting with 'zclassic:' or '{}:'".format(constants.net.SLPADDR_PREFIX))

    u = urllib.parse.urlparse(uri)
    address = u.path

    # python for android fails to parse query
    if address.find('?') > 0:
        address, query = u.path.split('?')
        pq = urllib.parse.parse_qs(query, keep_blank_values=True)
    else:
        pq = urllib.parse.parse_qs(u.query, keep_blank_values=True)

    for k, v in pq.items():
        if len(v)!=1:
            raise Exception('Duplicate Key', k)

    out = {k: v[0] for k, v in pq.items()}
    if address:
        if not bitcoin.is_address(address):
            raise Exception("Invalid Zclassic address:" + address)
        out['address'] = address
    if 'amount' in out:
        am = out['amount']
        m = re.match('([0-9\.]+)X([0-9])', am)
        if m:
            k = int(m.group(2)) - 8
            amount = Decimal(m.group(1)) * pow(  Decimal(10) , k)
        else:
            amount = Decimal(am) * COIN
        out['amount'] = int(amount)
    if 'message' in out:
        out['message'] = out['message']
        out['memo'] = out['message']
    if 'time' in out:
        out['time'] = int(out['time'])
    if 'exp' in out:
        out['exp'] = int(out['exp'])
    if 'sig' in out:
        out['sig'] = bh2u(bitcoin.base_decode(out['sig'], None, base=58))

    r = out.get('r')
    sig = out.get('sig')
    name = out.get('name')
    if on_pr and (r or (name and sig)):
        def get_payment_request_thread():
            from . import paymentrequest as pr
            if name and sig:
                s = pr.serialize_request(out).SerializeToString()
                request = pr.PaymentRequest(s)
            else:
                request = pr.get_payment_request(r)
            if on_pr:
                on_pr(request)
        t = threading.Thread(target=get_payment_request_thread)
        t.setDaemon(True)
        t.start()

    return out


def create_URI(addr, amount, message, *, op_return=None, op_return_raw=None, token_id=None):
    if not isinstance(addr, Address):
        return ""
    if op_return is not None and op_return_raw is not None:
        raise ValueError('Must specify exactly one of op_return or \
                            op_return_hex as kwargs to create_URI')
    scheme, path = addr.to_URI_components()
    query = []
    if token_id:
        query.append('amount=%s-%s'%( amount, token_id ))
    if amount:
        query.append('amount=%s'%format_satoshis_plain(amount))
    if message:
        query.append('message=%s'%urllib.parse.quote(message))
    if op_return:
        query.append(f'op_return={str(op_return)}')
    if op_return_raw:
        query.append(f'op_return_raw={str(op_return_raw)}')
    p = urllib.parse.ParseResult(scheme=scheme,
                                 netloc='', path=path, params='',
                                 query='&'.join(query), fragment='')
    return urllib.parse.urlunparse(p)
