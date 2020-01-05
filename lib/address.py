# Electron Cash - lightweight Bitcoin client
# Copyright (C) 2017 The Electron Cash Developers
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

# Many of the functions in this file are copied from ElectrumX

from collections import namedtuple
import hashlib
import struct

from . import cashaddr, constants
from enum import IntEnum

_sha256 = hashlib.sha256
_new_hash = hashlib.new
hex_to_bytes = bytes.fromhex


class AddressError(Exception):
    '''Exception used for Address errors.'''

class ScriptError(Exception):
    '''Exception used for Script errors.'''


# Derived from Zclassic script.h
class OpCodes(IntEnum):
    # push value
    OP_0 = 0x00
    OP_FALSE = OP_0
    OP_PUSHDATA1 = 0x4c
    OP_PUSHDATA2 = 0x4d
    OP_PUSHDATA4 = 0x4e
    OP_1NEGATE = 0x4f
    OP_RESERVED = 0x50
    OP_1 = 0x51
    OP_TRUE=OP_1
    OP_2 = 0x52
    OP_3 = 0x53
    OP_4 = 0x54
    OP_5 = 0x55
    OP_6 = 0x56
    OP_7 = 0x57
    OP_8 = 0x58
    OP_9 = 0x59
    OP_10 = 0x5a
    OP_11 = 0x5b
    OP_12 = 0x5c
    OP_13 = 0x5d
    OP_14 = 0x5e
    OP_15 = 0x5f
    OP_16 = 0x60

    # control
    OP_NOP = 0x61
    OP_VER = 0x62
    OP_IF = 0x63
    OP_NOTIF = 0x64
    OP_VERIF = 0x65
    OP_VERNOTIF = 0x66
    OP_ELSE = 0x67
    OP_ENDIF = 0x68
    OP_VERIFY = 0x69
    OP_RETURN = 0x6a

    # stack ops
    OP_TOALTSTACK = 0x6b
    OP_FROMALTSTACK = 0x6c
    OP_2DROP = 0x6d
    OP_2DUP = 0x6e
    OP_3DUP = 0x6f
    OP_2OVER = 0x70
    OP_2ROT = 0x71
    OP_2SWAP = 0x72
    OP_IFDUP = 0x73
    OP_DEPTH = 0x74
    OP_DROP = 0x75
    OP_DUP = 0x76
    OP_NIP = 0x77
    OP_OVER = 0x78
    OP_PICK = 0x79
    OP_ROLL = 0x7a
    OP_ROT = 0x7b
    OP_SWAP = 0x7c
    OP_TUCK = 0x7d

    # splice ops
    OP_CAT = 0x7e
    OP_SUBSTR = 0x7f
    OP_LEFT = 0x80
    OP_RIGHT = 0x81
    OP_SIZE = 0x82

    # bit logic
    OP_INVERT = 0x83
    OP_AND = 0x84
    OP_OR = 0x85
    OP_XOR = 0x86
    OP_EQUAL = 0x87
    OP_EQUALVERIFY = 0x88
    OP_RESERVED1 = 0x89
    OP_RESERVED2 = 0x8a

    # numeric
    OP_1ADD = 0x8b
    OP_1SUB = 0x8c
    OP_2MUL = 0x8d
    OP_2DIV = 0x8e
    OP_NEGATE = 0x8f
    OP_ABS = 0x90
    OP_NOT = 0x91
    OP_0NOTEQUAL = 0x92

    OP_ADD = 0x93
    OP_SUB = 0x94
    OP_MUL = 0x95
    OP_DIV = 0x96
    OP_MOD = 0x97
    OP_LSHIFT = 0x98
    OP_RSHIFT = 0x99

    OP_BOOLAND = 0x9a
    OP_BOOLOR = 0x9b
    OP_NUMEQUAL = 0x9c
    OP_NUMEQUALVERIFY = 0x9d
    OP_NUMNOTEQUAL = 0x9e
    OP_LESSTHAN = 0x9f
    OP_GREATERTHAN = 0xa0
    OP_LESSTHANOREQUAL = 0xa1
    OP_GREATERTHANOREQUAL = 0xa2
    OP_MIN = 0xa3
    OP_MAX = 0xa4

    OP_WITHIN = 0xa5

    # crypto
    OP_RIPEMD160 = 0xa6
    OP_SHA1 = 0xa7
    OP_SHA256 = 0xa8
    OP_HASH160 = 0xa9
    OP_HASH256 = 0xaa
    OP_CODESEPARATOR = 0xab
    OP_CHECKSIG = 0xac
    OP_CHECKSIGVERIFY = 0xad
    OP_CHECKMULTISIG = 0xae
    OP_CHECKMULTISIGVERIFY = 0xaf

    # expansion
    OP_NOP1 = 0xb0
    OP_NOP2 = 0xb1
    OP_CHECKLOCKTIMEVERIFY = OP_NOP2
    OP_NOP3 = 0xb2
    OP_NOP4 = 0xb3
    OP_NOP5 = 0xb4
    OP_NOP6 = 0xb5
    OP_NOP7 = 0xb6
    OP_NOP8 = 0xb7
    OP_NOP9 = 0xb8
    OP_NOP10 = 0xb9


    # template matching params
    OP_SMALLINTEGER = 0xfa
    OP_PUBKEYS = 0xfb
    OP_PUBKEYHASH = 0xfd
    OP_PUBKEY = 0xfe

    OP_INVALIDOPCODE = 0xff


P2PKH_prefix = bytes([OpCodes.OP_DUP, OpCodes.OP_HASH160, 20])
P2PKH_suffix = bytes([OpCodes.OP_EQUALVERIFY, OpCodes.OP_CHECKSIG])

P2SH_prefix = bytes([OpCodes.OP_HASH160, 20])
P2SH_suffix = bytes([OpCodes.OP_EQUAL])

# Utility functions

def to_bytes(x):
    '''Convert to bytes which is hashable.'''
    if isinstance(x, bytes):
        return x
    if isinstance(x, bytearray):
        return bytes(x)
    raise TypeError('{} is not bytes ({})'.format(x, type(x)))

def hash_to_hex_str(x):
    '''Convert a big-endian binary hash to displayed hex string.

    Display form of a binary hash is reversed and converted to hex.
    '''
    return bytes(reversed(x)).hex()

def hex_str_to_hash(x):
    '''Convert a displayed hex string to a binary hash.'''
    return bytes(reversed(hex_to_bytes(x)))

def bytes_to_int(be_bytes):
    '''Interprets a big-endian sequence of bytes as an integer'''
    return int.from_bytes(be_bytes, 'big')

def int_to_bytes(value):
    '''Converts an integer to a big-endian sequence of bytes'''
    return value.to_bytes((value.bit_length() + 7) // 8, 'big')

def sha256(x):
    '''Simple wrapper of hashlib sha256.'''
    return _sha256(x).digest()

def double_sha256(x):
    '''SHA-256 of SHA-256, as used extensively in bitcoin.'''
    return sha256(sha256(x))

def ripemd160(x):
    '''Simple wrapper of hashlib ripemd160.'''
    h = _new_hash('ripemd160')
    h.update(x)
    return h.digest()

def hash160(x):
    '''RIPEMD-160 of SHA-256.

    Used to make bitcoin addresses from pubkeys.'''
    return ripemd160(sha256(x))


class UnknownAddress(object):

    def to_ui_string(self):
        return '<UnknownAddress>'

    def __str__(self):
        return self.to_ui_string()

    def __repr__(self):
        return '<UnknownAddress>'


class PublicKey(namedtuple("PublicKeyTuple", "pubkey")):

    @classmethod
    def from_pubkey(cls, pubkey):
        '''Create from a public key expressed as binary bytes.'''
        cls.validate(pubkey)
        return cls(to_bytes(pubkey))

    @classmethod
    def from_string(cls, string):
        '''Create from a hex string.'''
        return cls.from_pubkey(hex_to_bytes(string))

    @classmethod
    def validate(cls, pubkey, req_compressed=False):
        if not isinstance(pubkey, (bytes, bytearray)):
            raise AddressError('pubkey must be of bytes type, not {}'.format(type(pubkey)))
        if len(pubkey) == 33 and pubkey[0] in (2, 3):
            return  # Compressed
        if len(pubkey) == 65 and pubkey[0] == 4:
            if not req_compressed:
                return
            raise AddressError('compressed public keys are required')
        raise AddressError('invalid pubkey {}'.format(pubkey))

    def to_Address(self):
        '''Convert to an Address object.'''
        return Address(hash160(self.pubkey), cls.ADDR_P2PKH)

    def to_ui_string(self):
        '''Convert to a hexadecimal string.'''
        return self.pubkey.hex()

    def to_script(self):
        return Script.P2PK_script(self.pubkey)

    def __str__(self):
        return self.to_ui_string()

    def __repr__(self):
        return '<PubKey {}>'.format(self.__str__())


class ScriptOutput(namedtuple("ScriptAddressTuple", "script")):

    @classmethod
    def from_string(self, string):
        '''Instantiate from a mixture of opcodes and raw data.'''
        script = bytearray()
        for word in string.split():
            if word.startswith('OP_'):
                try:
                    opcode = OpCodes[word]
                except KeyError:
                    raise AddressError('unknown opcode {}'.format(word))
                script.append(opcode)
            elif word.lower().startswith('<empty>'):
                script.extend([ OpCodes.OP_PUSHDATA1, OpCodes.OP_0 ])
            else:
                import binascii
                script.extend(Script.push_data(binascii.unhexlify(word)))
        return ScriptOutput(bytes(script))

    def to_ui_string(self, hex_only = False):
        '''Convert to user-readable OP-codes (plus text), eg OP_RETURN (12) "Hello there!"
           Or, to a hexadecimal string if that fails.
           Note that this function is the inverse of from_string() only if called with hex_only = True!'''
        if self.script and not hex_only:
            try:
                ret = ''
                ops = Script.get_ops(self.script)
                def lookup(x):
                    try:
                        return OpCodes(x).name
                    except ValueError:
                        return '('+str(x)+')'
                for op in ops:
                    if ret: ret += ", "
                    if isinstance(op, tuple):
                        if op[1] is None:
                            ret += "<EMPTY>"
                        else:
                            if hex_only:
                                friendlystring = None
                            else:
                                # Attempt to make a friendly string, or fail to hex
                                try:
                                    # Ascii only
                                    friendlystring = op[1].decode('ascii') # raises UnicodeDecodeError with bytes > 127.

                                    # Count ugly characters (that need escaping in python strings' repr())
                                    uglies = 0
                                    for b in op[1]:
                                        if b < 0x20 or b == 0x7f:
                                            uglies += 1
                                    # Less than half of characters may be ugly.
                                    if 2*uglies >= len(op[1]):
                                        friendlystring = None
                                except UnicodeDecodeError:
                                    friendlystring = None

                            if friendlystring is None:
                                ret += lookup(op[0]) + " " + op[1].hex()
                            else:
                                ret += lookup(op[0]) + " " + repr(friendlystring)
                    elif isinstance(op, int):
                        ret += lookup(op)
                    else:
                        ret += '[' + (op.hex() if isinstance(op, bytes) else str(op)) + ']'
                return ret
            except ScriptError:
                # Truncated script -- so just default to normal 'hex' encoding below.
                pass
        return self.script.hex()

    def to_asm(self):
        '''Convert to user-readable OP-codes (plus text), eg OP_RETURN (12) Hello there!
           Or, to a hexadecimal string if that fails.
           Note that this function is the inverse of from_string() only if called with hex_only = True!'''
        if self.script:
            try:
                ret = ''
                ops = Script.get_ops(self.script)
                def lookup(x):
                    if not (x > OpCodes.OP_0 and x < OpCodes.OP_1NEGATE): # only display non-PUSHDATA opcodes 'NOT 0 < x < 79'
                        try: return OpCodes(x).name
                        except ValueError: return ''
                    return None
                for op in ops:
                    if ret: ret += " "
                    if isinstance(op, tuple):
                        if lookup(op[0]) is not None:
                            ret += lookup(op[0]) + " " + op[1].hex()
                        elif op[1] is None:
                            ret += "<EMPTY>"
                        else:
                            ret += op[1].hex()
                    elif isinstance(op, int):
                        ret += str(lookup(op))  # FIXME: Handle possible None return from lookup here! -Calin
                    else:
                        ret += '[' + (op.hex() if isinstance(op, bytes) else str(op)) + ']'
                return ret
            except ScriptError:
                raise Exception("Truncated script.")
                # Truncated script -- so just default to normal 'hex' encoding below.
                pass
        raise Exception("There is no script object to convert to ASM format.")

    def to_script(self):
        return self.script

    def __str__(self):
        return self.to_ui_string(True)

    def __repr__(self):
        return '<ScriptOutput {}>'.format(self.__str__())


# A namedtuple for easy comparison and unique hashing
class Address(namedtuple("AddressTuple", "hash160 kind")):

    # Address kinds
    ADDR_P2PKH = 0
    ADDR_P2SH = 1

    # Address formats
    FMT_ZCLASSIC = 0
    FMT_SLPADDR = 1

    _NUM_FMTS = 2  # <-- Be sure to update this to be 1+ last format above!

    # Default to CashAddr using 'zslp' or 'zslptest' prefix
    FMT_UI = FMT_SLPADDR

    def __new__(cls, hash160, kind):
        assert kind in (cls.ADDR_P2PKH, cls.ADDR_P2SH)
        hash160 = to_bytes(hash160)
        assert len(hash160) == 20
        ret = super().__new__(cls, hash160, kind)
        ret._addr2str_cache = [None] * cls._NUM_FMTS
        return ret

    @classmethod
    def show_cashaddr(cls, format):
        if format == 1:
            cls.FMT_UI = cls.FMT_SLPADDR
        else:
            cls.FMT_UI = cls.FMT_ZCLASSIC

    @classmethod
    def from_slpaddr_string(cls, string, *, net=None):
        '''Construct from a slpaddress string.'''
        if net is None: net = constants.net
        prefix = net.SLPADDR_PREFIX
        if string.upper() == string:
            prefix = prefix.upper()
        if ':' not in string:
            string = ':'.join([prefix, string])
        addr_prefix, kind, addr_hash = cashaddr.decode(string)
        if addr_prefix != prefix:
            raise AddressError('address has unexpected prefix {}'
                               .format(addr_prefix))
        if kind == cashaddr.PUBKEY_TYPE:
            return cls(addr_hash, cls.ADDR_P2PKH)
        elif kind == cashaddr.SCRIPT_TYPE:
            return cls(addr_hash, cls.ADDR_P2SH)
        else:
            raise AddressError('address has unexpected kind {}'.format(kind))

    @classmethod
    def from_string(cls, string, *, net=None):
        '''Construct from an address string.'''
        if net is None: net = constants.net
        if len(string) > 35:
            try:
                return cls.from_slpaddr_string(string, net=net)
            except ValueError as e:
                raise AddressError(str(e))

        try:
            raw = Base58.decode_check(string)
        except Base58Error as e:
            raise AddressError(str(e))

        # Require version byte(s) plus hash160.
        if len(raw) != 22:
            raise AddressError('invalid address: {}'.format(string))

        verbyte, hash160 = raw[0:2], raw[2:]
        if verbyte in [net.ADDRTYPE_P2PKH]:
            kind = cls.ADDR_P2PKH
        elif verbyte in [net.ADDRTYPE_P2SH]:
            kind = cls.ADDR_P2SH
        else:
            raise AddressError('unknown version byte: {}'.format(verbyte))

        return cls(hash160, kind)

    @classmethod
    def prefix_from_address_string(cls, string):
        '''Get address prefix from address string which may be missing the prefix.'''
        if len(string) > 35:
            try:
                cls.from_slpaddr_string(string)
                return constants.net.SLPADDR_PREFIX
            except: 
                pass
        return ''

    @classmethod
    def is_valid(cls, string, *, net=None):
        if net is None: net = constants.net
        try:
            cls.from_string(string, net=net)
            return True
        except Exception:
            return False

    @classmethod
    def from_strings(cls, strings, *, net=None):
        '''Construct a list from an iterable of strings.'''
        if net is None: net = constants.net
        return [cls.from_string(string, net=net) for string in strings]

    @classmethod
    def from_pubkey(cls, pubkey):
        '''Returns a P2PKH address from a public key.  The public key can
        be bytes or a hex string.'''
        if isinstance(pubkey, str):
            pubkey = hex_to_bytes(pubkey)
        PublicKey.validate(pubkey)
        return cls(hash160(pubkey), cls.ADDR_P2PKH)

    @classmethod
    def from_P2PKH_hash(cls, hash160):
        '''Construct from a P2PKH hash160.'''
        return cls(hash160, cls.ADDR_P2PKH)

    @classmethod
    def from_P2SH_hash(cls, hash160):
        '''Construct from a P2PKH hash160.'''
        return cls(hash160, cls.ADDR_P2SH)

    @classmethod
    def from_multisig_script(cls, script):
        return cls(hash160(script), cls.ADDR_P2SH)

    @classmethod
    def to_strings(cls, fmt, addrs):
        '''Construct a list of strings from an iterable of Address objects.'''
        return [addr.to_string(fmt) for addr in addrs]

    def to_slpaddr(self, *, net=None):
        if net is None: net = constants.net
        if self.kind == self.ADDR_P2PKH:
            kind  = cashaddr.PUBKEY_TYPE
        else:
            kind  = cashaddr.SCRIPT_TYPE
        return cashaddr.encode(net.SLPADDR_PREFIX, kind, self.hash160)

    def to_string(self, fmt, *, net=None):
        '''Converts to a string of the given format.'''
        if net is None: net = constants.net
        if net is constants.net:
            try:
                cached = self._addr2str_cache[fmt]
                if cached:
                    return cached
            except (IndexError, TypeError):
                raise AddressError('unrecognised format')

        try:
            cached = None

            if fmt == self.FMT_SLPADDR:
                cached = self.to_slpaddr(net=net)
                return cached

            if fmt == self.FMT_ZCLASSIC:
                if self.kind == self.ADDR_P2PKH:
                    verbyte = net.ADDRTYPE_P2PKH
                else:
                    verbyte = net.ADDRTYPE_P2SH
            else:
                # This should never be reached due to cache-lookup check above. But leaving it in as it's a harmless sanity check.
                raise AddressError('unrecognised format')

            cached = Base58.encode_check(verbyte + self.hash160)
            return cached
        finally:
            if cached and net is constants.net:
                self._addr2str_cache[fmt] = cached

    def to_full_string(self, fmt, *, net=None):
        '''Convert to text, with a URI prefix for cashaddr format.'''
        if net is None: net = constants.net
        text = self.to_string(fmt, net=net)
        if fmt == self.FMT_SLPADDR:
            text = ':'.join([net.SLPADDR_PREFIX, text])
        return text

    def to_ui_string(self, *, net=None):
        '''Convert to text in the current UI format choice.'''
        if net is None: net = constants.net
        return self.to_string(self.FMT_UI, net=net)

    def to_full_ui_string(self, *, net=None):
        '''Convert to text, with a URI prefix if cashaddr.'''
        if net is None: net = constants.net
        return self.to_full_string(self.FMT_UI, net=net)

    def to_URI_components(self, *, net=None):
        '''Returns a (scheme, path) pair for building a URI.'''
        if net is None: net = constants.net
        scheme = ""
        scheme2 = net.SLPADDR_PREFIX
        path = self.to_ui_string(net=net)
        if self.FMT_UI == self.FMT_SLPADDR:
            scheme = scheme2
        return scheme, path

    def to_storage_string(self, *, net=None):
        '''Convert to text in the storage format.'''
        if net is None: net = constants.net
        return self.to_string(self.FMT_ZCLASSIC, net=net)

    def to_script(self):
        '''Return a binary script to pay to the address.'''
        if self.kind == self.ADDR_P2PKH:
            return Script.P2PKH_script(self.hash160)
        else:
            return Script.P2SH_script(self.hash160)

    def to_script_hex(self):
        '''Return a script to pay to the address as a hex string.'''
        return self.to_script().hex()

    def to_scripthash(self):
        '''Returns the hash of the script in binary.'''
        return sha256(self.to_script())

    def to_scripthash_hex(self):
        '''Like other bitcoin hashes this is reversed when written in hex.'''
        return hash_to_hex_str(self.to_scripthash())

    def __str__(self):
        return self.to_ui_string()

    def __repr__(self):
        return '<Address {}>'.format(self.__str__())


class Script(object):

    @classmethod
    def P2SH_script(cls, hash160):
        assert len(hash160) == 20
        return P2SH_prefix + hash160 + P2SH_suffix

    @classmethod
    def P2PKH_script(cls, hash160):
        assert len(hash160) == 20
        return P2PKH_prefix + hash160 + P2PKH_suffix

    @classmethod
    def P2PK_script(cls, pubkey):
        return cls.push_data(pubkey) + bytes([OpCodes.OP_CHECKSIG])

    @classmethod
    def multisig_script(cls, m, pubkeys):
        '''Returns the script for a pay-to-multisig transaction.'''
        n = len(pubkeys)
        if not 1 <= m <= n <= 15:
            raise ScriptError('{:d} of {:d} multisig script not possible'
                              .format(m, n))
        for pubkey in pubkeys:
            PublicKey.validate(pubkey, req_compressed=True)
        # See https://bitcoin.org/en/developer-guide
        # 2 of 3 is: OP_2 pubkey1 pubkey2 pubkey3 OP_3 OP_CHECKMULTISIG
        return (bytes([OpCodes.OP_1 + m - 1])
                + b''.join(cls.push_data(pubkey) for pubkey in pubkeys)
                + bytes([OpCodes.OP_1 + n - 1, OpCodes.OP_CHECKMULTISIG]))

    @classmethod
    def push_data(cls, data):
        '''Returns the opcodes to push the data on the stack.'''
        assert isinstance(data, (bytes, bytearray))

        n = len(data)
        if n < OpCodes.OP_PUSHDATA1:
            return bytes([n]) + data
        if n < 256:
            return bytes([OpCodes.OP_PUSHDATA1, n]) + data
        if n < 65536:
            return bytes([OpCodes.OP_PUSHDATA2]) + struct.pack('<H', n) + data
        return bytes([OpCodes.OP_PUSHDATA4]) + struct.pack('<I', n) + data

    @classmethod
    def get_ops(cls, script):
        ops = []

        # The unpacks or script[n] below throw on truncated scripts
        try:
            n = 0
            while n < len(script):
                op = script[n]
                n += 1

                if op <= OpCodes.OP_PUSHDATA4:
                    # Raw bytes follow
                    if op < OpCodes.OP_PUSHDATA1:
                        dlen = op
                    elif op == OpCodes.OP_PUSHDATA1:
                        dlen = script[n]
                        n += 1
                    elif op == OpCodes.OP_PUSHDATA2:
                        dlen, = struct.unpack('<H', script[n: n + 2])
                        n += 2
                    else:
                        dlen, = struct.unpack('<I', script[n: n + 4])
                        n += 4
                    if n + dlen > len(script):
                        raise IndexError
                    if dlen > 0:
                        op = (op, script[n:n + dlen])
                    else:
                        op = (op, None)
                    n += dlen

                ops.append(op)
        except Exception:
            # Truncated script; e.g. tx_hash
            # ebc9fa1196a59e192352d76c0f6e73167046b9d37b8302b6bb6968dfd279b767
            raise ScriptError('truncated script')

        return ops


class Base58Error(Exception):
    '''Exception used for Base58 errors.'''


class Base58(object):
    '''Class providing base 58 functionality.'''

    chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
    assert len(chars) == 58
    cmap = {c: n for n, c in enumerate(chars)}

    @staticmethod
    def char_value(c):
        val = Base58.cmap.get(c)
        if val is None:
            raise Base58Error('invalid base 58 character "{}"'.format(c))
        return val

    @staticmethod
    def decode(txt):
        """Decodes txt into a big-endian bytearray."""
        if not isinstance(txt, str):
            raise TypeError('a string is required')

        if not txt:
            raise Base58Error('string cannot be empty')

        value = 0
        for c in txt:
            value = value * 58 + Base58.char_value(c)

        result = int_to_bytes(value)

        # Prepend leading zero bytes if necessary
        count = 0
        for c in txt:
            if c != '1':
                break
            count += 1
        if count:
            result = bytes(count) + result

        return result

    @staticmethod
    def encode(be_bytes):
        """Converts a big-endian bytearray into a base58 string."""
        value = bytes_to_int(be_bytes)

        txt = ''
        while value:
            value, mod = divmod(value, 58)
            txt += Base58.chars[mod]

        for byte in be_bytes:
            if byte != 0:
                break
            txt += '1'

        return txt[::-1]

    @staticmethod
    def decode_check(txt):
        '''Decodes a Base58Check-encoded string to a payload.  The version
        prefixes it.'''
        be_bytes = Base58.decode(txt)
        result, check = be_bytes[:-4], be_bytes[-4:]
        if check != double_sha256(result)[:4]:
            raise Base58Error('invalid base 58 checksum for {}'.format(txt))
        return result

    @staticmethod
    def encode_check(payload):
        """Encodes a payload bytearray (which includes the version byte(s))
        into a Base58Check string."""
        be_bytes = payload + double_sha256(payload)[:4]
        return Base58.encode(be_bytes)
