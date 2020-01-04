# Electrum - lightweight ZClassic client
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

import binascii
import os, sys, re, json, time
from collections import defaultdict
from datetime import datetime
from decimal import Decimal
import decimal
import traceback
import inspect, weakref
import urllib
import threading
import hmac
from .address import Address
from . import constants
from .i18n import _

import urllib.request, urllib.parse, urllib.error
import queue
from locale import localeconv

def inv_dict(d):
    return {v: k for k, v in d.items()}


base_units = {'ZCL':8, 'mZCL':5, 'uZCL':2}

def normalize_version(v):
    return [int(x) for x in re.sub(r'(\.0+)*$','', v).split(".")]

class NotEnoughFunds(Exception): pass

class NotEnoughFundsSlp(Exception): pass

class NotEnoughUnfrozenFundsSlp(Exception): pass

class ExcessiveFee(Exception): pass

class NoDynamicFeeEstimates(Exception):
    def __str__(self):
        return _('Dynamic fee estimates not available')


class InvalidPassword(Exception):
    def __str__(self):
        return _("Incorrect password")


class FileImportFailed(Exception):
    def __init__(self, message=''):
        self.message = str(message)

    def __str__(self):
        return _("Failed to import from file.") + "\n" + self.message


class FileExportFailed(Exception):
    def __init__(self, message=''):
        self.message = str(message)

    def __str__(self):
        return _("Failed to export to file.") + "\n" + self.message


class TimeoutException(Exception):
    def __init__(self, message=''):
        self.message = str(message)

    def __str__(self):
        if not self.message:
            return _("Operation timed out.")
        return self.message


class WalletFileException(Exception): pass


class BitcoinException(Exception): pass


# Throw this exception to unwind the stack like when an error occurs.
# However unlike other exceptions the user won't be informed.
class UserCancelled(Exception):
    '''An exception that is suppressed from the user'''
    pass

class Satoshis(object):
    def __new__(cls, value):
        self = super(Satoshis, cls).__new__(cls)
        self.value = value
        return self

    def __repr__(self):
        return 'Satoshis(%d)'%self.value

    def __str__(self):
        return format_satoshis(self.value) + " BTC"

class Fiat(object):
    def __new__(cls, value, ccy):
        self = super(Fiat, cls).__new__(cls)
        self.ccy = ccy
        self.value = value
        return self

    def __repr__(self):
        return 'Fiat(%s)'% self.__str__()

    def __str__(self):
        if self.value.is_nan():
            return _('No Data')
        else:
            return "{:.2f}".format(self.value) + ' ' + self.ccy

class MyEncoder(json.JSONEncoder):
    def default(self, obj):
        from .transaction import Transaction
        if isinstance(obj, Transaction):
            return obj.as_dict()
        if isinstance(obj, Satoshis):
            return str(obj)
        if isinstance(obj, Fiat):
            return str(obj)
        if isinstance(obj, Decimal):
            return str(obj)
        if isinstance(obj, datetime):
            return obj.isoformat(' ')[:-3]
        return super(MyEncoder, self).default(obj)

class PrintError(object):
    '''A handy base class'''
    def diagnostic_name(self):
        return self.__class__.__name__

    def print_error(self, *msg):
        # only prints with --verbose flag
        print_error("[%s]" % self.diagnostic_name(), *msg)

    def print_stderr(self, *msg):
        print_stderr("[%s]" % self.diagnostic_name(), *msg)

    def print_msg(self, *msg):
        print_msg("[%s]" % self.diagnostic_name(), *msg)

class ThreadJob(PrintError):
    """A job that is run periodically from a thread's main loop.  run() is
    called from that thread's context.
    """

    def run(self):
        """Called periodically from the thread"""
        pass

class DebugMem(ThreadJob):
    '''A handy class for debugging GC memory leaks'''
    def __init__(self, classes, interval=30):
        self.next_time = 0
        self.classes = classes
        self.interval = interval

    def mem_stats(self):
        import gc
        self.print_error("Start memscan")
        gc.collect()
        objmap = defaultdict(list)
        for obj in gc.get_objects():
            for class_ in self.classes:
                if isinstance(obj, class_):
                    objmap[class_].append(obj)
        for class_, objs in objmap.items():
            self.print_error("%s: %d" % (class_.__name__, len(objs)))
        self.print_error("Finish memscan")

    def run(self):
        if time.time() > self.next_time:
            self.mem_stats()
            self.next_time = time.time() + self.interval

class DaemonThread(threading.Thread, PrintError):
    """ daemon thread that terminates cleanly """

    def __init__(self):
        threading.Thread.__init__(self)
        self.parent_thread = threading.currentThread()
        self.running = False
        self.running_lock = threading.Lock()
        self.job_lock = threading.Lock()
        self.jobs = []

    def add_jobs(self, jobs):
        with self.job_lock:
            self.jobs.extend(jobs)

    def run_jobs(self):
        # Don't let a throwing job disrupt the thread, future runs of
        # itself, or other jobs.  This is useful protection against
        # malformed or malicious server responses
        with self.job_lock:
            for job in self.jobs:
                try:
                    job.run()
                except Exception as e:
                    traceback.print_exc(file=sys.stderr)

    def remove_jobs(self, jobs):
        with self.job_lock:
            for job in jobs:
                self.jobs.remove(job)

    def start(self):
        with self.running_lock:
            self.running = True
        return threading.Thread.start(self)

    def is_running(self):
        with self.running_lock:
            return self.running and self.parent_thread.is_alive()

    def stop(self):
        with self.running_lock:
            self.running = False

    def on_stop(self):
        if 'ANDROID_DATA' in os.environ:
            import jnius
            jnius.detach()
            self.print_error("jnius detach")
        self.print_error("stopped")


# TODO: disable
is_verbose = True
def set_verbosity(b):
    global is_verbose
    is_verbose = b


def print_error(*args):
    if not is_verbose: return
    print_stderr(*args)

def print_stderr(*args):
    args = [str(item) for item in args]
    sys.stderr.write(" ".join(args) + "\n")
    sys.stderr.flush()

def print_msg(*args):
    # Stringify args
    args = [str(item) for item in args]
    sys.stdout.write(" ".join(args) + "\n")
    sys.stdout.flush()

def json_encode(obj):
    try:
        s = json.dumps(obj, sort_keys = True, indent = 4, cls=MyEncoder)
    except TypeError:
        s = repr(obj)
    return s

def json_decode(x):
    try:
        return json.loads(x, parse_float=Decimal)
    except:
        return x


# taken from Django Source Code
def constant_time_compare(val1, val2):
    """Return True if the two strings are equal, False otherwise."""
    return hmac.compare_digest(to_bytes(val1, 'utf8'), to_bytes(val2, 'utf8'))


# decorator that prints execution time
def profiler(func):
    def do_profile(args, kw_args):
        t0 = time.time()
        o = func(*args, **kw_args)
        t = time.time() - t0
        print_error("[profiler]", func.__qualname__, "%.4f"%t)
        return o
    return lambda *args, **kw_args: do_profile(args, kw_args)


def android_headers_file_name():
    from bitcoin import TESTNET
    s = 'blockchain_headers'
    if TESTNET:
        s += '_testnet'
    return s


def android_ext_dir():
    import jnius
    env = jnius.autoclass('android.os.Environment')
    return env.getExternalStorageDirectory().getPath()

def android_data_dir():
    import jnius
    PythonActivity = jnius.autoclass('org.kivy.android.PythonActivity')
    return PythonActivity.mActivity.getFilesDir().getPath() + '/data'

def android_headers_dir():
    d = android_ext_dir() + '/cash.z.electrum.electrum_zclassic'
    if not os.path.exists(d):
        os.mkdir(d)
    return d

def android_check_data_dir():
    """ if needed, move old directory to sandbox """
    ext_dir = android_ext_dir()
    data_dir = android_data_dir()
    old_electrum_dir = ext_dir + '/electrum-zclassic'
    if not os.path.exists(data_dir) and os.path.exists(old_electrum_dir):
        import shutil
        new_headers_path = android_headers_dir() + '/blockchain_headers'
        old_headers_path = old_electrum_dir + '/blockchain_headers'
        if not os.path.exists(new_headers_path) and os.path.exists(old_headers_path):
            print_error("Moving headers file to", new_headers_path)
            shutil.move(old_headers_path, new_headers_path)
        print_error("Moving data to", data_dir)
        shutil.move(old_electrum_dir, data_dir)
    return data_dir

def get_headers_dir(config):
    return android_headers_dir() if 'ANDROID_DATA' in os.environ else config.path


def assert_bytes(*args):
    """
    porting helper, assert args type
    """
    try:
        for x in args:
            assert isinstance(x, (bytes, bytearray))
    except:
        print('assert bytes failed', list(map(type, args)))
        raise


def assert_str(*args):
    """
    porting helper, assert args type
    """
    for x in args:
        assert isinstance(x, str)



def to_string(x, enc):
    if isinstance(x, (bytes, bytearray)):
        return x.decode(enc)
    if isinstance(x, str):
        return x
    else:
        raise TypeError("Not a string or bytes like object")

def to_bytes(something, encoding='utf8'):
    """
    cast string to bytes() like object, but for python2 support it's bytearray copy
    """
    # Dirty fix for address coming here TODOTTT: check with latest implementation
    if isinstance(something, Address):
        something = str(something)
    if isinstance(something, bytes):
        return something
    if isinstance(something, str):
        return something.encode(encoding)
    elif isinstance(something, bytearray):
        return bytes(something)
    else:
        raise TypeError("Not a string or bytes like object")


bfh = bytes.fromhex
hfu = binascii.hexlify

def bh2u(x):
    """
    str with hex representation of a bytes-like object

    >>> x = bytes((1, 2, 10))
    >>> bh2u(x)
    '01020A'

    :param x: bytes
    :rtype: str
    """
    return hfu(x).decode('ascii')


def user_dir():
    if 'ANDROID_DATA' in os.environ:
        return android_check_data_dir()
    elif os.name == 'posix':
        return os.path.join(os.environ["HOME"], ".electrum-zclassic")
    elif "APPDATA" in os.environ:
        return os.path.join(os.environ["APPDATA"], "Electrum-Zclassic")
    elif "LOCALAPPDATA" in os.environ:
        return os.path.join(os.environ["LOCALAPPDATA"], "Electrum-Zclassic")
    else:
        #raise Exception("No home directory found in environment variables.")
        return


def format_satoshis_plain(x, decimal_point = 8):
    """Display a satoshi amount scaled.  Always uses a '.' as a decimal
    point and has no thousands separator"""
    scale_factor = pow(10, decimal_point)
    return "{:.8f}".format(Decimal(x) / scale_factor).rstrip('0').rstrip('.')


def format_satoshis(x, is_diff=False, num_zeros = 0, decimal_point = 8, whitespaces=False):
    if x is None:
        return 'unknown'
    x = int(x)  # Some callers pass Decimal
    scale_factor = pow (10, decimal_point)
    integer_part = "{:d}".format(int(abs(x) / scale_factor))
    if x < 0:
        integer_part = '-' + integer_part
    elif is_diff:
        integer_part = '+' + integer_part
    dp = localeconv()['decimal_point']
    fract_part = ("{:0" + str(decimal_point) + "}").format(abs(x) % scale_factor)
    fract_part = fract_part.rstrip('0')
    if len(fract_part) < num_zeros:
        fract_part += "0" * (num_zeros - len(fract_part))
    result = integer_part + dp + fract_part
    if whitespaces:
        result += " " * (decimal_point - len(fract_part))
        result = " " * (15 - len(result)) + result
    return result

def format_satoshis_plain_nofloat(x, decimal_point = 8):
    """Display a satoshi amount scaled.  Always uses a '.' as a decimal
    point and has no thousands separator.
    Does not use any floating point representation internally, so no rounding ever occurs.
    """
    x = int(x)
    xstr = str(abs(x))

    if decimal_point > 0:
        integer_part = xstr[:-decimal_point]
        fract_part   = xstr[-decimal_point:]
        fract_part = '0'*(decimal_point - len(fract_part)) + fract_part  # add leading zeros
        fract_part = fract_part.rstrip('0')  # snip off trailing zeros
    else:
        integer_part = xstr
        fract_part = ''
    if not integer_part:
        integer_part = '0'
    if x < 0:
        integer_part = '-' + integer_part

    if fract_part:
        return integer_part + '.' + fract_part
    else:
        return integer_part

def format_satoshis_nofloat(x, num_zeros=0, decimal_point=8, precision=None, is_diff=False, whitespaces=False):
    """ Format the quantity x/10**decimal_point, for integer x.
    Does not use any floating point representation internally, so no rounding ever occurs when precision is None.
    Don't pass values other than nonnegative integers for decimal_point or num_zeros or precision.
    Undefined things will occur.
    `whitespaces` may be passed as an integer or True (the latter defaulting to 15, as in format_satoshis).
    """
    if x is None:
        return 'unknown'
    if precision is not None:
        x = round(int(x), precision - decimal_point)
    else:
        x = int(x)

    xstr = str(abs(x))

    if decimal_point > 0:
        integer_part = xstr[:-decimal_point]
        fract_part   = xstr[-decimal_point:]

        fract_part = '0'*(decimal_point - len(fract_part)) + fract_part  # add leading zeros
        fract_part = fract_part.rstrip('0')  # snip off trailing zeros
    else:
        integer_part = xstr
        fract_part = ''
    if not integer_part:
        integer_part = '0'
    if x < 0: # put the sign on
        integer_part = '-' + integer_part
    elif is_diff:
        integer_part = '+' + integer_part

    fract_part += "0" * (num_zeros - len(fract_part)) # restore desired minimum number of fractional figures

    dp = localeconv()['decimal_point']
    result = integer_part + dp + fract_part

    if whitespaces is True:
        whitespaces = 15
    if whitespaces:
        result += " " * (decimal_point - len(fract_part))
        result = " " * (whitespaces - len(result)) + result

    return result

def get_satoshis_nofloat(s, decimal_point=8):
    """ Convert a decimal string to integer.
    e.g., "5.6663" to 566630000 when decimal_point = 8
    Does not round, ever. If too many fractional digits are provided
    (even zeros) then ValueError is raised.
    """
    dec = decimal.Decimal(s)
    dtup = dec.as_tuple()

    if dtup.exponent < -decimal_point:
        raise ValueError('Too many fractional digits', s, decimal_point)

    # Create context with right amount of precision; we want to raise Inexact
    # just in case any rounding occurs (still, it should never happen!).
    C = decimal.Context(prec=len(dtup.digits), traps=[decimal.Inexact])

    res = int(C.to_integral_exact(C.scaleb(dec, decimal_point)))

    return res

def timestamp_to_datetime(timestamp):
    if timestamp is None:
        return None
    return datetime.fromtimestamp(timestamp)

def format_time(timestamp):
    date = timestamp_to_datetime(timestamp)
    return date.isoformat(' ')[:-3] if date else _("Unknown")


# Takes a timestamp and returns a string with the approximation of the age
def age(from_date, since_date = None, target_tz=None, include_seconds=False):
    if from_date is None:
        return "Unknown"

    from_date = datetime.fromtimestamp(from_date)
    if since_date is None:
        since_date = datetime.now(target_tz)

    td = time_difference(from_date - since_date, include_seconds)
    return td + " ago" if from_date < since_date else "in " + td


def time_difference(distance_in_time, include_seconds):
    #distance_in_time = since_date - from_date
    distance_in_seconds = int(round(abs(distance_in_time.days * 86400 + distance_in_time.seconds)))
    distance_in_minutes = int(round(distance_in_seconds/60))

    if distance_in_minutes <= 1:
        if include_seconds:
            for remainder in [5, 10, 20]:
                if distance_in_seconds < remainder:
                    return "less than %s seconds" % remainder
            if distance_in_seconds < 40:
                return "half a minute"
            elif distance_in_seconds < 60:
                return "less than a minute"
            else:
                return "1 minute"
        else:
            if distance_in_minutes == 0:
                return "less than a minute"
            else:
                return "1 minute"
    elif distance_in_minutes < 45:
        return "%s minutes" % distance_in_minutes
    elif distance_in_minutes < 90:
        return "about 1 hour"
    elif distance_in_minutes < 1440:
        return "about %d hours" % (round(distance_in_minutes / 60.0))
    elif distance_in_minutes < 2880:
        return "1 day"
    elif distance_in_minutes < 43220:
        return "%d days" % (round(distance_in_minutes / 1440))
    elif distance_in_minutes < 86400:
        return "about 1 month"
    elif distance_in_minutes < 525600:
        return "%d months" % (round(distance_in_minutes / 43200))
    elif distance_in_minutes < 1051200:
        return "about 1 year"
    else:
        return "over %d years" % (round(distance_in_minutes / 525600))


# Python bug (http://bugs.python.org/issue1927) causes raw_input
# to be redirected improperly between stdin/stderr on Unix systems
#TODO: py3
def raw_input(prompt=None):
    if prompt:
        sys.stdout.write(prompt)
    return builtin_raw_input()

import builtins
builtin_raw_input = builtins.input
builtins.input = raw_input


def parse_json(message):
    # TODO: check \r\n pattern
    n = message.find(b'\n')
    if n==-1:
        return None, message
    try:
        j = json.loads(message[0:n].decode('utf8'))
    except:
        j = None
    return j, message[n+1:]


class timeout(Exception):
    pass

import socket
import ssl

class SocketPipe:
    def __init__(self, socket):
        self.socket = socket
        self.message = b''
        self.set_timeout(0.1)
        self.recv_time = time.time()

    def set_timeout(self, t):
        self.socket.settimeout(t)

    def idle_time(self):
        return time.time() - self.recv_time

    def get(self):
        while True:
            response, self.message = parse_json(self.message)
            if response is not None:
                return response
            try:
                data = self.socket.recv(1024)
            except socket.timeout:
                raise timeout
            except ssl.SSLError:
                raise timeout
            except socket.error as err:
                if err.errno == 60:
                    raise timeout
                elif err.errno in [11, 35, 10035]:
                    print_error("socket errno %d (resource temporarily unavailable)"% err.errno)
                    time.sleep(0.2)
                    raise timeout
                else:
                    print_error("pipe: socket error", err)
                    data = b''
            except:
                traceback.print_exc(file=sys.stderr)
                data = b''

            if not data:  # Connection closed remotely
                return None
            self.message += data
            self.recv_time = time.time()

    def send(self, request):
        out = json.dumps(request) + '\n'
        out = out.encode('utf8')
        self._send(out)

    def send_all(self, requests):
        out = b''.join(map(lambda x: (json.dumps(x) + '\n').encode('utf8'), requests))
        self._send(out)

    def _send(self, out):
        while out:
            try:
                sent = self.socket.send(out)
                out = out[sent:]
            except ssl.SSLError as e:
                print_error("SSLError:", e)
                time.sleep(0.1)
                continue


class QueuePipe:

    def __init__(self, send_queue=None, get_queue=None):
        self.send_queue = send_queue if send_queue else queue.Queue()
        self.get_queue = get_queue if get_queue else queue.Queue()
        self.set_timeout(0.1)

    def get(self):
        try:
            return self.get_queue.get(timeout=self.timeout)
        except queue.Empty:
            raise timeout

    def get_all(self):
        responses = []
        while True:
            try:
                r = self.get_queue.get_nowait()
                responses.append(r)
            except queue.Empty:
                break
        return responses

    def set_timeout(self, t):
        self.timeout = t

    def send(self, request):
        self.send_queue.put(request)

    def send_all(self, requests):
        for request in requests:
            self.send(request)




def setup_thread_excepthook():
    """
    Workaround for `sys.excepthook` thread bug from:
    http://bugs.python.org/issue1230540

    Call once from the main thread before creating any threads.
    """

    init_original = threading.Thread.__init__

    def init(self, *args, **kwargs):

        init_original(self, *args, **kwargs)
        run_original = self.run

        def run_with_except_hook(*args2, **kwargs2):
            try:
                run_original(*args2, **kwargs2)
            except Exception:
                sys.excepthook(*sys.exc_info())

        self.run = run_with_except_hook

    threading.Thread.__init__ = init


def versiontuple(v):
    return tuple(map(int, (v.split("."))))


def import_meta(path, validater, load_meta):
    try:
        with open(path, 'r', encoding='utf-8') as f:
            d = validater(json.loads(f.read()))
        load_meta(d)
    #backwards compatibility for JSONDecodeError
    except ValueError:
        traceback.print_exc(file=sys.stderr)
        raise FileImportFailed(_("Invalid JSON code."))
    except BaseException as e:
        traceback.print_exc(file=sys.stdout)
        raise FileImportFailed(e)


def export_meta(meta, fileName):
    try:
        with open(fileName, 'w+', encoding='utf-8') as f:
            json.dump(meta, f, indent=4, sort_keys=True)
    except (IOError, os.error) as e:
        traceback.print_exc(file=sys.stderr)
        raise FileExportFailed(e)

class Weak:
    '''
    Weak reference factory. Create either a weak proxy to a bound method
    or a weakref.proxy, depending on whether this factory class's __new__ is
    invoked with a bound method or a regular function/object as its first
    argument.

    If used with an object/function reference this factory just creates a
    weakref.proxy and returns that.

        myweak = Weak(myobj)
        type(myweak) == weakref.proxy # <-- True

    The interesting usage is when this factory is used with a bound method
    instance.  In which case it returns a MethodProxy which behaves like
    a proxy to a bound method in that you can call the MethodProxy object
    directly:

        mybound = Weak(someObj.aMethod)
        mybound(arg1, arg2) # <-- invokes someObj.aMethod(arg1, arg2)

    This is unlike regular weakref.WeakMethod which is not a proxy and requires
    unsightly `foo()(args)`, or perhaps `foo() and foo()(args)` idioms.

    Also note that no exception is raised with MethodProxy instances when
    calling them on dead references.

    Instead, if the weakly bound method is no longer alive (because its object
    died), the situation is ignored as if no method were called (with an
    optional print facility provided to print debug information in such a
    situation).

    The optional `print_func` class attribute can be set in MethodProxy
    globally or for each instance specifically in order to specify a debug
    print function (which will receive exactly two arguments: the
    MethodProxy instance and an info string), so you can track when your weak
    bound method is being called after its object died (defaults to
    `print_error`).

    Note you may specify a second postional argument to this factory,
    `callback`, which is identical to the `callback` argument in the weakref
    documentation and will be called on target object finalization
    (destruction).

    This usage/idiom is intented to be used with Qt's signal/slots mechanism
    to allow for Qt bound signals to not prevent target objects from being
    garbage collected due to reference cycles -- hence the permissive,
    exception-free design.'''

    def __new__(cls, obj_or_bound_method, *args, **kwargs):
        if inspect.ismethod(obj_or_bound_method):
            # is a method -- use our custom proxy class
            return cls.MethodProxy(obj_or_bound_method, *args, **kwargs)
        else:
            # Not a method, just return a weakref.proxy
            return weakref.proxy(obj_or_bound_method, *args, **kwargs)

    ref = weakref.ref # alias for convenience so you don't have to import weakref
    Set = weakref.WeakSet # alias for convenience
    ValueDictionary = weakref.WeakValueDictionary # alias for convenience
    KeyDictionary = weakref.WeakKeyDictionary # alias for convenience
    Method = weakref.WeakMethod # alias
    finalize = weakref.finalize # alias

    _weak_refs_for_print_error = defaultdict(list)
    @staticmethod
    def finalization_print_error(obj, msg=None):
        ''' Supply a message to be printed via print_error when obj is
        finalized (Python GC'd). This is useful for debugging memory leaks. '''
        assert not isinstance(obj, type), "finaliztion_print_error can only be used on instance objects!"
        if msg is None:
            if isinstance(obj, PrintError):
                name = obj.diagnostic_name()
            else:
                name = obj.__class__.__qualname__
            msg = "[{}] finalized".format(name)
        def finalizer(x):
            wrs = Weak._weak_refs_for_print_error
            msgs = wrs.get(x, [])
            for m in msgs:
                print_error(m)
            wrs.pop(x, None)
        wr = Weak.ref(obj, finalizer)
        Weak._weak_refs_for_print_error[wr].append(msg)


    class MethodProxy(weakref.WeakMethod):
        ''' Direct-use of this class is discouraged (aside from assigning to
            its print_func attribute). Instead use of the wrapper class 'Weak'
            defined in the enclosing scope is encouraged. '''

        print_func = lambda x, this, info: print_error(this, info) # <--- set this attribute if needed, either on the class or instance level, to control debug printing behavior. None is ok here.

        def __init__(self, meth, *args, **kwargs):
            super().__init__(meth, *args, **kwargs)
            # teehee.. save some information about what to call this thing for debug print purposes
            self.qname, self.sname = meth.__qualname__, str(meth.__self__)

        def __call__(self, *args, **kwargs):
            ''' Either directly calls the method for you or prints debug info
                if the target object died '''
            meth = super().__call__() # if dead, None is returned
            if meth: # could also do callable() as the test but hopefully this is sightly faster
                return meth(*args,**kwargs)
            elif callable(self.print_func):
                self.print_func(self, "MethodProxy for '{}' called on a dead reference. Referent was: {})".format(self.qname,
                                                                                                                  self.sname))

# Export this method to the top level for convenience. People reading code
# may wonder 'Why Weak.finaliztion_print_error'?. The fact that this relies on
# weak refs is an implementation detail, really.
finalization_print_error = Weak.finalization_print_error
