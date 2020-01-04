"""

Background search and batch download for graph transactions.

This is used by slp_validator_0x01.py.

To generate proto files use the following command:
python3 -m grpc_tools.protoc --proto_path=lib/ --python_out=lib/ --grpc_python_out=lib/ lib/slp_graphsearchrpc.proto

"""

import sys
import time
import threading
import queue
import traceback
import weakref
import collections
import json
import base64
import requests
import codecs
from .transaction import Transaction
from .caches import ExpiringCache

class SlpdbErrorNoSearchData(Exception):
    pass

class GraphSearchJob:
    def __init__(self, txid, valjob_ref):
        self.root_txid = txid
        self.valjob = valjob_ref

        # metadata fetched from back end
        self.depth_map = None
        self.total_depth = None
        self.txn_count_total = None

        # job status info
        self.search_started = False
        self.search_success = None
        self.job_complete = False
        self.exit_msg = None
        self.depth_completed = 0
        self.depth_current_query = None
        self.txn_count_progress = 0
        self.last_search_url = '(url empty)'

        # ctl
        self.waiting_to_cancel = False
        self.cancel_callback = None
        self.fetch_retries = 0

        # host for graph search
        self.host = self.valjob.network.slp_gs_host

    def sched_cancel(self, callback=None, reason='job canceled'):
        self.exit_msg = reason
        if self.job_complete:
            return
        if not self.waiting_to_cancel:
            self.waiting_to_cancel = True
            self.cancel_callback = callback
            return

    def _cancel(self):
        self.job_complete = True
        self.search_success = False
        if self.cancel_callback:
            self.cancel_callback(self)

    def set_success(self):
        self.search_success = True
        self.job_complete = True

    def set_failed(self, reason=None):
        self.search_started = True
        self.search_success = False
        self.job_complete = True
        self.exit_msg = reason

class SlpGraphSearchManager:
    """
    A single thread that processes graph search requests sequentially.
    """
    def __init__(self, threadname="GraphSearch"):
        # holds the job history and status
        self.search_jobs = dict()
        self.lock = threading.Lock()

        # Create a single use queue on a new thread
        self.search_queue = queue.Queue()  # TODO: make this a PriorityQueue based on dag size

        self.threadname = threadname
        self.search_thread = threading.Thread(target=self.mainloop, name=self.threadname+'/search', daemon=True)
        self.search_thread.start()

    def new_search(self, valjob_ref):
        """
        Starts a new thread to fetch GS metadata for a job.
        Depending on the metadata results the job may end up being added to the GS queue.

        Returns weakref of the new GS job object if new job is created.
        """
        txid = valjob_ref.root_txid
        with self.lock:
            if txid not in self.search_jobs.keys():
                job = GraphSearchJob(txid, valjob_ref)
                self.search_jobs[txid] = job
                self.search_queue.put(job)
            else:
                job = self.search_jobs[txid]
            return job
        return None

    def restart_search(self, job):
        def callback(job):
            with self.lock:
                self.search_jobs.pop(job.root_txid, None)
            self.new_search(job.valjob)
            job = None
        if not job.job_complete:
            job.sched_cancel(callback, reason='job restarted')
        else:
            callback(job)

    def mainloop(self,):
        try:
            while True:
                job = self.search_queue.get(block=True)
                job.search_started = True
                if not job.valjob.running and not job.valjob.has_never_run:
                    job.set_failed('validation finished')
                    continue
                try:
                    # search_query is a recursive call, most time will be spent here
                    self.search_query(job)
                except Exception as e:
                    print("error in graph search query", e, file=sys.stderr)
                    job.set_failed(str(e))
        finally:
            print("[SLP Graph Search] Error: mainloop exited.", file=sys.stderr)

    def search_query(self, job):
        if job.waiting_to_cancel:
            job._cancel()
            return
        if not job.valjob.running and not job.valjob.has_never_run:
            job.set_failed('validation finished')
            return
        print('Requesting txid from gs++: ' + job.root_txid)
        txid = codecs.encode(codecs.decode(job.root_txid,'hex')[::-1], 'hex').decode()
        print('Requesting txid from gs++ (reversed): ' + txid)

        query_json = { "txid": txid } # TODO: handle 'validity_cache' exclusion from graph search (NOTE: this will impact total dl count)
        reqresult = requests.post(job.valjob.network.slp_gs_host + "/v1/graphsearch/graphsearch", json=query_json, timeout=60)
        try:
            txns = json.loads(reqresult.content.decode('utf-8'))['txdata']
        except:
            m = json.loads(reqresult.content)
            if m["error"]:
                raise Exception(m["error"])
            raise Exception(m)
        for txn in txns:
            job.txn_count_progress += 1
            tx = Transaction(base64.b64decode(txn).hex())
            SlpGraphSearchManager.tx_cache_put(tx)
        job.set_success()
        print("[SLP Graph Search] job success.")

    # This cache stores foreign (non-wallet) tx's we fetched from the network
    # for the purposes of the "fetch_input_data" mechanism. Its max size has
    # been thoughtfully calibrated to provide a decent tradeoff between
    # memory consumption and UX.
    #
    # In even aggressive/pathological cases this cache won't ever exceed
    # 100MB even when full. [see ExpiringCache.size_bytes() to test it].
    # This is acceptable considering this is Python + Qt and it eats memory
    # anyway.. and also this is 2019 ;). Note that all tx's in this cache
    # are in the non-deserialized state (hex encoded bytes only) as a memory
    # savings optimization.  Please maintain that invariant if you modify this
    # code, otherwise the cache may grow to 10x memory consumption if you
    # put deserialized tx's in here.
    _fetched_tx_cache = ExpiringCache(maxlen=100000, name="GraphSearchTxnFetchCache")

    @classmethod
    def tx_cache_get(cls, txid: str) -> object:
        ''' Attempts to retrieve txid from the tx cache that this class
        keeps in-memory.  Returns None on failure. The returned tx is
        not deserialized, and is a copy of the one in the cache. '''
        tx = cls._fetched_tx_cache.get(txid)
        if tx is not None and tx.raw:
            # make sure to return a copy of the transaction from the cache
            # so that if caller does .deserialize(), *his* instance will
            # use up 10x memory consumption, and not the cached instance which
            # should just be an undeserialized raw tx.
            return Transaction(tx.raw)
        return None

    @classmethod
    def tx_cache_put(cls, tx: bytes, txid: str = None):
        ''' Puts a non-deserialized copy of tx into the tx_cache. '''
        txid = txid or Transaction._txid(tx.raw)  # optionally, caller can pass-in txid to save CPU time for hashing
        cls._fetched_tx_cache.put(txid, tx)
