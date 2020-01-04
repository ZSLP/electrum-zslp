"""
Validate SLP token transactions with declared version 0x01.

This uses the graph searching mechanism from slp_dagging.py
"""

import threading
import queue
from typing import Tuple, List
import weakref

from .transaction import Transaction
from .simple_config import get_config
from . import slp
from .slp import SlpMessage, SlpParsingError, SlpUnsupportedSlpTokenType, SlpInvalidOutputMessage
from .slp_dagging import TokenGraph, ValidationJob, ValidationJobManager, ValidatorGeneric
from .bitcoin import TYPE_SCRIPT
from .util import print_error, PrintError

from . import slp_proxying # loading this module starts a thread.
from .slp_graph_search import SlpGraphSearchManager # thread is started upon instantiation

class GraphContext(PrintError):
    ''' Instance of the DAG cache. Uses a single per-instance
    ValidationJobManager to validate SLP tokens if is_parallel=False.

    If is_parallel=True, will create 1 job manager (thread) per tokenid it is
    validating. '''

    def __init__(self, name='GraphContext', is_parallel=False, use_graph_search=False):
        # Global db for shared graphs (each token_id_hex has its own graph).
        self.graph_db_lock = threading.Lock()
        self.graph_db = dict()   # token_id_hex -> TokenGraph
        self.is_parallel = is_parallel
        self.job_mgrs = weakref.WeakValueDictionary()   # token_id_hex -> ValidationJobManager (only used if is_parallel, otherwise self.job_mgr is used)
        self.name = name
        self.graph_search_mgr = SlpGraphSearchManager() if use_graph_search else None
        self._setup_job_mgr()

    def diagnostic_name(self):
        return self.name

    def _setup_job_mgr(self):
        if self.is_parallel:
            self.job_mgr = None
        else:
            self.job_mgr = self._new_job_mgr()

    def _new_job_mgr(self, suffix='') -> ValidationJobManager:
        ret = ValidationJobManager(threadname=f'{self.name}/ValidationJobManager{suffix}', exit_when_done=self.is_parallel)
        weakref.finalize(ret, print_error, f'[{ret.threadname}] finalized')  # track object lifecycle
        return ret

    def _get_or_make_mgr(self, token_id_hex: str) -> ValidationJobManager:
        ''' Helper: This must be called with self.graph_db_lock held.
        Creates a new job manager for token_id_hex if is_parallel=True and one
        doesn't already exist, and returns it.

        Returns self.job_mgr if is_parallel=False. '''
        job_mgr = self.job_mgr or self.job_mgrs.get(token_id_hex) or self._new_job_mgr(token_id_hex[:4])
        if job_mgr is not self.job_mgr:
            # was an is_parallel setup
            assert not self.job_mgr and self.is_parallel and job_mgr
            self.job_mgrs[token_id_hex] = job_mgr
        return job_mgr

    def get_graph(self, token_id_hex) -> Tuple[TokenGraph, ValidationJobManager]:
        ''' Returns an existing or new graph for a particular token.
        A new job manager is created for that token if self.is_parallel=True,
        otherwise the shared job manager is used.'''
        with self.graph_db_lock:
            try:
                return self.graph_db[token_id_hex], self._get_or_make_mgr(token_id_hex)
            except KeyError:
                pass

            val = Validator_SLP1(token_id_hex)

            graph = TokenGraph(val)

            self.graph_db[token_id_hex] = graph

            return graph, self._get_or_make_mgr(token_id_hex)

    def kill_graph(self, token_id_hex):
        ''' Reset a graph. This will stop all the jobs for that token_id_hex. '''
        with self.graph_db_lock:
            try:
                graph = self.graph_db.pop(token_id_hex)
                job_mgr = self.job_mgrs.pop(token_id_hex, None)
            except KeyError:
                return
        if job_mgr:
            assert job_mgr is not self.job_mgr
            job_mgr.kill()
        elif self.job_mgr:
            # todo: see if we can put this in the above 'with' block (while
            # holding locks). I was hesitant to do so for fear of deadlocks.
            self.job_mgr.stop_all_with_txid(token_id_hex)

        graph.reset()

    def kill(self):
        ''' Kills all jobs and resets this instance to the state it had
        when freshly constructed '''
        with self.graph_db_lock:
            for token_id_hex, graph in self.graph_db.items():
                graph.reset()
                job_mgr = self.job_mgrs.pop(token_id_hex, None)
                if job_mgr: job_mgr.kill()
            self.graph_db.clear()
            self.job_mgrs.clear()
        if self.job_mgr:
            self.job_mgr.kill()
            self._setup_job_mgr()  # re-create a new, clean instance, if needed

    def setup_job(self, tx, reset=False) -> Tuple[TokenGraph, ValidationJobManager]:
        """ Perform setup steps before validation for a given transaction. """
        slpMsg = SlpMessage.parseSlpOutputScript(tx.outputs()[0][1])

        if slpMsg.transaction_type == 'GENESIS':
            token_id_hex = tx.txid_fast()
        elif slpMsg.transaction_type in ('MINT', 'SEND'):
            token_id_hex = slpMsg.op_return_fields['token_id_hex']
        else:
            return None

        if reset and not self.is_parallel:
            try:
                self.kill_graph(token_id_hex)
            except KeyError:
                pass

        graph, job_mgr = self.get_graph(token_id_hex)

        return graph, job_mgr

    @staticmethod
    def get_validation_config():
        config = get_config()
        try:
            limit_dls   = config.get('slp_validator_download_limit', None)
            limit_depth = config.get('slp_validator_depth_limit', None)
            proxy_enable = config.get('slp_validator_proxy_enabled', False)
        except NameError: # in daemon mode (no GUI) 'config' is not defined
            limit_dls = None
            limit_depth = None
            proxy_enable = False

        return limit_dls, limit_depth, proxy_enable

    @staticmethod
    def get_gs_config():
        config = get_config()
        try:
            gs_enable = config.get('slp_validator_graphsearch_enabled', False)
            gs_host = config.get('slpdb_host', None)
        except NameError: # in daemon mode (no GUI) 'config' is not defined
            gs_enable = False
            gs_host = None

        return gs_enable, gs_host


    def make_job(self, tx, wallet, network, *, debug=False, reset=False, callback_done=None, **kwargs) -> ValidationJob:
        """
        Basic validation job maker for a single transaction.
        Creates job and starts it running in the background thread.
        Returns job, or None if it was not a validatable type.

        Note that the app-global 'config' object from simpe_config should be
        defined before this is called.
        """
        limit_dls, limit_depth, proxy_enable = self.get_validation_config()
        gs_enable, gs_host = self.get_gs_config()
        network.slpdb_host = gs_host

        try:
            graph, job_mgr = self.setup_job(tx, reset=reset)
        except (SlpParsingError, IndexError):
            return

        txid = tx.txid_fast()

        num_proxy_requests = 0
        proxyqueue = queue.Queue()

        def proxy_cb(txids, results):
            newres = {}
            # convert from 'true/false' to (True,1) or (False,3)
            for t,v in results.items():
                if v:
                    newres[t] = (True, 1)
                else:
                    newres[t] = (True, 3)
            proxyqueue.put(newres)
            
        def fetch_hook(txids, val_job):
            l = []
            nonlocal gs_enable, gs_host
            if gs_enable and gs_host and self.graph_search_mgr:
                if val_job.root_txid not in self.graph_search_mgr.search_jobs.keys():
                    search_job = self.graph_search_mgr.new_search(val_job)
                    val_job.graph_search_job = search_job if search_job else None
            else:
                gs_enable, gs_host = self.get_gs_config()
                network.slpdb_host = gs_host

            for txid in txids:
                txn = SlpGraphSearchManager.tx_cache_get(txid)
                if txn:
                    l.append(txn)
                else:
                    try:
                        l.append(wallet.transactions[txid])
                    except KeyError:
                        pass
            return l

        def done_callback(job):
            # wait for proxy stuff to roll in
            results = {}
            try:
                for _ in range(num_proxy_requests):
                    r = proxyqueue.get(timeout=5)
                    results.update(r)
            except queue.Empty:
                pass

            if proxy_enable:
                graph.finalize_from_proxy(results)

            # Do consistency check here
            # XXXXXXX

            # Save validity
            for t,n in job.nodes.items():
                val = n.validity
                if val != 0:
                    wallet.slpv1_validity[t] = val


        job = ValidationJob(graph, txid, network,
                            fetch_hook=fetch_hook,
                            validitycache=wallet.slpv1_validity,
                            download_limit=limit_dls,
                            depth_limit=limit_depth,
                            debug=debug, ref=wallet,
                            **kwargs)
        job.add_callback(done_callback)

        job_mgr.add_job(job)

        return job

    def stop_all_for_wallet(self, wallet, timeout=None) -> List[ValidationJob]:
        ''' Stops all extant jobs for a particular wallet. This method is
        intended to be called on wallet close so that all the work that
        particular wallet enqueued can get cleaned up. This method properly
        supports both is_parallel and single mode.  Will return all the jobs
        that matched as a list or the empty list if no jobs matched.

        Optional arg timeout, if not None and positive, will make this function
        wait for the jobs to complete for up to timeout seconds per job.'''
        jobs = []
        if self.job_mgr:
            # single job manager mode
            jobs = self.job_mgr.stop_all_for(wallet)
        else:
            # multi job-manager mode, iterate over all extant job managers
            with self.graph_db_lock:
                for txid, job_mgr in dict(self.job_mgrs).items():
                    jobs += job_mgr.stop_all_for(wallet)
        if timeout is not None and timeout > 0:
            for job in jobs:
                if job.running:
                    job.exited.wait(timeout=timeout) or self.print_error(f"Warning: Job {job} wait timed out (timeout={timeout})")
        return jobs


# App-wide instance. Wallets share the results of the DAG lookups.
# This instance is shared so that we don't redundantly verify tokens for each
# wallet, but rather do it app-wide.  Note that when wallet instances close
# while a verification is in progress, all extant jobs for that wallet are
# stopped -- ultimately stopping the entire DAG lookup for that token if all
# wallets verifying a token are closed.  The next time a wallet containing that
# token is opened, however, the validation continues where it left off.
shared_context = GraphContext(is_parallel=True, use_graph_search=True)  # <-- Set is_parallel=True if you want 1 thread per token (tokens validate in parallel). Otherwise there is 1 validator thread app-wide and tokens validate in series.

class Validator_SLP1(ValidatorGeneric):
    prevalidation = True # indicate we want to check validation when some inputs still active.

    validity_states = {
        0: 'Unknown',
        1: 'Valid',
        2: 'Invalid: not SLP / malformed SLP',
        3: 'Invalid: insufficient valid inputs',
        4: 'Invalid: token type different than required'
        }

    def __init__(self, token_id_hex, *, enforced_token_type=1):
        self.token_id_hex = token_id_hex
        self.token_type = enforced_token_type

    def get_info(self, tx, *, diff_testing_mode=False):
        """
        Enforce internal consensus rules (check all rules that don't involve
        information from inputs).

        Prune if mismatched token_id_hex from this validator or SLP version other than 1.

        diff_testing_mode, allows None for token_type and token_id_hex for fuzzer testing
        """
        txouts = tx.outputs()
        if len(txouts) < 1:
            return ('prune', 2) # not SLP -- no outputs!

        # We take for granted that parseSlpOutputScript here will catch all
        # consensus-invalid op_return messages. In this procedure we check the
        # remaining internal rules, having to do with the overall transaction.
        try:
            slpMsg = SlpMessage.parseSlpOutputScript(txouts[0][1])
        except SlpUnsupportedSlpTokenType as e:
            # for unknown types: pruning as unknown has similar effect as pruning
            # invalid except it tells the validity cacher to not remember this
            # tx as 'bad'
            return ('prune', 0)
        except SlpInvalidOutputMessage as e:
            return ('prune', 2)

        # Parse the SLP
        if slpMsg.token_type not in [1,129]:
            return ('prune', 0)

        # Check that the correct token_type is enforced (type 0x01 or 0x81)
        if diff_testing_mode and self.token_type is not None and self.token_type != slpMsg.token_type:
            return ('prune', 4)
        elif not diff_testing_mode and self.token_type != slpMsg.token_type:
            return ('prune', 4)

        if slpMsg.transaction_type == 'SEND':
            token_id_hex = slpMsg.op_return_fields['token_id_hex']

            # need to examine all inputs
            vin_mask = (True,)*len(tx.inputs())

            # myinfo is the output sum
            # Note: according to consensus rules, we compute sum before truncating extra outputs.
#            print("DEBUG SLP:getinfo %.10s outputs: %r"%(tx.txid(), slpMsg.op_return_fields['token_output']))
            myinfo = sum(slpMsg.op_return_fields['token_output'])

            # outputs straight from the token amounts
            outputs = slpMsg.op_return_fields['token_output']
        elif slpMsg.transaction_type == 'GENESIS':
            token_id_hex = tx.txid_fast()

            vin_mask = (False,)*len(tx.inputs()) # don't need to examine any inputs.

            myinfo = 'GENESIS'

            # place 'MINT' as baton signifier on the designated output
            mintvout = slpMsg.op_return_fields['mint_baton_vout']
            if mintvout is None:
                outputs = [None,None]
            else:
                outputs = [None]*(mintvout) + ['MINT']
            outputs[1] = slpMsg.op_return_fields['initial_token_mint_quantity']
        elif slpMsg.transaction_type == 'MINT':
            token_id_hex = slpMsg.op_return_fields['token_id_hex']

            vin_mask = (True,)*len(tx.inputs()) # need to examine all vins, even for baton.

            myinfo = 'MINT'

            # place 'MINT' as baton signifier on the designated output
            mintvout = slpMsg.op_return_fields['mint_baton_vout']
            if mintvout is None:
                outputs = [None,None]
            else:
                outputs = [None]*(mintvout) + ['MINT']
            outputs[1] = slpMsg.op_return_fields['additional_token_quantity']
        elif slpMsg.transaction_type == 'COMMIT':
            return ('prune', 0)

        if diff_testing_mode and self.token_id_hex is not None and token_id_hex != self.token_id_hex:
            return ('prune', 0)  # mismatched token_id_hex
        elif not diff_testing_mode and token_id_hex != self.token_id_hex:
            return ('prune', 0)

        # truncate / expand outputs list to match tx outputs length
        outputs = tuple(outputs[:len(txouts)])
        outputs = outputs + (None,)*(len(txouts) - len(outputs))

        return vin_mask, myinfo, outputs


    def check_needed(self, myinfo, out_n):
        if myinfo == 'MINT':
            # mints are only interested in the baton input
            return (out_n == 'MINT')
        if myinfo == 'GENESIS':
            # genesis shouldn't have any parents, so this should not happen.
            raise RuntimeError('Unexpected', out_n)

        # TRAN txes are only interested in integer, non-zero input contributions.
        if out_n is None or out_n == 'MINT':
            return False
        else:
            return (out_n > 0)


    def validate(self, myinfo, inputs_info):
        if myinfo == 'GENESIS':
            if len(inputs_info) != 0:
                raise RuntimeError('Unexpected', inputs_info)
            return (True, 1)   # genesis is always valid.
        elif myinfo == 'MINT':
            if not all(inp[2] == 'MINT' for inp in inputs_info):
                raise RuntimeError('non-MINT inputs should have been pruned!', inputs_info)
            if len(inputs_info) == 0:
                return (False, 3) # no baton? invalid.
            if any(inp[1] == 1 for inp in inputs_info):
                # Why we use 'any' here:
                # multiple 'valid' baton inputs are possible with double spending.
                # technically 'valid' though miners will never confirm.
                return (True, 1)
            if all(inp[1] in [2,3,4] for inp in inputs_info):
                return (False, 3)
            return None
        else:
            # TRAN --- myinfo is an integer sum(outs)

            # Check whether from the unknown + valid inputs there could be enough to satisfy outputs.
            insum_all = sum(inp[2] for inp in inputs_info if inp[1] <= 1)
            if insum_all < myinfo:
                return (False, 3)

            # Check whether the known valid inputs provide enough tokens to satisfy outputs:
            insum_valid = sum(inp[2] for inp in inputs_info if inp[1] == 1)
            if insum_valid >= myinfo:
                return (True, 1)
            return None
