"""
Validate SLP token transactions with declared version 0x65.

This uses the graph searching mechanism from slp_dagging.py
"""

import threading
import queue
from typing import Tuple
import warnings
import weakref

from .transaction import Transaction
from . import slp
from .slp import SlpMessage, SlpParsingError, SlpUnsupportedSlpTokenType, SlpInvalidOutputMessage
from .slp_dagging import TokenGraph, ValidationJob, ValidationJobManager, ValidatorGeneric
from .bitcoin import TYPE_SCRIPT
from .util import print_error
from .slp_validator_0x01 import Validator_SLP1, GraphContext

from . import slp_proxying # loading this module starts a thread.
from . import slp_graph_search # thread doesn't start until instantiation, one thread per search job, w/ shared txn cache

class GraphContext_NFT1(GraphContext):
    ''' Instance of the NFT1 DAG cache.  Uses a single per-instance
    ValidationJobManager to validate SLP tokens.  '''

    def __init__(self, name="GraphContext_NFT1"): #, is_parallel=False): # NFT1 has not been tested with is_parallel=True
        super().__init__(name=name) #, is_parallel=is_parallel)

    def _new_job_mgr(self, suffix='') -> ValidationJobManager:
        ret = ValidationJobManager(threadname=f'{self.name}/ValidationJobManager{suffix}', graph_context=self, exit_when_done=False) #self.is_parallel)
        weakref.finalize(ret, print_error, f'{ret.threadname} finalized')
        return ret

    def get_graph(self, token_id_hex, token_type) -> Tuple[TokenGraph, ValidationJobManager]:
        with self.graph_db_lock:
            try:
                return self.graph_db[token_id_hex], self._get_or_make_mgr(token_id_hex)
            except KeyError:
                pass

            if token_type == 129:
                val = Validator_SLP1(token_id_hex, enforced_token_type=129)
            elif token_type == 65:
                val = Validator_NFT1(token_id_hex, self.job_mgr)

            graph = TokenGraph(val)

            self.graph_db[token_id_hex] = graph

            return graph, self._get_or_make_mgr(token_id_hex)


    def setup_job(self, tx, reset=False) -> Tuple[TokenGraph, ValidationJobManager]:
        """ Perform setup steps before validation for a given transaction. """
        slpMsg = SlpMessage.parseSlpOutputScript(tx.outputs()[0][1])

        if slpMsg.token_type not in [65, 129]:
            raise SlpParsingError("NFT1 invalid if parent or child transaction is of SLP type " + str(slpMsg.token_type))

        if slpMsg.transaction_type == 'GENESIS':
            token_id_hex = tx.txid_fast()
        elif slpMsg.transaction_type in ('MINT', 'SEND'):
            token_id_hex = slpMsg.op_return_fields['token_id_hex']
        else:
            return None

        if reset:
            try:
                self.kill_graph(token_id_hex)
            except KeyError:
                pass

        graph, job_mgr = self.get_graph(token_id_hex, slpMsg.token_type)

        return graph, job_mgr


    def make_job(self, tx, wallet, network, nft_type, *, debug=False, reset=False, callback_done=None, **kwargs) -> ValidationJob:
        """
        Basic validation job maker for a single transaction.
        Creates job and starts it running in the background thread.
        Returns job, or None if it was not a validatable type.

        Note that the app-global 'config' object from simpe_config should be
        defined before this is called.
        """
        limit_dls, limit_depth, proxy_enable = self.get_validation_config()

        try:
            graph, job_mgr = self.setup_job(tx, reset=reset)
        except (SlpParsingError, IndexError):
            return

        # fixme -- wouldn't subsequent wallet instances clobber previous ones?!
        # graph.validator.wallet = wallet
        # graph.validator.network = network

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
            for txid in txids:
                try:
                    l.append(wallet.transactions[txid])
                except KeyError:
                    pass
            if proxy_enable:
                proxy.add_job(txids, proxy_cb)
                nonlocal num_proxy_requests
                num_proxy_requests += 1
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

        if nft_type == 'SLP65':
            job = ValidationJobNFT1Child(graph, txid, network,
                                fetch_hook=fetch_hook,
                                validitycache=None, #wallet.slpv1_validity,
                                download_limit=limit_dls,
                                depth_limit=limit_depth,
                                debug=debug,
                                was_reset=reset,
                                ref=wallet,
                                **kwargs)
        elif nft_type == 'SLP129':
            job = ValidationJob(graph, txid, network,
                                fetch_hook=fetch_hook,
                                validitycache=None, #wallet.slpv1_validity,
                                download_limit=limit_dls,
                                depth_limit=limit_depth,
                                debug=debug,
                                ref=wallet,
                                **kwargs)
        else:
            raise RuntimeError('Invalid NFT type provided.')

        job.add_callback(done_callback)
        job_mgr.add_job(job)
        return job

class ValidationJobNFT1Child(ValidationJob):
    def __init__(self, graph, txids, network,
                    fetch_hook=None,
                    validitycache=None,
                    download_limit=None, depth_limit=None,
                    debug=False, was_reset=False, ref=None):
        self.was_reset = was_reset
        self.genesis_tx = None
        self.nft_parent_tx = None
        self.nft_parent_validity = 0
        super().__init__(graph, txids, network, fetch_hook, validitycache, download_limit, depth_limit, debug, ref)

# App-wide instance. Wallets share the results of the DAG lookups.
# This instance is shared so that we don't redundantly verify tokens for each
# wallet, but rather do it app-wide.  Note that when wallet instances close
# while a verification is in progress, all extant jobs for that wallet are
# stopped -- ultimately stopping the entire DAG lookup for that token if all
# wallets verifying a token are closed.  The next time a wallet containing that
# token is opened, however, the validation continues where it left off.
shared_context_nft1 = GraphContext_NFT1()

class Validator_NFT1(ValidatorGeneric):
    prevalidation = True # indicate we want to check validation when some inputs still active.

    validity_states = {
        0: 'Unknown',
        1: 'Valid',
        2: 'Invalid: not SLP / malformed SLP',
        3: 'Invalid: insufficient valid inputs',
        4: 'Invalid: bad parent for child NFT'
        }

    def __init__(self, token_id_hex, jobmgr):
        self.token_id_hex = token_id_hex
        self.validation_jobmgr = jobmgr

    def get_info(self,tx):
        """
        Enforce internal consensus rules (check all rules that don't involve
        information from inputs).

        Prune if mismatched token_id_hex from this validator or SLP version other than 65.
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
        if slpMsg.token_type not in [65]:
            return ('prune', 0)

        if slpMsg.transaction_type == 'SEND':
            token_id_hex = slpMsg.op_return_fields['token_id_hex']

            # need to examine all inputs
            vin_mask = (True,)*len(tx.inputs())

            # myinfo is the output sum
            # Note: according to consensus rules, we compute sum before truncating extra outputs.
        #    print("DEBUG SLP:getinfo %.10s outputs: %r"%(tx.txid(), slpMsg.op_return_fields['token_output']))
            myinfo = sum(slpMsg.op_return_fields['token_output'])

            # Cannot have more than 1 SLP output w/ child NFT (vout 0 op_return msg & vout 1 qty)
            if len(slpMsg.op_return_fields['token_output']) != 2:
                return ('prune', 2)

            # Cannot have quantity other than 1 as output at vout 1
            if slpMsg.op_return_fields['token_output'][1] != 1:
                return ('prune', 2)

            # outputs straight from the token amounts
            outputs = slpMsg.op_return_fields['token_output']
        elif slpMsg.transaction_type == 'GENESIS':
            token_id_hex = tx.txid_fast()

            vin_mask = (False,)*len(tx.inputs()) # don't need to examine any inputs.

            myinfo = 'GENESIS'

            mintvout = slpMsg.op_return_fields['mint_baton_vout']
            if mintvout is not None:
                return ('prune', 2)
            decimals = slpMsg.op_return_fields['decimals']
            if decimals != 0:
                return ('prune', 2)
            outputs = [None,None]
            outputs[1] = slpMsg.op_return_fields['initial_token_mint_quantity']
            if outputs[1] > 1:
                return ('prune', 2)
        elif slpMsg.transaction_type == 'MINT':
            return ('prune', 2)
        elif slpMsg.transaction_type == 'COMMIT':
            return ('prune', 0)

        if token_id_hex != self.token_id_hex:
            return ('prune', 0)  # mismatched token_id_hex

        # truncate / expand outputs list to match tx outputs length
        outputs = tuple(outputs[:len(txouts)])
        outputs = outputs + (None,)*(len(txouts) - len(outputs))

        return vin_mask, myinfo, outputs


    def check_needed(self, myinfo, out_n):
        if myinfo == 'GENESIS':
            # genesis shouldn't have any parents, so this should not happen.
            raise RuntimeError('Unexpected', out_n)

        # TRAN txes are only interested in integer, non-zero input contributions.
        if out_n is None or out_n == 'MINT':
            return False
        else:
            return (out_n > 0)

    def download_nft_genesis(self, nft_child_job, done_callback):
        def dl_cb(resp):
            if resp.get('error'):
                raise Exception(resp['error'].get('message'))
            raw = resp.get('result')
            tx = Transaction(raw)
            assert tx.txid_fast() == self.token_id_hex
            txid = self.token_id_hex
            wallet = nft_child_job.ref()
            with wallet.lock:
                if not wallet.transactions.get(txid, None):
                    wallet.transactions[txid] = tx
                if not wallet.tx_tokinfo.get(txid, None):
                    from .slp import SlpMessage
                    slpMsg = SlpMessage.parseSlpOutputScript(tx.outputs()[0][1])
                    tti = { 'type':'SLP%d'%(slpMsg.token_type,),
                        'transaction_type':slpMsg.transaction_type,
                        'token_id': txid,
                        'validity': 0,
                    }
                    wallet.tx_tokinfo[txid] = tti
                wallet.save_transactions()
            nft_child_job.genesis_tx = tx
            if done_callback:
                done_callback()
        requests = [('blockchain.transaction.get', [self.token_id_hex]), ]
        nft_child_job.network.send(requests, dl_cb)

    def download_nft_parent_tx(self, nft_child_job, done_callback):
        def dl_cb(resp):
            if resp.get('error'):
                raise Exception(resp['error'].get('message'))
            raw = resp.get('result')
            tx = Transaction(raw)
            txid = tx.txid_fast()
            wallet = nft_child_job.ref()
            with wallet.lock:
                if not wallet.transactions.get(txid, None):
                    wallet.transactions[txid] = tx
                if not wallet.tx_tokinfo.get(txid, None):
                    slpMsg = SlpMessage.parseSlpOutputScript(tx.outputs()[0][1])
                    tti = { 'type':'SLP%d'%(slpMsg.token_type,),
                        'transaction_type':slpMsg.transaction_type,
                        'validity': 0,
                    }
                    if slpMsg.transaction_type == 'GENESIS':
                        tti['token_id'] = txid
                    else:
                        tti['token_id'] = slpMsg.op_return_fields['token_id_hex']
                    wallet.tx_tokinfo[txid] = tti
                wallet.save_transactions()
            nft_child_job.nft_parent_tx = tx
            if done_callback:
                done_callback()
        nft_parent_txid = nft_child_job.genesis_tx.inputs()[0]['prevout_hash']
        requests = [('blockchain.transaction.get', [nft_parent_txid]), ]
        nft_child_job.network.send(requests, dl_cb)

    def start_NFT_parent_job(self, nft_child_job, done_callback):
        wallet = nft_child_job.ref()
        network = nft_child_job.network
        def callback(job):
            (txid,node), = job.nodes.items()
            val = node.validity
            group_id = wallet.tx_tokinfo[nft_child_job.nft_parent_tx.txid_fast()]['token_id']
            if not wallet.token_types.get(group_id, None):
                name = wallet.token_types[nft_child_job.genesis_tx.txid_fast()]['name'] + '-parent'
                #decimals = SlpMessage.parseSlpOutputScript(wallet.transactions[group_id].outputs()[0][1]).op_return_fields['decimals']
                parent_entry = dict({'class':'SLP129','name':name,'decimals':0}) # TODO: handle case where decimals is not 0
                wallet.add_token_type(group_id, parent_entry)
            with wallet.lock:
                wallet.token_types[nft_child_job.genesis_tx.txid_fast()]['group_id'] = group_id
                wallet.tx_tokinfo[nft_child_job.nft_parent_tx.txid_fast()]['validity'] = val
                wallet.tx_tokinfo[nft_child_job.genesis_tx.txid_fast()]['validity'] = val
                wallet.save_transactions()
            ui_cb = wallet.ui_emit_validity_updated
            if ui_cb:
                ui_cb(txid, val)
                ui_cb(nft_child_job.genesis_tx.txid_fast(), val)
            if done_callback:
                done_callback(val)

        tx = nft_child_job.nft_parent_tx
        job = self.validation_jobmgr.graph_context and self.validation_jobmgr.graph_context.make_job(tx, wallet, network, nft_type='SLP129', debug=nft_child_job.debug, reset=nft_child_job.was_reset)
        if job is not None:
            job.add_callback(callback)
        elif self.validation_jobmgr.graph_context is None:
            # FIXME?
            warnings.warn("Graph Context is None, JobManager was killed")
        else:
            with wallet.lock:
                wallet.tx_tokinfo[nft_child_job.genesis_tx.txid_fast()]['validity'] = 4
                wallet.save_transactions()
            ui_cb = wallet.ui_emit_validity_updated
            if ui_cb:
                ui_cb(nft_child_job.genesis_tx.txid_fast(), 4)
            if done_callback:
                done_callback(4)

    def validate_NFT_parent(self, nft_child_job, myinfo):
        def restart_nft_job(val):
            nft_child_job.nft_parent_validity = val
            self.validation_jobmgr.unpause_job(nft_child_job)
            #self.nft_child_job = None # release reference

        def start_nft_parent_validation():
            self.start_NFT_parent_job(nft_child_job, done_callback=restart_nft_job)

        def start_dl_nft_parent():
            self.download_nft_parent_tx(nft_child_job, done_callback=start_nft_parent_validation)

        self.validation_jobmgr.pause_job(nft_child_job)
        self.download_nft_genesis(nft_child_job, start_dl_nft_parent)

    def validate(self, myinfo, inputs_info):
        nft_child_job = self.validation_jobmgr.job_current

        # NFT requires parent validation pre-valid phase
        if nft_child_job.nft_parent_tx is None:
            self.validate_NFT_parent(nft_child_job, myinfo)
            return None

        if myinfo == 'GENESIS':
            if len(inputs_info) != 0:
                raise RuntimeError('Unexpected', inputs_info)
            if nft_child_job.nft_parent_validity == 1:
                return (True, 1)
            elif nft_child_job.nft_parent_validity > 1:
                return (False, nft_child_job.nft_parent_validity)
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
