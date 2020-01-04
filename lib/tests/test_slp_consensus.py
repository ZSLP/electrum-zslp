import unittest
from pprint import pprint
from queue import Queue, Empty

from time import sleep
from lib.slp_validator_0x01_nft1 import ValidationJobNFT1Child

from lib.address import ScriptOutput

from lib.transaction import Transaction

import json

from lib import slp
from lib import slp_validator_0x01
from lib import slp_validator_0x01_nft1
from lib.storage import WalletStorage
from lib.wallet import Slp_ImportedAddressWallet

import requests
import os

scripttests_local = os.path.abspath('../slp-unit-test-data/script_tests.json')
scripttests_url = 'https://raw.githubusercontent.com/simpleledger/slp-unit-test-data/master/script_tests.json' #https://simpleledger.cash/slp-unit-test-data/script_tests.json'

txintests_local = os.path.abspath('../slp-unit-test-data/tx_input_tests.json')
txintests_url = 'https://raw.githubusercontent.com/simpleledger/slp-unit-test-data/master/tx_input_tests.json' #'https://simpleledger.cash/slp-unit-test-data/tx_input_tests.json'

errorcodes = {
    # no-error maps to None

    # various script format errors
    ('Bad OP_RETURN', 'Script error'): 1,
    # disallowed opcodes
    ('Bad OP_RETURN', 'Non-push opcode'): 2,
    ('Bad OP_RETURN', 'OP_1NEGATE to OP_16 not allowed'): 2,
    ('Bad OP_RETURN', 'OP_0 not allowed'): 2,

    # not OP_RETURN script / not SLP
    # (note in some implementations, parsers should never be given such non-SLP scripts in the first place. In such implementations, error code 3 tests may be skipped.)
    ('Bad OP_RETURN', 'No OP_RETURN'): 3,
    ('Empty OP_RETURN', ): 3,
    ('Not SLP',): 3,

    # 10- field bytesize is wrong
    ('Field has wrong length', ): 10,
    ('Ticker too long', ): 10,
    ('Token document hash is incorrect length',): 10,
    ('token_id is wrong length',): 10,

    # 11- improper value
    ('Too many decimals',): 11,
    ('Bad transaction type',): 11,
    ('Mint baton cannot be on vout=0 or 1',): 11,

    # 12- missing field / too few fields
    ('Missing output amounts', ): 12,
    ('Missing token_type', ): 12,
    ('Missing SLP command', ): 12,
    ('GENESIS with incorrect number of parameters', ): 12,
    ('SEND with too few parameters', ): 12,
    ('MINT with incorrect number of parameters', ): 12,

    # specific
    ('More than 19 output amounts',): 21,

    # specific - NFT1 GENESIS 
    ('Cannot have a minting baton in a NFT_CHILD token.', ): 22,
    ('NFT1 child token must have divisibility set to 0 decimal places.', ): 22,
    ('NFT1 child token must have GENESIS quantity of 1.', ): 22,

    #SlpUnsupportedSlpTokenType : 255 below
}

# We need a mock network because of the NFT1 validator
class MockNetwork:
    def __init__(self, txes):
        self.txes = txes
    def send(self, req, dl_cb):
        try:
            result = {'result':self.txes[req[0][1][0]].raw}
        except KeyError:
            result = {'error':{'message':'unknown txid ' + req[0][1][0] + ' ' + str(self.txes)}}
        sleep(0.001)
        dl_cb(result)

class SLPConsensusTests(unittest.TestCase):
    def test_opreturns(self):
        try:
            with open(scripttests_local) as f:
                testlist = json.load(f)
            print("Got script tests from %s; will not download."%(scripttests_local,))
        except IOError:
            print("Couldn't get script tests from %s; downloading from %s..."%(scripttests_local,scripttests_url))
            testlist = requests.get(scripttests_url).json()

        print("Starting %d tests on SLP's OP_RETURN parser"%len(testlist))
        for d in testlist:
            description = d['msg']
            scripthex = d['script']
            code = d['code']
            if scripthex is None:
                continue
            if hasattr(code, '__iter__'):
                expected_codes = tuple(code)
            else:
                expected_codes = (code, )

            with self.subTest(description=description, script=scripthex):
                sco = ScriptOutput(bytes.fromhex(scripthex))
                try:
                    msg = slp.SlpMessage.parseSlpOutputScript(sco)
                except Exception as e:
                    if isinstance(e, slp.SlpInvalidOutputMessage):
                        emsg = e.args
                        if errorcodes[emsg] not in expected_codes:
                            raise AssertionError("Invalidity reason %r (code: %d) not in expected reasons %r"%(emsg, errorcodes[emsg], expected_codes))
                    elif isinstance(e, slp.SlpUnsupportedSlpTokenType):
                        if 255 not in expected_codes:
                            raise AssertionError("SlpUnsupportedSlpTokenType exception raised (code 255) but not in expected reasons (%r)"%(expected_codes,))
                    else:
                        raise
                else:
                    # no exception
                    if None not in expected_codes:
                        raise AssertionError("Script was found valid but should have been invalid, for a reason code in %r."%(expected_codes,))

        pass


    def test_inputs(self):
        try:
            with open(txintests_local) as f:
                testlist = json.load(f)
            print("Got script tests from %s; will not download."%(txintests_local,))
        except IOError:
            print("Couldn't get script tests from %s; downloading from %s..."%(txintests_local,txintests_url))
            testlist = requests.get(txintests_url).json()

        print("Starting %d tests on SLP's input validation"%len(testlist))
        for test in testlist:
            description = test['description']

            given_validity  = {}
            #should_validity = {}
            txes = {}
            for d in test['when']:
                tx = Transaction(d['tx'])
                txid = tx.txid()
                txes[txid] = tx
                if d['valid'] is True:
                    given_validity[txid] = 1
                elif d['valid'] is False:
                    given_validity[txid] = 2
                else:
                    raise ValueError(d['valid'])

            for d in test['should']:
                tx = Transaction(d['tx'])
                txid = tx.txid()
                txes[txid] = tx
                d['txid'] = txid
                #if d['valid'] is True:
                    #should_validity[txid] = 1
                #elif d['valid'] is False:
                    #should_validity[txid] = 2
                #else:
                    #raise ValueError(d['valid'])

            graph_context, graph_context_nft1 = slp_validator_0x01.GraphContext(), slp_validator_0x01_nft1.GraphContext_NFT1()

            for i, d in enumerate(test['should']):
                txid = d['txid']
                with self.subTest(description=description, i=i):
                    try:
                        slp_msg = slp.SlpMessage.parseSlpOutputScript(txes[txid].outputs()[0][1])
                        if slp_msg.token_type == 1:
                            graph, job_mgr = graph_context.setup_job(txes[txid], reset=True)
                        elif slp_msg.token_type == 65 or slp_msg.token_type == 129:
                            graph, job_mgr = graph_context_nft1.setup_job(txes[txid], reset=True)
                        else:
                            raise slp.SlpUnsupportedSlpTokenType(slp_msg.token_type)
                    except slp.SlpInvalidOutputMessage: # If output 0 is not OP_RETURN
                        self.assertEqual(d['valid'], False)
                        continue
                    except slp.SlpUnsupportedSlpTokenType:
                        self.assertEqual(d['valid'], False)
                        continue

                    def fetch_hook(txids, job):
                        l = []
                        for txid in txids:
                            try:
                                l.append(txes[txid])
                            except KeyError:
                                #raise Exception('KEY ERROR ' + txid)
                                pass
                        ### Call proxy here!
                        return l

                    if slp_msg.token_type == 1:
                        job = slp_validator_0x01.ValidationJob(graph, txid, None,
                                            fetch_hook = fetch_hook, validitycache=given_validity)
                    elif slp_msg.token_type == 65:
                        network = MockNetwork(txes)
                        storage = WalletStorage(os.path.curdir, manual_upgrades=True, in_memory_only=True)
                        wallet = Slp_ImportedAddressWallet(storage)
                        wallet.slp_graph_0x01_nft = graph_context_nft1
                        #raise Exception(txid)
                        job = slp_validator_0x01_nft1.ValidationJobNFT1Child(graph, txid, network,
                                            fetch_hook=fetch_hook, validitycache=None, ref=wallet)
                    elif slp_msg.token_type == 129:
                        job = slp_validator_0x01_nft1.ValidationJob(graph, txid, None,
                                            fetch_hook=fetch_hook, validitycache=given_validity)
                    #if txid == '8a08b78ae434de0b1a26e56ae7e78bb11b20f8240eb3d97371fd46a609df7fc3':
                        #graph.debugging = True
                        #job.debugging_graph_state = True
                    q = Queue()
                    job.add_callback(q.put)
                    job_mgr.add_job(job)
                    while True:
                        try:
                            q.get(timeout=3) # unlimited timeout
                        except Empty:
                            raise RuntimeError("Timeout during validation unit test")
                        # if isinstance(job, ValidationJobNFT1Child) and not job.paused:# and job.stop_reason != 'inconclusive':
                        #     raise Exception(job.stop_reason)
                        if not job.paused and not job.running: # and job.stop_reason != 'inconclusive':
                            n = next(iter(job.nodes.values()))
                            if d['valid'] is True:
                                self.assertEqual(n.validity, 1)
                            elif d['valid'] is False:
                                if test.get('allow_inconclusive', False): # "allow_inconclusive" allows for ending with an "unvalidated" state for harder corner-cases
                                    self.assertIn(n.validity, (0,2,3,4))
                                else:
                                    self.assertIn(n.validity, (2,3,4))
                            else:
                                raise ValueError(d['valid'])
                            break
                        else:
                            if len(job.callbacks) > 1:
                                raise Exception("shouldn't have more than 1 callback")
                            job.callbacks.clear()
                            job.add_callback(q.put, allow_run_cb_now=False)
