import copy
import datetime
from functools import partial
import json
import threading
import sys, traceback

from PyQt5.QtCore import *
from PyQt5.QtGui import *
from PyQt5.QtWidgets import *

from electrum_zclassic.address import Address, PublicKey
from electrum_zclassic.bitcoin import base_encode, TYPE_ADDRESS
from electrum_zclassic.i18n import _
from electrum_zclassic.plugins import run_hook

from .util import *

from electrum_zclassic.util import bfh, format_satoshis_nofloat, format_satoshis_plain_nofloat, NotEnoughFunds, ExcessiveFee, finalization_print_error
from electrum_zclassic.transaction import Transaction
from electrum_zclassic.slp import SlpMessage, SlpUnsupportedSlpTokenType, SlpInvalidOutputMessage, buildGenesisOpReturnOutput_V1, buildSendOpReturnOutput_V1
from electrum_zclassic.slp_checker import SlpTransactionChecker
from .amountedit import SLPAmountEdit
from .transaction_dialog import show_transaction

from .bfp_upload_file_dialog import BitcoinFilesUploadDialog

from electrum_zclassic import constants

dialogs = []  # Otherwise python randomly garbage collects the dialogs...

def get_nft_parent_coin(nft_parent_id, main_window):
    # get nft_parent's coins
    nft_parent_coins = main_window.wallet.get_slp_utxos(
        nft_parent_id,
        domain=None,
        exclude_frozen=True,
        confirmed_only=main_window.config.get('confirmed_only', False),
        slp_include_invalid=False,
        slp_include_baton=False
        )

    # determine if parent coin has qty 1 to burn
    selected_coin = None
    for coin in nft_parent_coins:
        if coin['token_value'] == 1:
            selected_coin = coin
            break

    return selected_coin

class SlpCreateTokenGenesisDialog(QDialog, MessageBoxMixin):

    def __init__(self, main_window, *, nft_parent_id=None):
        #self.provided_token_name = token_name
        # We want to be a top-level window
        QDialog.__init__(self, parent=None)
        from .main_window import ElectrumWindow

        assert isinstance(main_window, ElectrumWindow)
        main_window._slp_dialogs.add(self)
        finalization_print_error(self)  # track object lifecycle

        self.main_window = main_window
        self.wallet = main_window.wallet
        self.config = main_window.config
        self.network = main_window.network
        self.app = main_window.app
        self.nft_parent_id = nft_parent_id
        if nft_parent_id != None:
            self.token_type = 65
        else:
            self.token_type = 1

        if self.main_window.gui_object.warn_if_no_network(self.main_window):
            return

        self.setWindowTitle(_("Create a New Token"))

        vbox = QVBoxLayout()
        self.setLayout(vbox)

        grid = QGridLayout()
        grid.setColumnStretch(1, 1)
        vbox.addLayout(grid)
        row = 0

        msg = _('An optional name string embedded in the token genesis transaction.')
        grid.addWidget(HelpLabel(_('Token Name (optional):'), msg), row, 0)
        self.token_name_e = QLineEdit()
        grid.addWidget(self.token_name_e, row, 1)
        row += 1

        msg = _('An optional ticker symbol string embedded into the token genesis transaction.')
        grid.addWidget(HelpLabel(_('Ticker Symbol (optional):'), msg), row, 0)
        self.token_ticker_e = QLineEdit()
        self.token_ticker_e.setFixedWidth(110)
        self.token_ticker_e.textChanged.connect(self.upd_token)
        grid.addWidget(self.token_ticker_e, row, 1)
        row += 1

        msg = _('An optional URL string embedded into the token genesis transaction.')
        grid.addWidget(HelpLabel(_('Document URL (optional):'), msg), row, 0)
        self.token_url_e = QLineEdit()
        self.token_url_e.setFixedWidth(560)
        self.token_url_e.textChanged.connect(self.upd_token)
        grid.addWidget(self.token_url_e, row, 1)
        row += 1

        msg = _('An optional hash hexidecimal bytes embedded into the token genesis transaction for hashing') \
                                                    + 'the document file contents at the URL provided above.'
        grid.addWidget(HelpLabel(_('Document Hash (optional):'), msg), row, 0)
        self.token_dochash_e = QLineEdit()
        self.token_dochash_e.setInputMask("HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH")
        self.token_dochash_e.setFixedWidth(560)
        self.token_dochash_e.textChanged.connect(self.upd_token)
        grid.addWidget(self.token_dochash_e, row, 1)
        row += 1

        msg = _('Sets the number of decimals of divisibility for this token (embedded into genesis).') \
                + '\n\n' \
                + _('Each 1 token is divisible into 10^(decimals) base units, and internally in the protocol') \
                + _('the token amounts are represented as 64-bit integers measured in these base units.')
        grid.addWidget(HelpLabel(_('Decimal Places:'), msg), row, 0)
        self.token_ds_e = QDoubleSpinBox()
        self.token_ds_e.setRange(0, 9)
        self.token_ds_e.setDecimals(0)
        self.token_ds_e.setFixedWidth(50)
        self.token_ds_e.valueChanged.connect(self.upd_token)
        grid.addWidget(self.token_ds_e, row, 1)
        row += 1

        msg = _('The number of tokens created during token genesis transaction,') \
                                    + _('send to the receiver address provided below.')
        if nft_parent_id == None:
            self.token_qty_label = HelpLabel(_('Token Quantity:'), msg)
        else:
            self.token_qty_label = HelpLabel(_('Number of Child NFTs:'), msg)
        grid.addWidget(self.token_qty_label, row, 0)
        self.token_qty_e = SLPAmountEdit('', 0)
        self.token_qty_e.setFixedWidth(200)
        self.token_qty_e.textChanged.connect(self.check_token_qty)
        grid.addWidget(self.token_qty_e, row, 1)
        row += 1

        msg = _('The \'simpleledger:\' formatted bitcoin address for the genesis receiver of all genesis tokens.')
        grid.addWidget(HelpLabel(_('Token Receiver Address:'), msg), row, 0)
        self.token_pay_to_e = ButtonsLineEdit()
        self.token_pay_to_e.setFixedWidth(560)
        grid.addWidget(self.token_pay_to_e, row, 1)
        try:
            slpAddr = self.wallet.get_unused_address().to_slpaddr()
            self.token_pay_to_e.setText(Address.prefix_from_address_string(slpAddr) + ":" + slpAddr)
        except:
            pass
        row += 1

        self.token_fixed_supply_cb = cb = QCheckBox(_('Fixed Supply'))
        self.token_fixed_supply_cb.setChecked(True)
        grid.addWidget(self.token_fixed_supply_cb, row, 1)
        cb.clicked.connect(self.show_mint_baton_address)
        row += 1

        self.token_nft_parent_cb = cb = QCheckBox(_('Is NFT Parent?'))
        self.token_nft_parent_cb.setChecked(False)
        grid.addWidget(self.token_nft_parent_cb, row, 1)
        cb.clicked.connect(self.token_nft_parent_cb_update)
        row += 1

        if self.nft_parent_id:
            self.token_nft_parent_cb.setDisabled(True)
            self.token_fixed_supply_cb.setDisabled(True)
            self.token_qty_e.setAmount(1)
            self.token_qty_e.setDisabled(True)
            self.token_ds_e.setDisabled(True)

        msg = _('The \'simpleledger:\' formatted bitcoin address for the "minting baton" receiver.') + '\n\n' \
                + _('After the genesis transaction, further unlimited minting operations can be performed by the owner of') \
                + ' the "minting baton" transaction output. This baton can be repeatedly used for minting operations but' \
                + ' it cannot be duplicated.'
        self.token_baton_label = HelpLabel(_('Address for Baton:'), msg)
        self.token_baton_label.setHidden(True)
        grid.addWidget(self.token_baton_label, row, 0)
        self.token_baton_to_e = ButtonsLineEdit()
        self.token_baton_to_e.setFixedWidth(560)
        self.token_baton_to_e.setHidden(True)
        grid.addWidget(self.token_baton_to_e, row, 1)
        row += 1

        if nft_parent_id: 
            nft_parent_coin = get_nft_parent_coin(nft_parent_id, main_window)
            if not get_nft_parent_coin(nft_parent_id, main_window):
                hbox2 = QHBoxLayout()
                vbox.addLayout(hbox2)
                warnpm = QIcon(":icons/warning.png").pixmap(20,20)
                self.warn1 = l = QLabel(); l.setPixmap(warnpm)
                hbox2.addWidget(l)
                self.warn_msg = msg = QLabel(_("     NOTE: The parent token needs to be split before a new NFT can be created, click 'Prepare Group Parent'."))
                hbox2.addWidget(msg)
                self.warn2 = l = QLabel(); l.setPixmap(warnpm)
                hbox2.addStretch(1)
                hbox2.addWidget(l)

        hbox = QHBoxLayout()
        vbox.addLayout(hbox)

        self.cancel_button = b = QPushButton(_("Cancel"))
        self.cancel_button.setAutoDefault(False)
        self.cancel_button.setDefault(False)
        b.clicked.connect(self.close)
        hbox.addWidget(self.cancel_button)

        hbox.addStretch(1)

        # self.hash_button = b = QPushButton(_("Compute Document Hash..."))
        # self.hash_button.setAutoDefault(False)
        # self.hash_button.setDefault(False)
        # b.clicked.connect(self.hash_file)
        # b.setDefault(True)
        # hbox.addWidget(self.hash_button)

        # self.tok_doc_button = b = QPushButton(_("Upload a Token Document..."))
        # self.tok_doc_button.setAutoDefault(False)
        # self.tok_doc_button.setDefault(False)
        # b.clicked.connect(self.show_upload)
        # b.setDefault(True)
        # hbox.addWidget(self.tok_doc_button)

        self.preview_button = EnterButton(_("Preview"), self.do_preview)
        hbox.addWidget(self.preview_button)

        self.create_button = b = QPushButton(_("Create New Token")) #if self.provided_token_name is None else _("Change"))
        b.clicked.connect(self.create_token)
        self.create_button.setAutoDefault(True)
        self.create_button.setDefault(True)
        hbox.addWidget(self.create_button)

        if nft_parent_id:
            self.create_button.setText("Create NFT")
            if not nft_parent_coin:
                self.create_button.setHidden(True)
                self.prepare_parent_bttn = QPushButton(_("Prepare Group Parent"))
                self.prepare_parent_bttn.clicked.connect(self.prepare_nft_parent)
                self.prepare_parent_bttn.setAutoDefault(True)
                self.prepare_parent_bttn.setDefault(True)
                hbox.addWidget(self.prepare_parent_bttn)
                self.token_name_e.setDisabled(True)
                self.token_ticker_e.setDisabled(True)
                self.token_url_e.setDisabled(True)
                self.token_dochash_e.setDisabled(True)
                self.token_pay_to_e.setDisabled(True)
                self.token_baton_to_e.setDisabled(True)

        dialogs.append(self)
        self.show()
        self.token_name_e.setFocus()

    def show_upload(self):
        d = BitcoinFilesUploadDialog(self)
        dialogs.append(d)
        d.setModal(True)
        d.show()

    def do_preview(self):
        if self.nft_parent_id and not get_nft_parent_coin(self.nft_parent_id, self.main_window):
            self.prepare_nft_parent(preview=True)
            return
        self.create_token(preview=True)

    def hash_file(self):
        options = QFileDialog.Options()
        options |= QFileDialog.DontUseNativeDialog
        filename, _ = QFileDialog.getOpenFileName(self,"Compute SHA256 For File", "","All Files (*)", options=options)
        if filename != '':
            with open(filename,"rb") as f:
                bytes = f.read() # read entire file as bytes
                import hashlib
                readable_hash = hashlib.sha256(bytes).hexdigest()
                self.token_dochash_e.setText(readable_hash)

    def upd_token(self,):
        self.token_qty_e.set_token(self.token_ticker_e.text(), int(self.token_ds_e.value()))

        # force update (will truncate excess decimals)
        self.token_qty_e.numbify()
        self.token_qty_e.update()
        self.check_token_qty()

    def show_mint_baton_address(self):
        self.token_baton_to_e.setHidden(self.token_fixed_supply_cb.isChecked())
        self.token_baton_label.setHidden(self.token_fixed_supply_cb.isChecked())

    def token_nft_parent_cb_update(self):
        if self.token_nft_parent_cb.isChecked():
            self.token_type = 129
            self.token_ds_e.setDisabled(True)
            self.token_ds_e.setValue(0)
            self.upd_token()
        else:
            self.token_type = 1
            self.token_ds_e.setDisabled(False)

    def parse_address(self, address):
        if constants.net.SLPADDR_PREFIX not in address:
            address = constants.net.SLPADDR_PREFIX + ":" + address
        return Address.from_string(address)

    def prepare_nft_parent(self, preview=False):

        self.show_message("An initial preparation transaction is required before a new NFT can be created. This ensures only 1 parent token is burned in the NFT Genesis transaction.\n\nAfter this is transaction is broadcast you can proceed to fill out the NFT details and then click 'Create NFT'.")

        # IMPORTANT: set wallet.sedn_slpTokenId to None to guard tokens during this transaction
        self.main_window.token_type_combo.setCurrentIndex(0)
        assert self.main_window.slp_token_id == None

        coins = self.main_window.get_coins()
        fee = None

        try:
            selected_coin = None
            nft_parent_coins = self.main_window.wallet.get_slp_utxos(
                                        self.nft_parent_id,
                                        domain=None,
                                        exclude_frozen=True,
                                        confirmed_only=self.main_window.config.get('confirmed_only', False),
                                        slp_include_invalid=False,
                                        slp_include_baton=False
                                        )
            for coin in nft_parent_coins:
                if coin['token_value'] > 1:
                    selected_coin = coin
                    break

            if selected_coin['token_value'] < 19:
                slp_qtys = [1] * selected_coin['token_value']
            elif selected_coin['token_value'] >= 19:
                slp_qtys = [1] * 18
                slp_qtys.append(selected_coin['token_value'] - 18)
            outputs = []
            try:
                slp_op_return_msg = buildSendOpReturnOutput_V1(self.nft_parent_id, slp_qtys, token_type=129)
                outputs.append(slp_op_return_msg)
            except OPReturnTooLarge:
                self.show_message(_("Optional string text causiing OP_RETURN greater than 223 bytes."))
                return
            except Exception as e:
                traceback.print_exc(file=sys.stdout)
                self.show_message(str(e))
                return
            try:
                addr = self.parse_address(self.token_pay_to_e.text())
                for i in slp_qtys:
                    outputs.append((TYPE_ADDRESS, addr, 546))
            except:
                self.show_message(_("Must have Receiver Address in simpleledger format."))
                return
            if selected_coin:
                tx = self.main_window.wallet.make_unsigned_transaction(coins,
                        outputs, self.main_window.config, fee, None, mandatory_coins=[selected_coin])
            else:
                self.show_message(_("Unable to select a parent coin to prepare."))
                return 
        except NotEnoughFunds:
            self.show_message(_("Insufficient funds"))
            return
        except ExcessiveFee:
            self.show_message(_("Your fee is too high.  Max is 50 sat/byte."))
            return
        except BaseException as e:
            traceback.print_exc(file=sys.stdout)
            self.show_message(str(e))
            return
        if preview:
            show_transaction(tx, self.main_window, None, False, self, slp_coins_to_burn=[selected_coin])
            return

        msg = []

        if self.main_window.wallet.has_password():
            msg.append("")
            msg.append(_("Enter your password to proceed"))
            password = self.main_window.password_dialog('\n'.join(msg))
            if not password:
                return
        else:
            password = None
        tx_desc = None
        
        def sign_done(success):
            if success:
                if not tx.is_complete():
                    show_transaction(tx, self.main_window, None, False, self)
                    self.main_window.do_clear()
                else:
                    token_id = tx.txid()
                    if self.token_name_e.text() == '':
                        wallet_name = tx.txid()[0:5]
                    else:
                        wallet_name = self.token_name_e.text()[0:20]
                    # Check for duplication error
                    d = self.wallet.token_types.get(token_id)
                    for tid, d in self.wallet.token_types.items():
                        if d['name'] == wallet_name and tid != token_id:
                            wallet_name = wallet_name + "-" + token_id[:3]
                            break
                    self.broadcast_transaction(tx, self.token_name_e.text(), wallet_name, is_nft_prep=True)
                    self.token_name_e.setDisabled(False)
                    self.token_ticker_e.setDisabled(False)
                    self.token_url_e.setDisabled(False)
                    self.token_dochash_e.setDisabled(False)
                    self.token_pay_to_e.setDisabled(False)
                    self.token_baton_to_e.setDisabled(False)
                    self.warn1.setHidden(True)
                    self.warn2.setHidden(True)
                    self.warn_msg.setHidden(True)
                    
        self.sign_tx_with_password(tx, sign_done, password, slp_coins_to_burn=[selected_coin])

    def create_token(self, preview=False):
        token_name = self.token_name_e.text() if self.token_name_e.text() != '' else None
        ticker = self.token_ticker_e.text() if self.token_ticker_e.text() != '' else None
        token_document_url = self.token_url_e.text() if self.token_url_e.text() != '' else None
        token_document_hash_hex = self.token_dochash_e.text() if self.token_dochash_e.text() != '' else None
        decimals = int(self.token_ds_e.value())
        mint_baton_vout = 2 if self.token_baton_to_e.text() != '' and not self.token_fixed_supply_cb.isChecked() else None

        init_mint_qty = self.token_qty_e.get_amount()
        if init_mint_qty is None:
            self.show_message(_("Invalid token quantity entered."))
            return
        if init_mint_qty > (2 ** 64) - 1:
            maxqty = format_satoshis_plain_nofloat((2 ** 64) - 1, decimals)
            self.show_message(_("Token output quantity is too large. Maximum %s.")%(maxqty,))
            return

        if token_document_hash_hex != None:
            if len(token_document_hash_hex) != 64:
                self.show_message(_("Token document hash must be a 32 byte hexidecimal string or left empty."))
                return

        outputs = []
        try:
            slp_op_return_msg = buildGenesisOpReturnOutput_V1(ticker, token_name, token_document_url,
                                                                token_document_hash_hex, decimals, mint_baton_vout,
                                                                init_mint_qty, token_type=self.token_type)
            outputs.append(slp_op_return_msg)
        except OPReturnTooLarge:
            self.show_message(_("Optional string text causiing OP_RETURN greater than 223 bytes."))
            return
        except Exception as e:
            traceback.print_exc(file=sys.stdout)
            self.show_message(str(e))
            return

        try:
            addr = self.parse_address(self.token_pay_to_e.text())
            outputs.append((TYPE_ADDRESS, addr, 546))
        except:
            self.show_message(_("Must have Receiver Address in simpleledger format."))
            return

        if not self.token_fixed_supply_cb.isChecked() and not self.nft_parent_id:
            try:
                addr = self.parse_address(self.token_baton_to_e.text())
                outputs.append((TYPE_ADDRESS, addr, 546))
            except:
                self.show_message(_("Must have Baton Address in simpleledger format."))
                return

        # IMPORTANT: set wallet.sedn_slpTokenId to None to guard tokens during this transaction
        self.main_window.token_type_combo.setCurrentIndex(0)
        assert self.main_window.slp_token_id == None

        coins = self.main_window.get_coins()
        fee = None

        try:
            selected_coin = None
            if self.nft_parent_id:
                selected_coin = get_nft_parent_coin(self.nft_parent_id, self.main_window)
                if selected_coin:
                    tx = self.main_window.wallet.make_unsigned_transaction(coins,
                            outputs, self.main_window.config, fee, None, mandatory_coins=[selected_coin])
                else:
                    raise Exception('Must have a parent NFT coin with value of 1 first.')
            else:
                tx = self.main_window.wallet.make_unsigned_transaction(coins,
                                    outputs, self.main_window.config, fee, None)
        except NotEnoughFunds:
            self.show_message(_("Insufficient funds"))
            return
        except ExcessiveFee:
            self.show_message(_("Your fee is too high.  Max is 50 sat/byte."))
            return
        except BaseException as e:
            traceback.print_exc(file=sys.stdout)
            self.show_message(str(e))
            return

        if preview:
            show_transaction(tx, self.main_window, None, False, self, slp_coins_to_burn=[selected_coin])
            return

        msg = []

        if self.main_window.wallet.has_password():
            msg.append("")
            msg.append(_("Enter your password to proceed"))
            password = self.main_window.password_dialog('\n'.join(msg))
            if not password:
                return
        else:
            password = None
        tx_desc = None

        def sign_done(success):
            if success:
                if not tx.is_complete():
                    show_transaction(tx, self.main_window, None, False, self)
                    self.main_window.do_clear()
                else:
                    token_id = tx.txid()
                    if self.token_name_e.text() == '':
                        wallet_name = tx.txid()[0:5]
                    else:
                        wallet_name = self.token_name_e.text()[0:20]
                    # Check for duplication error
                    d = self.wallet.token_types.get(token_id)
                    for tid, d in self.wallet.token_types.items():
                        if d['name'] == wallet_name and tid != token_id:
                            wallet_name = wallet_name + "-" + token_id[:3]
                            break
                    self.broadcast_transaction(tx, self.token_name_e.text(), wallet_name)
        self.sign_tx_with_password(tx, sign_done, password, slp_coins_to_burn=[selected_coin])

    def sign_tx_with_password(self, tx, callback, password, *, slp_coins_to_burn=None):
        '''Sign the transaction in a separate thread.  When done, calls
        the callback with a success code of True or False.
        '''

        # check transaction SLP validity before signing
        try:
            assert SlpTransactionChecker.check_tx_slp(self.wallet, tx, coins_to_burn=slp_coins_to_burn)
        except (Exception, AssertionError) as e:
            self.show_warning(str(e))
            return

        # call hook to see if plugin needs gui interaction
        run_hook('sign_tx', self, tx)

        def on_signed(result):
            callback(True)

        def on_failed(exc_info):
            self.main_window.on_error(exc_info)
            callback(False)

        if self.main_window.tx_external_keypairs:
            task = partial(Transaction.sign, tx, self.main_window.tx_external_keypairs)
        else:
            task = partial(self.wallet.sign_transaction, tx, password)
        WaitingDialog(self, _('Signing transaction...'), task, on_signed, on_failed)

    def broadcast_transaction(self, tx, token_name, token_wallet_name, is_nft_prep=False):
        # Capture current TL window; override might be removed on return
        parent = self.top_level_window()
        if self.main_window.gui_object.warn_if_no_network(self):
            # Don't allow a useless broadcast when in offline mode. Previous to this we were getting an exception on broadcast.
            return
        elif not self.network.is_connected():
            # Don't allow a potentially very slow broadcast when obviously not connected.
            #parent.show_error(_("Not connected"))
            return

        def broadcast_thread():
            # non-GUI thread
            status = False
            msg = "Failed"
            status, msg =  self.network.broadcast(tx)
            return status, msg

        def broadcast_done(result):
            # GUI thread
            if result:
                status, msg = result
                if status:
                    token_id = msg
                    if is_nft_prep:
                        parent.show_message("Transaction Id: " + token_id + "\n\nReady to create NFT, please click 'Create NFT'")
                        self.create_button.setHidden(False)
                        self.create_button.setDefault(True)
                        self.prepare_parent_bttn.setHidden(True)
                    else:
                        self.main_window.add_token_type('SLP%d'%(self.token_type,), token_id, token_wallet_name, int(self.token_ds_e.value()), allow_overwrite=True)
                        if tx.is_complete():
                            self.wallet.set_label(token_id, "ZSLP Token Created: " + token_wallet_name)
                        if token_name == '':
                            parent.show_message("ZSLP Token Created.\n\nName in wallet: " + token_wallet_name + "\nTokenId: " + token_id)
                        elif token_name != token_wallet_name:
                            parent.show_message("ZSLP Token Created.\n\nName in wallet: " + token_wallet_name + "\nName on blockchain: " + token_name + "\nTokenId: " + token_id)
                        else:
                            parent.show_message("ZSLP Token Created.\n\nName: " + token_name + "\nToken ID: " + token_id)
                else:
                    if msg.startswith("error: "):
                        msg = msg.split(" ", 1)[-1] # take the last part, sans the "error: " prefix
                    self.show_error(msg)
            if not is_nft_prep:
                self.close()
        if self.nft_parent_id and is_nft_prep:
            msg = 'Preparing for a new NFT...'
        elif self.nft_parent_id:
            msg = 'Creating NFT Token...'
        else:
            msg = 'Creating ZSLP Token...' 
        WaitingDialog(self, msg, broadcast_thread, broadcast_done, None)


    def closeEvent(self, event):
        super().closeEvent(event)
        event.accept()
        self.main_window.create_token_dialog = None
        def remove_self():
            try: dialogs.remove(self)
            except ValueError: pass  # wasn't in list.
        QTimer.singleShot(0, remove_self)  # need to do this some time later. Doing it from within this function causes crashes. See #35

    def update(self):
        return

    def check_token_qty(self):
        try:
            if self.token_qty_e.get_amount() > 18446744073709551615:
                self.token_qty_e.setAmount(18446744073709551615)
            #if not self.token_fixed_supply_cb.isChecked():
            #    self.show_warning(_("If you issue this much, users will may find it awkward to transfer large amounts, as each transaction output may only take up to ~" + str(self.token_qty_e.text()) + " tokens, thus requiring multiple outputs for very large amounts."))
        except:
            pass
