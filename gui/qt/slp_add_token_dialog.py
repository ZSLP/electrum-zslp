
import copy
import datetime
from functools import partial
import json
import threading
import html
import traceback

from PyQt5.QtCore import *
from PyQt5.QtGui import *
from PyQt5.QtWidgets import *

from electrum_zclassic import constants
from electrum_zclassic.address import Address, PublicKey
from electrum_zclassic.bitcoin import base_encode
from electrum_zclassic.i18n import _
from electrum_zclassic.plugins import run_hook

from electrum_zclassic.util import bfh
from .util import *

from electrum_zclassic.util import format_satoshis_nofloat, finalization_print_error
from electrum_zclassic.transaction import Transaction
from electrum_zclassic.slp import SlpMessage, SlpUnsupportedSlpTokenType, SlpInvalidOutputMessage

dialogs = []  # Otherwise python randomly garbage collects the dialogs...

class SlpAddTokenDialog(QDialog, MessageBoxMixin):

    got_network_response_sig = pyqtSignal()

    @pyqtSlot()
    def got_network_response_slot(self):
        self.download_finished = True

        resp = self.json_response
        if resp.get('error'):
            return self.fail_genesis_info("Download error!\n%r"%(resp['error'].get('message')))
        raw = resp.get('result')

        tx = Transaction(raw)
        self.handle_genesis_tx(tx)

    def __init__(self, main_window, token_id_hex=None, token_name=None, allow_overwrite=False, add_callback=None):
        # We want to be a top-level window
        QDialog.__init__(self, parent=None)
        from .main_window import ElectrumWindow

        assert isinstance(main_window, ElectrumWindow)
        main_window._slp_dialogs.add(self)
        finalization_print_error(self)  # Track object lifecycle

        self.provided_token_name = token_name
        self.allow_overwrite = allow_overwrite
        self.add_callback = add_callback
        self.main_window = main_window
        self.wallet = main_window.wallet
        self.network = main_window.network
        self.app = main_window.app

        if self.main_window.gui_object.warn_if_no_network(self.main_window):
            return

        if self.provided_token_name:
            self.setWindowTitle(_("ZSLP Token Details"))
        else:
            self.setWindowTitle(_("Add ZSLP Token"))

        vbox = QVBoxLayout()
        self.setLayout(vbox)

        vbox.addWidget(QLabel(_('Token ID:')))


        self.token_id_e = ButtonsLineEdit()
        if token_id_hex is not None:
            self.token_id_e.addCopyButton(self.app)
        vbox.addWidget(self.token_id_e)


        hbox = QHBoxLayout()
        vbox.addLayout(hbox)

        hbox.addWidget(QLabel(_('Genesis transaction information:')))

        self.get_info_button = b = QPushButton(_("Download"))
        b.clicked.connect(self.download_info)
        hbox.addWidget(b)

        self.load_tx_menu_button = b = QPushButton(_("Load..."))
        menu = QMenu()
        menu.addAction(_("&From file"), self.do_process_from_file)
        menu.addAction(_("&From text"), self.do_process_from_text)
        menu.addAction(_("&From QR code"), self.read_tx_from_qrcode)
        b.setMenu(menu)
        hbox.addWidget(b)

        self.view_tx_button = b = QPushButton(_("View Tx"))
        b.clicked.connect(self.view_tx)
        b.setDisabled(True)
        hbox.addWidget(b)

        hbox.addStretch(1)

        self.token_info_e = QTextBrowser()
        self.token_info_e.setOpenExternalLinks(True)
        self.token_info_e.setMinimumHeight(100)
        vbox.addWidget(self.token_info_e)

        hbox = QHBoxLayout()
        vbox.addLayout(hbox)

        warnpm = QIcon(":icons/warning.png").pixmap(20,20)

        l = QLabel(); l.setPixmap(warnpm)
        hbox.addWidget(l)
        hbox.addWidget(QLabel(_('Avoid counterfeits—carefully compare the token ID with a trusted source.')))
        l = QLabel(); l.setPixmap(warnpm)
        hbox.addWidget(l)

        if self.provided_token_name is None:
            namelabel = QLabel(_('To use tokens with this ID, assign it a name.'))
            namelabel.setAlignment(Qt.AlignRight)
            vbox.addWidget(namelabel)

        hbox = QHBoxLayout()
        vbox.addLayout(hbox)

        self.cancel_button = b = QPushButton(_("Cancel"))
        self.cancel_button.setAutoDefault(False)
        self.cancel_button.setDefault(False)
        b.clicked.connect(self.close)
        b.setDefault(True)
        hbox.addWidget(self.cancel_button)

        hbox.addStretch(1)

        hbox.addWidget(QLabel(_('Name in wallet:')))
        self.token_name_e = QLineEdit()
        self.token_name_e.setFixedWidth(200)
        if self.provided_token_name is not None:
            self.token_name_e.setText(self.provided_token_name)
        hbox.addWidget(self.token_name_e)


        self.add_button = b = QPushButton(_("Add") if self.provided_token_name is None else _("Change"))
        b.clicked.connect(self.add_token)
        self.add_button.setAutoDefault(True)
        self.add_button.setDefault(True)
        b.setDisabled(True)
        hbox.addWidget(self.add_button)

        if token_id_hex is not None:
            self.token_id_e.setText(token_id_hex)
            self.download_info()

        self.got_network_response_sig.connect(self.got_network_response_slot, Qt.QueuedConnection)
        self.update()

        dialogs.append(self)
        self.show()

        self.token_name_e.setFocus()

    def closeEvent(self, event):
        super().closeEvent(event)
        if event.isAccepted():
            try: self.got_network_response_sig.disconnect()  # prevent future asynch responses from doing anything if we are closed.
            except TypeError: pass  # not connected
            def remove_self():
                try: dialogs.remove(self)
                except ValueError: pass  # wasn't in list.
            QTimer.singleShot(0, remove_self)  # need to do this some time later. Doing it from within this function causes crashes. See #35

    def download_info(self):
        txid = self.token_id_e.text()

        self.token_id_e.setReadOnly(True)
        self.token_info_e.setText("Downloading...")
        self.get_info_button.setDisabled(True)
        self.load_tx_menu_button.setDisabled(True)
        self.view_tx_button.setDisabled(True)

        try:
            tx = self.wallet.transactions[txid]
        except KeyError:
            def callback(response):
                self.json_response = response
                self.got_network_response_sig.emit()

            requests = [ ('blockchain.transaction.get', [txid]), ]
            self.network.send(requests, callback)
        else:
            self.handle_genesis_tx(tx)

    def handle_genesis_tx(self, tx):
        self.token_id_e.setReadOnly(True)
        self.get_info_button.setDisabled(True)
        self.load_tx_menu_button.setDisabled(True)

        self.newtoken_genesis_tx      = tx
        self.view_tx_button.setDisabled(False)

        txid = tx.txid()
        token_id = self.token_id_e.text().strip().lower()  # tolerate user to paste of uppercase hex with whitespace around it
        if token_id and txid != token_id:
            return self.fail_genesis_info(_('TXID does not match token ID!'))
        self.newtoken_token_id = txid
        self.token_id_e.setText(self.newtoken_token_id)

        try:
            slpMsg = SlpMessage.parseSlpOutputScript(tx.outputs()[0][1])
        except SlpUnsupportedSlpTokenType as e:
            return self.fail_genesis_info(_("Unsupported ZSLP token version/type - %r.")%(e.args[0],))
        except SlpInvalidOutputMessage as e:
            return self.fail_genesis_info(_("This transaction does not contain a valid ZSLP message.\nReason: %r.")%(e.args,))
        if slpMsg.transaction_type != 'GENESIS':
            return self.fail_genesis_info(_("This is an ZSLP transaction, however it is not a genesis transaction."))


        f_fieldnames = QTextCharFormat()
        f_fieldnames.setFont(QFont(MONOSPACE_FONT))
        f_normal = QTextCharFormat()

        self.token_info_e.clear()
        cursor = self.token_info_e.textCursor()

        fields = [
            ('ticker', _('ticker'), 'utf8', None),
            ('token_name', _('name'), 'utf8', None),
            ('token_doc_url', _('doc url'), 'ascii', 'html'),
            ('token_doc_hash', _('doc hash'), 'hex', None),
                 ]

        cursor.insertText(_('Issuer-declared strings in genesis:'))
        cursor.insertBlock()
        for k,n,e,f in fields:
            data = slpMsg.op_return_fields[k]
            if e == 'hex':
                friendlystring = None
            else:
                # Attempt to make a friendly string, or fail to hex
                try:
                    # Ascii only
                    friendlystring = data.decode(e) # raises UnicodeDecodeError with bytes > 127.

                    # Count ugly characters (that need escaping in python strings' repr())
                    uglies = 0
                    for b in data:
                        if b < 0x20 or b == 0x7f:
                            uglies += 1
                    # Less than half of characters may be ugly.
                    if 2*uglies >= len(data):
                        friendlystring = None
                except UnicodeDecodeError:
                    friendlystring = None

            if len(data) == 0:
                showstr = '(empty)'
                f=None
            elif friendlystring is None:
                showstr = data.hex()
                f=None
            else:
                showstr = repr(friendlystring)

            cursor.insertText(' '*(10 - len(n)) + n + ': ', f_fieldnames)
            if f == 'html':
                enc_url  = html.escape(friendlystring)
                enc_text = html.escape(showstr)
                cursor.insertHtml('<a href="%s" title="%s">%s</a>'%(enc_url, enc_url, enc_text))
            else:
                cursor.insertText(showstr, f_normal)
            cursor.insertBlock()

        # try to auto-fill name input
        name_ext = ''
        for key in [ 'ticker', 'token_name' ]:
            if self.token_name_e.text() == '' and slpMsg.op_return_fields[key] != b'':
                base_name = slpMsg.op_return_fields[key].decode("utf-8")
                for k,v in self.wallet.token_types.copy().items():
                    if v['name'] == base_name:
                        name_ext = "-" + self.token_id_e.text()[:3]
                self.token_name_e.setText(base_name + name_ext)
                break

        self.newtoken_decimals = slpMsg.op_return_fields['decimals']
        cursor.insertText(_('Decimals:') + ' ' + str(self.newtoken_decimals))
        cursor.insertBlock()

        numtokens = format_satoshis_nofloat(slpMsg.op_return_fields['initial_token_mint_quantity'],
                                    num_zeros=self.newtoken_decimals,
                                    decimal_point=self.newtoken_decimals,)
        mbv = slpMsg.op_return_fields['mint_baton_vout']
        if mbv is None or mbv > len(tx.outputs()):
            issuance_type = _('Initial issuance type: fixed supply')
        else:
            issuance_type = _('Initial issuance type: flexible supply')

        cursor.insertText(_('Initial issuance:') + ' ' + numtokens)
        cursor.insertBlock()
        cursor.insertText(issuance_type)

        #cursor.insertBlock()

        self.newtoken_genesis_message = slpMsg

        self.add_button.setDisabled(False)
        self.activateWindow()
        self.raise_()

    def fail_genesis_info(self, message):
        self.token_info_e.setText(message)
        self.add_button.setDisabled(True)
        self.token_id_e.setReadOnly(False)
        self.get_info_button.setDisabled(False)
        self.load_tx_menu_button.setDisabled(False)

    def view_tx(self,):
        self.main_window.show_transaction(self.newtoken_genesis_tx)

    def add_token(self):
        # Make sure to throw an error dialog if name exists, hash exists, ...
        token_name = self.token_name_e.text()
        ow = (self.provided_token_name is not None) or self.allow_overwrite
        token_class = 'SLP%d'%(self.newtoken_genesis_message.token_type,)
        ret = self.main_window.add_token_type(token_class, self.newtoken_token_id, token_name, self.newtoken_decimals,
                                              error_callback = self.show_error, allow_overwrite=ow)
        if ret:
            self.add_button.setDisabled(True)
            self.close()
            if self.add_callback:
                self.add_callback()
        else:
            # couldn't add for some reason...
            pass


    ### Ripped and modified from main_window.py --- load transaction manually!

    def user_loaded_transaction(self, tx):
        self.handle_genesis_tx(tx)

    def tx_from_text(self, txt):
        from electrum_zclassic.transaction import tx_from_str
        try:
            txt_tx = tx_from_str(txt)
            tx = Transaction(txt_tx, sign_schnorr=self.wallet.is_schnorr_enabled())
            tx.deserialize()
            return tx
        except:
            traceback.print_exc(file=sys.stdout)
            self.show_critical(_("Electron Cash was unable to parse your transaction"))
            return

    def read_tx_from_qrcode(self):
        from electrum_zclassic import qrscanner
        try:
            data = qrscanner.scan_barcode(self.main_window.config.get_video_device())
        except BaseException as e:
            self.show_error(str(e))
            return
        if not data:
            return
        # if the user scanned a bitcoincash URI
        if data.lower().startswith('zclassic:') or data.lower().startswith(constants.net.SLPADDR_PREFIX + ':'):
            self.show_error(_("This is not a transaction."))
            return
        # else if the user scanned an offline signed tx
        data = bh2u(bitcoin.base_decode(data, length=None, base=43))
        tx = self.tx_from_text(data)
        if not tx:
            return
        self.user_loaded_transaction(tx)

    def read_tx_from_file(self):
        fileName, __ = QFileDialog.getOpenFileName(self,_("Select your transaction file"), '', "*.txn")
        if not fileName:
            return
        try:
            with open(fileName, "r") as f:
                file_content = f.read()
        except (ValueError, IOError, os.error) as reason:
            self.show_critical(_("Electron Cash was unable to open your transaction file") + "\n" + str(reason), title=_("Unable to read file or no transaction found"))
            return
        file_content = file_content.strip()
        tx = self.tx_from_text(file_content)
        # Older saved transaction do not include this key.
        return tx

    def do_process_from_text(self):
        from electrum_zclassic.transaction import SerializationError
        text = text_dialog(self, _('Input raw transaction'), _("Transaction:"), _("Load transaction"))
        if not text:
            return
        try:
            tx = self.tx_from_text(text)
            if tx:
                self.user_loaded_transaction(tx)
        except SerializationError as e:
            self.show_critical(_("Electron Cash was unable to deserialize the transaction:") + "\n" + str(e))

    def do_process_from_file(self):
        from electrum_zclassic.transaction import SerializationError
        try:
            tx = self.read_tx_from_file()
            if tx:
                self.user_loaded_transaction(tx)
        except SerializationError as e:
            self.show_critical(_("Electron Cash was unable to deserialize the transaction:") + "\n" + str(e))
