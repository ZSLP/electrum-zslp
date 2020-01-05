#!/usr/bin/env python
#
# Electrum - lightweight ZClassic client
# Copyright (C) 2012 thomasv@gitorious
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

import re
import sys, time, threading
import os, json, traceback
import shutil
import weakref
import webbrowser
import csv
from decimal import Decimal
import base64
from functools import partial

from PyQt5.QtGui import *
from PyQt5.QtCore import *
import PyQt5.QtCore as QtCore

from .exception_window import Exception_Hook
from PyQt5.QtWidgets import *

from electrum_zclassic import keystore, simple_config
from electrum_zclassic.address import Address, ScriptOutput, AddressError
from electrum_zclassic.bitcoin import COIN, is_address, TYPE_ADDRESS, TYPE_SCRIPT
from electrum_zclassic import constants
from electrum_zclassic.plugins import run_hook
from electrum_zclassic.i18n import _
from electrum_zclassic.util import (format_time, format_satoshis, PrintError,
                                format_satoshis_plain, format_satoshis_plain_nofloat,
                                NotEnoughFunds, NotEnoughFundsSlp, NotEnoughUnfrozenFundsSlp, ExcessiveFee,
                                UserCancelled, NoDynamicFeeEstimates, profiler,
                                export_meta, import_meta, bh2u, bfh, InvalidPassword,
                                Weak)
import electrum_zclassic.web as web
from electrum_zclassic import Transaction
from electrum_zclassic import util, bitcoin, commands, coinchooser
from electrum_zclassic import paymentrequest
from electrum_zclassic.wallet import Multisig_Wallet, AddTransactionException

from .amountedit import AmountEdit, BTCAmountEdit, MyLineEdit, FeerateEdit
from .qrcodewidget import QRCodeWidget, QRDialog
from .qrtextedit import ShowQRTextEdit, ScanQRTextEdit
from .transaction_dialog import show_transaction
from .fee_slider import FeeSlider
from .util import *

import electrum_zclassic.slp as slp
from electrum_zclassic.slp_coinchooser import SlpCoinChooser
from electrum_zclassic.slp_checker import SlpTransactionChecker
from .amountedit import SLPAmountEdit
from electrum_zclassic.util import format_satoshis_nofloat
from .slp_create_token_genesis_dialog import SlpCreateTokenGenesisDialog
from .bfp_download_file_dialog import BfpDownloadFileDialog
from .bfp_upload_file_dialog import BitcoinFilesUploadDialog

class StatusBarButton(QPushButton):
    def __init__(self, icon, tooltip, func):
        QPushButton.__init__(self, icon, '')
        self.setToolTip(tooltip)
        self.setFlat(True)
        self.setMaximumWidth(25)
        self.clicked.connect(self.onPress)
        self.func = func
        self.setIconSize(QSize(25,25))

    def onPress(self, checked=False):
        '''Drops the unwanted PyQt5 "checked" argument'''
        self.func()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Return:
            self.func()


from electrum_zclassic.paymentrequest import PR_PAID


class ElectrumWindow(QMainWindow, MessageBoxMixin, PrintError):

    # Note: self.clean_up_connections automatically detects signals named XXX_signal and disconnects them on window close.
    payment_request_ok_signal = pyqtSignal()
    payment_request_error_signal = pyqtSignal()
    notify_transactions_signal = pyqtSignal()
    new_fx_quotes_signal = pyqtSignal()
    new_fx_history_signal = pyqtSignal()
    network_signal = pyqtSignal(str, object)
    alias_received_signal = pyqtSignal()
    computing_privkeys_signal = pyqtSignal()
    show_privkeys_signal = pyqtSignal()
    cashaddr_toggled_signal = pyqtSignal()
    slp_validity_signal = pyqtSignal(object, object)
    history_updated_signal = pyqtSignal()
    on_timer_signal = pyqtSignal()  # functions wanting to be executed from timer_actions should connect to this signal, preferably via Qt.DirectConnection

    def __init__(self, gui_object, wallet):
        QMainWindow.__init__(self)

        self.gui_object = gui_object
        self.wallet = wallet
        self.config = config = gui_object.config
        self.is_slp_wallet = "slp_" in self.wallet.storage.get('wallet_type', '')

        self._old_excepthook = None
        self.setup_exception_hook()
        self.network = gui_object.daemon.network
        self.fx = gui_object.daemon.fx
        self.invoices = wallet.invoices
        self.contacts = wallet.contacts
        self.tray = gui_object.tray
        self.app = gui_object.app
        self.cleaned_up = False
        self.is_max = False
        self.payment_request = None
        self.checking_accounts = False
        self.qr_window = None
        self.not_enough_funds = False
        self.not_enough_funds_slp = False
        self.not_enough_unfrozen_funds_slp = False
        self.op_return_toolong = False
        self.pluginsdialog = None
        self.require_fee_update = False
        self.tx_notifications = []
        self.tl_windows = []
        self.tx_external_keypairs = {}
        self._tx_dialogs = Weak.Set()
        self._slp_dialogs = Weak.Set()
        self.tx_update_mgr = TxUpdateMgr(self)  # manages network callbacks for 'new_transaction' and 'verified2', and collates GUI updates from said callbacks as a performance optimization
        # self.is_schnorr_enabled = self.wallet.is_schnorr_enabled  # This is a function -- Support for plugins that may be using the 4.0.3 & 4.0.4 API -- this function used to live in this class, before being moved to Abstract_Wallet.
        self.send_tab_opreturn_widgets, self.receive_tab_opreturn_widgets = [], []  # defaults to empty list
        self._shortcuts = Weak.Set()  # keep track of shortcuts and disable them on close

        self.create_status_bar()
        self.need_update = threading.Event()

        self.decimal_point = config.get('decimal_point', 8)
        self.num_zeros     = int(config.get('num_zeros', 8))

        self.completions = QStringListModel()

        self.tabs = tabs = QTabWidget(self)
        self.send_tab = self.create_send_tab()
        self.receive_tab = self.create_receive_tab()
        self.addresses_tab = self.create_addresses_tab()
        self.utxo_tab = self.create_utxo_tab()
        self.console_tab = self.create_console_tab()
        self.contacts_tab = self.create_contacts_tab()
        self.slp_mgt_tab = self.create_slp_mgt_tab()
        self.converter_tab = self.create_converter_tab()
        self.slp_history_tab = self.create_slp_history_tab()
        self.slp_token_id = None
        tabs.addTab(self.create_history_tab(), QIcon(":icons/tab_history.png"), _('History'))
        tabs.addTab(self.send_tab, QIcon(":icons/tab_send.png"), _('Send'))
        tabs.addTab(self.receive_tab, QIcon(":icons/tab_receive.png"), _('Receive'))
        # clears/inits the opreturn widgets
        self.on_toggled_opreturn(bool(self.config.get('enable_opreturn')))

        def add_optional_tab(tabs, tab, icon, description, name, default=False):
            tab.tab_icon = icon
            tab.tab_description = description
            tab.tab_pos = len(tabs)
            tab.tab_name = name
            if self.config.get('show_{}_tab'.format(name), default):
                tabs.addTab(tab, icon, description.replace("&", ""))

        add_optional_tab(tabs, self.addresses_tab, QIcon(":icons/tab_addresses.png"), _("&Addresses"), "addresses")
        add_optional_tab(tabs, self.utxo_tab, QIcon(":icons/tab_coins.png"), _("Co&ins"), "utxo")
        add_optional_tab(tabs, self.contacts_tab, QIcon(":icons/tab_contacts.png"), _("Con&tacts"), "contacts")
        add_optional_tab(tabs, self.converter_tab, QIcon(":icons/tab_converter.svg"), _("Address Converter"), "converter", True)
        add_optional_tab(tabs, self.console_tab, QIcon(":icons/tab_console.png"), _("Con&sole"), "console")
        if self.is_slp_wallet:
            add_optional_tab(tabs, self.slp_mgt_tab, QIcon(":icons/tab_slp_icon.png"), _("Tokens"), "tokens")
            add_optional_tab(tabs, self.slp_history_tab, QIcon(":icons/tab_slp_icon.png"), _("ZSLP History"), "zslp_history", True)

        tabs.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.setCentralWidget(tabs)

        if self.config.get("is_maximized"):
            self.showMaximized()

        self.setWindowIcon(QIcon(":icons/electrum-zclassic.png"))
        self.init_menubar()

        wrtabs = weakref.proxy(tabs)
        QShortcut(QKeySequence("Ctrl+W"), self, self.close)
        QShortcut(QKeySequence("Ctrl+Q"), self, self.close)
        QShortcut(QKeySequence("Ctrl+R"), self, self.update_wallet)
        QShortcut(QKeySequence("Ctrl+PgUp"), self, lambda: wrtabs.setCurrentIndex((wrtabs.currentIndex() - 1)%wrtabs.count()))
        QShortcut(QKeySequence("Ctrl+PgDown"), self, lambda: wrtabs.setCurrentIndex((wrtabs.currentIndex() + 1)%wrtabs.count()))

        for i in range(wrtabs.count()):
            QShortcut(QKeySequence("Alt+" + str(i + 1)), self, lambda i=i: wrtabs.setCurrentIndex(i))

        self.payment_request_ok_signal.connect(self.payment_request_ok)
        self.payment_request_error_signal.connect(self.payment_request_error)
        self.notify_transactions_signal.connect(self.notify_transactions)
        self.history_list.setFocus(True)
        self.slp_history_list.setFocus(True)

        # network callbacks
        if self.network:
            self.network_signal.connect(self.on_network_qt)
            interests = ['updated', 'new_transaction', 'status',
                         'banner', 'verified', 'fee']
            # To avoid leaking references to "self" that prevent the
            # window from being GC-ed when closed, callbacks should be
            # methods of this class only, and specifically not be
            # partials, lambdas or methods of subobjects.  Hence...
            self.network.register_callback(self.on_network, interests)
            # set initial message
            self.console.showMessage(self.network.banner)
            self.network.register_callback(self.on_quotes, ['on_quotes'])
            self.network.register_callback(self.on_history, ['on_history'])
            self.new_fx_quotes_signal.connect(self.on_fx_quotes)
            self.new_fx_history_signal.connect(self.on_fx_history)

        # update fee slider in case we missed the callback
        self.fee_slider.update()
        self.load_wallet(wallet)

        self.connect_slots(gui_object.timer)
        self.fetch_alias()

    def update_token_type_combo(self):
        self.token_type_combo.clear()
        self.receive_token_type_combo.clear()
        self.token_type_combo.addItem(QIcon(':icons/tab_coins.png'), 'None', None)
        self.receive_token_type_combo.addItem(QIcon(':icons/tab_coins.png'), 'None', None)

        try:
            token_types = self.wallet.token_types
        except AttributeError:
            pass
        else:
            sorted_items = sorted(token_types.items(), key=lambda x:x[1]['name'])
            for token_id, i in sorted_items:
                if i['decimals'] != '?':
                    self.token_type_combo.addItem(QIcon(':icons/tab_slp_icon.png'),i['name'], token_id)
                    self.receive_token_type_combo.addItem(QIcon(':icons/tab_slp_icon.png'),i['name'], token_id)

    def on_history(self, b):
        self.new_fx_history_signal.emit()

    def setup_exception_hook(self):
        Exception_Hook(self)

    @rate_limited(3.0) # Rate limit to no more than once every 3 seconds
    def on_fx_history(self):
        if self.cleaned_up: return
        self.history_list.refresh_headers()
        self.history_list.update()
        self.address_list.update()
        self.history_updated_signal.emit() # inform things like address_dialog that there's a new history

    def on_quotes(self, b):
        self.new_fx_quotes_signal.emit()

    def on_fx_quotes(self):
        self.update_status()
        # Refresh edits with the new rate
        edit = self.fiat_send_e if self.fiat_send_e.is_last_edited else self.amount_e
        edit.textEdited.emit(edit.text())
        edit = self.fiat_receive_e if self.fiat_receive_e.is_last_edited else self.receive_amount_e
        edit.textEdited.emit(edit.text())
        # History tab needs updating if it used spot
        if self.fx.history_used_spot:
            self.history_list.update()

    def toggle_tab(self, tab, forceStatus = 0):

        # forceStatus = 0 , do nothing
        # forceStatus = 1 , force Show
        # forceStatus = 2 , force hide
        if forceStatus==1:
            show=True
        elif forceStatus==2:
            show=False
        else:
            show = not self.config.get('show_{}_tab'.format(tab.tab_name), False)
        self.config.set_key('show_{}_tab'.format(tab.tab_name), show)
        item_text = (_("Hide") if show else _("Show")) + " " + tab.tab_description
        tab.menu_action.setText(item_text)
        if show:
            # Find out where to place the tab
            index = len(self.tabs)
            for i in range(len(self.tabs)):
                try:
                    if tab.tab_pos < self.tabs.widget(i).tab_pos:
                        index = i
                        break
                except AttributeError:
                    pass
            self.tabs.insertTab(index, tab, tab.tab_icon, tab.tab_description.replace("&", ""))
        else:
            i = self.tabs.indexOf(tab)
            self.tabs.removeTab(i)

    def push_top_level_window(self, window):
        '''Used for e.g. tx dialog box to ensure new dialogs are appropriately
        parented.  This used to be done by explicitly providing the parent
        window, but that isn't something hardware wallet prompts know.'''
        self.tl_windows.append(window)

    def pop_top_level_window(self, window):
        self.tl_windows.remove(window)

    def top_level_window(self, test_func=None):
        '''Do the right thing in the presence of tx dialog windows'''
        override = self.tl_windows[-1] if self.tl_windows else None
        if override and test_func and not test_func(override):
            override = None  # only override if ok for test_func
        return self.top_level_window_recurse(override, test_func)

    def diagnostic_name(self):
        return "%s/%s" % (PrintError.diagnostic_name(self),
                          self.wallet.basename() if self.wallet else "None")

    def is_hidden(self):
        return self.isMinimized() or self.isHidden()

    def show_or_hide(self):
        if self.is_hidden():
            self.bring_to_top()
        else:
            self.hide()

    def bring_to_top(self):
        self.show()
        self.raise_()

    def on_error(self, exc_info):
        if not isinstance(exc_info[1], UserCancelled):
            traceback.print_exception(*exc_info)
            self.show_error(str(exc_info[1]))

    def on_network(self, event, *args):
        if event == 'updated':
            self.need_update.set()
            self.gui_object.network_updated_signal_obj.network_updated_signal \
                .emit(event, args)
        elif event == 'new_transaction':
            self.tx_notifications.append(args[0])
            self.notify_transactions_signal.emit()
        elif event in ['status', 'banner', 'verified', 'fee']:
            # Handle in GUI thread
            self.network_signal.emit(event, args)
        else:
            self.print_error("unexpected network message:", event, args)

    def on_network_qt(self, event, args=None):
        if self.cleaned_up: return
        # Handle a network message in the GUI thread
        if event == 'status':
            self.update_status()
        elif event == 'banner':
            self.console.showMessage(args[0])
        elif event == 'verified':
            self.history_list.update_item(*args)
            self.slp_history_list.update_item_netupdate(*args)
        elif event == 'fee':
            if self.config.is_dynfee():
                self.fee_slider.update()
                self.do_update_fee()
        elif event == 'fee_histogram':
            if self.config.is_dynfee():
                self.fee_slider.update()
                self.do_update_fee()
            # todo: update only unconfirmed tx
            self.history_list.update()
        else:
            self.print_error("unexpected network_qt signal:", event, args)

    def fetch_alias(self):
        self.alias_info = None
        alias = self.config.get('alias')
        if alias:
            alias = str(alias)
            def f():
                self.alias_info = self.contacts.resolve_openalias(alias)
                self.alias_received_signal.emit()
            t = threading.Thread(target=f)
            t.setDaemon(True)
            t.start()

    def close_wallet(self):
        if self.wallet:
            self.print_error('close_wallet', self.wallet.storage.path)
        run_hook('close_wallet', self.wallet)

    @profiler
    def load_wallet(self, wallet):
        wallet.thread = TaskThread(self, self.on_error, name = self.wallet.diagnostic_name() + '/Wallet')
        self.wallet.ui_emit_validity_updated = self.slp_validity_signal.emit
        self.update_recently_visited(wallet.storage.path)
        # address used to create a dummy transaction and estimate transaction fee
        self.history_list.update()
        self.address_list.update()
        self.utxo_list.update()
        self.need_update.set()
        # update menus
        self.seed_menu.setEnabled(self.wallet.has_seed())
        self.update_lock_icon()
        self.update_buttons_on_seed()
        self.update_console()
        self.clear_receive_tab()
        self.request_list.update()

        if self.is_slp_wallet:
            self.slp_history_list.update()
            self.token_list.update()
            self.update_token_type_combo()

        self.tabs.show()
        self.init_geometry()
        if self.config.get('hide_gui') and self.gui_object.tray.isVisible():
            self.hide()
        else:
            self.show()
            if self._is_invalid_testnet_wallet():
                self.gui_object.daemon.stop_wallet(self.wallet.storage.path)
                self._rebuild_history_action.setEnabled(False)
                self._warn_if_invalid_testnet_wallet()
        self.watching_only_changed()
        self.history_updated_signal.emit() # inform things like address_dialog that there's a new history
        if self.is_slp_wallet:
            self.toggle_cashaddr(1, True)
            self.toggle_tab(self.slp_mgt_tab, 1)
            self.toggle_tab(self.slp_history_tab, 1)
        else:
            self.toggle_cashaddr(0, True)
        self.update_receive_address_widget()
        self.address_list.update()
        self.utxo_list.update()
        self.slp_mgt_tab.update()
        self.slp_history_tab.update()
        self.update_cashaddr_icon()
        run_hook('load_wallet', wallet, self)

    def init_geometry(self):
        winpos = self.wallet.storage.get("winpos-qt")
        try:
            screen = self.app.desktop().screenGeometry()
            assert screen.contains(QRect(*winpos))
            self.setGeometry(*winpos)
        except:
            self.print_error("using default geometry")
            self.setGeometry(100, 100, 840, 400)

    def watching_only_changed(self):
        name = "Electrum-ZSLP Testnet" if constants.net.TESTNET else "Electrum-ZSLP"
        title = '%s %s  -  %s' % (name, self.wallet.electrum_version,
                                        self.wallet.basename())
        extra = [self.wallet.storage.get('wallet_type', '?')]
        if self.wallet.is_watching_only():
            self.warn_if_watching_only()
            extra.append(_('watching only'))
        title += '  [%s]'% ', '.join(extra)
        self.setWindowTitle(title)
        self.password_menu.setEnabled(self.wallet.may_have_password())
        self.import_privkey_menu.setVisible(self.wallet.can_import_privkey())
        self.import_address_menu.setVisible(self.wallet.can_import_address())
        self.export_menu.setEnabled(self.wallet.can_export())

    def warn_if_watching_only(self):
        if self.wallet.is_watching_only():
            msg = ' '.join([
                _("This wallet is watching-only."),
                _("This means you will not be able to spend Zclassic coins with it."),
                _("Make sure you own the seed phrase or the private keys, before you request Zclassic coins to be sent to this wallet.")
            ])
            self.show_warning(msg, title=_('Information'))

    def _is_invalid_testnet_wallet(self):
        if not constants.net.TESTNET:
            return False
        is_old_bad = False
        xkey = ((hasattr(self.wallet, 'get_master_public_key') and self.wallet.get_master_public_key())
                or None)
        if xkey:
            from electrum_zclassic.bitcoin import deserialize_xpub, InvalidXKeyFormat
            try:
                xp = deserialize_xpub(xkey)
            except InvalidXKeyFormat:
                is_old_bad = True
        return is_old_bad

    def _warn_if_invalid_testnet_wallet(self):
        ''' This was added after the upgrade from the bad xpub testnet wallets
        to the good tpub testnet wallet format in version 3.3.6. See #1164.
        We warn users if they are using the bad wallet format and instruct
        them on how to upgrade their wallets.'''
        is_old_bad = self._is_invalid_testnet_wallet()
        if is_old_bad:
            msg = ' '.join([
                _("This testnet wallet has an invalid master key format."),
                _("(Old versions of Electron Cash before 3.3.6 produced invalid testnet wallets)."),
                '<br><br>',
                _("In order to use this wallet without errors with this version of EC, please <b>re-generate this wallet from seed</b>."),
                "<br><br><em><i>~SPV stopped~</i></em>"
            ])
            self.show_critical(msg, title=_('Invalid Master Key'), rich_text=True)
        return is_old_bad

    def open_wallet(self):
        try:
            wallet_folder = self.get_wallet_folder()
        except FileNotFoundError as e:
            self.show_error(str(e))
            return
        filename, __ = QFileDialog.getOpenFileName(self, "Select your wallet file", wallet_folder)
        if not filename:
            return
        self.gui_object.new_window(filename)


    def backup_wallet(self):
        path = self.wallet.storage.path
        wallet_folder = os.path.dirname(path)
        filename, __ = QFileDialog.getSaveFileName(self, _('Enter a filename for the copy of your wallet'), wallet_folder)
        if not filename:
            return
        new_path = os.path.join(wallet_folder, filename)
        if new_path != path:
            try:
                shutil.copy2(path, new_path)
                self.show_message(_("A copy of your wallet file was created in")+" '%s'" % str(new_path), title=_("Wallet backup created"))
            except BaseException as reason:
                self.show_critical(_("Electrum-Zclassic was unable to copy your wallet file to the specified location.") + "\n" + str(reason), title=_("Unable to create backup"))

    def update_recently_visited(self, filename):
        recent = self.config.get('recently_open', [])
        try:
            sorted(recent)
        except:
            recent = []
        if filename in recent:
            recent.remove(filename)
        recent.insert(0, filename)
        recent = recent[:5]
        self.config.set_key('recently_open', recent)
        self.recently_visited_menu.clear()
        for i, k in enumerate(sorted(recent)):
            b = os.path.basename(k)
            def loader(k):
                return lambda: self.gui_object.new_window(k)
            self.recently_visited_menu.addAction(b, loader(k)).setShortcut(QKeySequence("Ctrl+%d"%(i+1)))
        self.recently_visited_menu.setEnabled(len(recent))

    def get_wallet_folder(self):
        return os.path.dirname(os.path.abspath(self.config.get_wallet_path()))

    def new_wallet(self):
        try:
            wallet_folder = self.get_wallet_folder()
        except FileNotFoundError as e:
            self.show_error(str(e))
            return
        i = 1
        while True:
            filename = "wallet_%d" % i
            if filename in os.listdir(wallet_folder):
                i += 1
            else:
                break
        full_path = os.path.join(wallet_folder, filename)
        self.gui_object.start_new_window(full_path, None)

    def init_menubar(self):
        menubar = QMenuBar()

        file_menu = menubar.addMenu(_("&File"))
        self.recently_visited_menu = file_menu.addMenu(_("&Recently open"))
        file_menu.addAction(_("&Open"), self.open_wallet).setShortcut(QKeySequence.Open)
        file_menu.addAction(_("&New/Restore"), self.new_wallet).setShortcut(QKeySequence.New)
        file_menu.addAction(_("&Save Copy"), self.backup_wallet).setShortcut(QKeySequence.SaveAs)
        file_menu.addAction(_("Delete"), self.remove_wallet)
        file_menu.addSeparator()
        file_menu.addAction(_("&Quit"), self.close)

        wallet_menu = menubar.addMenu(_("&Wallet"))
        wallet_menu.addAction(_("&Information"), self.show_master_public_keys)
        wallet_menu.addSeparator()
        self.password_menu = wallet_menu.addAction(_("&Password"), self.change_password_dialog)
        self.seed_menu = wallet_menu.addAction(_("&Seed"), self.show_seed_dialog)
        self.private_keys_menu = wallet_menu.addMenu(_("&Private keys"))
        self.private_keys_menu.addAction(_("&Sweep"), self.sweep_key_dialog)
        self.import_privkey_menu = self.private_keys_menu.addAction(_("&Import"), self.do_import_privkey)
        self.export_menu = self.private_keys_menu.addAction(_("&Export"), self.export_privkeys_dialog)
        self.import_address_menu = wallet_menu.addAction(_("Import addresses"), self.import_addresses)
        wallet_menu.addSeparator()

        addresses_menu = wallet_menu.addMenu(_("&Addresses"))
        addresses_menu.addAction(_("&Filter"), lambda: self.address_list.toggle_toolbar(self.config))
        labels_menu = wallet_menu.addMenu(_("&Labels"))
        labels_menu.addAction(_("&Import"), self.do_import_labels)
        labels_menu.addAction(_("&Export"), self.do_export_labels)
        history_menu = wallet_menu.addMenu(_("&History"))
        history_menu.addAction(_("&Filter"), lambda: self.history_list.toggle_toolbar(self.config))
        history_menu.addAction(_("&Summary"), self.history_list.show_summary)
        history_menu.addAction(_("&Plot"), self.history_list.plot_history_dialog)
        history_menu.addAction(_("&Export"), self.history_list.export_history_dialog)
        contacts_menu = wallet_menu.addMenu(_("Contacts"))
        contacts_menu.addAction(_("&New"), self.new_contact_dialog)
        contacts_menu.addAction(_("Import"), lambda: self.contact_list.import_contacts())
        contacts_menu.addAction(_("Export"), lambda: self.contact_list.export_contacts())
        invoices_menu = wallet_menu.addMenu(_("Invoices"))
        invoices_menu.addAction(_("Import"), lambda: self.invoice_list.import_invoices())
        invoices_menu.addAction(_("Export"), lambda: self.invoice_list.export_invoices())

        wallet_menu.addSeparator()
        wallet_menu.addAction(_("Find"), self.toggle_search).setShortcut(QKeySequence("Ctrl+F"))

        def add_toggle_action(view_menu, tab):
            is_shown = self.tabs.indexOf(tab) > -1
            item_format = _("Hide {tab_description}") if is_shown else _("Show {tab_description}")
            item_name = item_format.format(tab_description=tab.tab_description)
            tab.menu_action = view_menu.addAction(item_name, lambda: self.toggle_tab(tab))

        view_menu = menubar.addMenu(_("&View"))
        add_toggle_action(view_menu, self.addresses_tab)
        add_toggle_action(view_menu, self.utxo_tab)
        add_toggle_action(view_menu, self.contacts_tab)
        add_toggle_action(view_menu, self.converter_tab)
        add_toggle_action(view_menu, self.console_tab)
        if self.is_slp_wallet:
            add_toggle_action(view_menu, self.slp_mgt_tab)
            add_toggle_action(view_menu, self.slp_history_tab)

        tools_menu = menubar.addMenu(_("&Tools"))

        # Settings / Preferences are all reserved keywords in macOS using this as work around
        tools_menu.addAction(_("Electrum-ZSLP Preferences") if sys.platform == 'darwin' else _("Preferences"), self.settings_dialog)
        tools_menu.addAction(_("&Network"), lambda: self.gui_object.show_network_dialog(self))
        tools_menu.addAction(_("&Plugins"), self.plugins_dialog)
        tools_menu.addSeparator()
        tools_menu.addAction(_("&Sign/verify message"), self.sign_verify_message)
        tools_menu.addAction(_("&Encrypt/decrypt message"), self.encrypt_message)
        tools_menu.addSeparator()
        # tools_menu.addAction(_("Upload a file using BFP"), lambda: BitcoinFilesUploadDialog(self, None, True, "Upload a File Using BFP"))
        # tools_menu.addAction(_("Download a file using BFP"), lambda: BfpDownloadFileDialog(self,))
        # tools_menu.addSeparator()

        paytomany_menu = tools_menu.addAction(_("&Pay to many"), self.paytomany)

        raw_transaction_menu = tools_menu.addMenu(_("&Load transaction"))
        raw_transaction_menu.addAction(_("&From file"), self.do_process_from_file)
        raw_transaction_menu.addAction(_("&From text"), self.do_process_from_text)
        raw_transaction_menu.addAction(_("&From the blockchain"), self.do_process_from_txid)
        raw_transaction_menu.addAction(_("&From QR code"), self.read_tx_from_qrcode)
        self.raw_transaction_menu = raw_transaction_menu
        run_hook('init_menubar_tools', self, tools_menu)

        help_menu = menubar.addMenu(_("&Help"))
        help_menu.addAction(_("&About"), self.show_about)
        #help_menu.addAction(_("&Official website"), lambda: webbrowser.open("https://github.com/ZclassicCommunity/electrum-zclassic"))
        help_menu.addSeparator()
        #help_menu.addAction(_("&Documentation"), lambda: webbrowser.open("http://github.com/ZclassicCommunity/electrum-zclassic")).setShortcut(QKeySequence.HelpContents)
        #self._auto_crash_reports = QAction(_("&Automated Crash Reports"), self, checkable=True)
        #self._auto_crash_reports.setChecked(self.config.get("show_crash_reporter", default=False))
        #self._auto_crash_reports.triggered.connect(self.auto_crash_reports)
        #help_menu.addAction(self._auto_crash_reports)
        help_menu.addAction(_("&Report Bug"), self.show_report_bug)
        help_menu.addSeparator()
        help_menu.addAction(_("&Donate to server"), self.donate_to_server)

        self.setMenuBar(menubar)

    def auto_crash_reports(self, state):
        self.config.set_key("show_crash_reporter", state)
        self.setup_exception_hook()

    def donate_to_server(self):
        d = self.network.get_donation_address()
        if d:
            host = self.network.get_parameters()[0]
            self.pay_to_URI('zclassic:%s?message=donation for %s'%(d, host))
        else:
            self.show_error(_('No donation address for this server'))

    def show_about(self):
        QMessageBox.about(self, "Electrum-ZSLP",
            _("Version")+" %s" % (self.wallet.electrum_version) + "\n\n" +
                _("Electrum-Zclassic focus is speed, with low resource usage and simplifying ZClassic. You do not need to perform regular backups, because your wallet can be recovered from a secret phrase that you can memorize or write on paper. Startup times are instant because it operates in conjunction with high-performance servers that handle the most complicated parts of the ZClassic system."  + "\n\n" +
                _("Uses icons from the Icons8 icon pack (icons8.com).")))

    def show_report_bug(self):
        msg = ' '.join([
            _("Please report any bugs as issues on github:<br/>"),
            "<a href=\"https://github.com/ZclassicCommunity/electrum-zclassic/issues\">https://github.com/ZclassicCommunity/electrum-zclassic/issues</a><br/><br/>",
            _("Before reporting a bug, upgrade to the most recent version of Electrum-Zclassic (latest release or git HEAD), and include the version number in your report."),
            _("Try to explain not only what the bug is, but how it occurs.")
         ])
        self.show_message(msg, title="Electrum-ZSLP - " + _("Reporting Bugs"))

    def notify_transactions(self):
        if not self.network or not self.network.is_connected():
            return
        self.print_error("Notifying GUI")
        if len(self.tx_notifications) > 0:
            # Combine the transactions if there are at least three
            num_txns = len(self.tx_notifications)
            if num_txns >= 3:
                total_amount = 0
                tokens_included = set()
                for tx in self.tx_notifications:
                    is_relevant, is_mine, v, fee = self.wallet.get_wallet_delta(tx)
                    if v > 0:
                        total_amount += v
                    if self.is_slp_wallet:
                        try:
                            tti = self.wallet.tx_tokinfo[tx.txid()]
                            tokens_included.add(self.wallet.token_types.get(tti['token_id'],{}).get('name','unknown'))
                        except KeyError:
                            pass
                if tokens_included:
                    tokstring = _('. Tokens included: ') + ', '.join(sorted(tokens_included))
                else:
                    tokstring = ''
                self.notify(_("{} new transactions received: Total amount received in the new transactions {}{}")
                            .format(num_txns, self.format_amount_and_units(total_amount),tokstring))
                self.tx_notifications = []
            else:
                for tx in self.tx_notifications:
                    if tx:
                        self.tx_notifications.remove(tx)
                        is_relevant, is_mine, v, fee = self.wallet.get_wallet_delta(tx)
                        if self.config.get('enable_slp'):
                            try:
                                tti = self.wallet.tx_tokinfo[tx.txid()]
                                tokstring = _(". Token included: ") + self.wallet.token_types.get(tti['token_id'],{}).get('name','unknown')
                            except KeyError:
                                tokstring = ""
                        else:
                            tokstring = ""
                        if v > 0:
                            self.notify(_("New transaction received: {}{}").format(self.format_amount_and_units(v), tokstring))

    def notify(self, message):
        if self.tray:
            try:
                # this requires Qt 5.9
                self.tray.showMessage("Electrum-ZSLP", message, QIcon(":icons/electrum_dark_icon"), 20000)
            except TypeError:
                self.tray.showMessage("Electrum-ZSLP", message, QSystemTrayIcon.Information, 20000)



    # custom wrappers for getOpenFileName and getSaveFileName, that remember the path selected by the user
    def getOpenFileName(self, title, filter = ""):
        directory = self.config.get('io_dir', os.path.expanduser('~'))
        fileName, __ = QFileDialog.getOpenFileName(self, title, directory, filter)
        if fileName and directory != os.path.dirname(fileName):
            self.config.set_key('io_dir', os.path.dirname(fileName), True)
        return fileName

    def getSaveFileName(self, title, filename, filter = ""):
        directory = self.config.get('io_dir', os.path.expanduser('~'))
        path = os.path.join( directory, filename )
        fileName, __ = QFileDialog.getSaveFileName(self, title, path, filter)
        if fileName and directory != os.path.dirname(fileName):
            self.config.set_key('io_dir', os.path.dirname(fileName), True)
        return fileName

    def connect_slots(self, sender):
        sender.timer_signal.connect(self.timer_actions)

    def timer_actions(self):
        # Note this runs in the GUI thread
        if self.need_update.is_set():
            self.need_update.clear()
            self.update_wallet()
        # resolve aliases
        # FIXME this is a blocking network call that has a timeout of 5 sec
        self.payto_e.resolve()
        # update fee
        if self.require_fee_update:
            self.do_update_fee()
            self.require_fee_update = False

    def format_amount(self, x, is_diff=False, whitespaces=False):
        return format_satoshis(x, is_diff, self.num_zeros, self.decimal_point, whitespaces)

    def format_amount_and_units(self, amount):
        text = self.format_amount(amount) + ' '+ self.base_unit()
        x = self.fx.format_amount_and_units(amount) if self.fx else None
        if text and x:
            text += ' (%s)'%x
        return text

    def format_fee_rate(self, fee_rate):
        return '%s sat/kB' % round(fee_rate)

    def get_decimal_point(self):
        return self.decimal_point

    def base_unit(self):
        assert self.decimal_point in [2, 5, 8]
        if self.decimal_point == 2:
            return 'uZCL'
        if self.decimal_point == 5:
            return 'mZCL'
        if self.decimal_point == 8:
            return 'ZCL'
        raise Exception('Unknown base unit')

    def connect_fields(self, window, btc_e, fiat_e, fee_e):

        def edit_changed(edit):
            if edit.follows:
                return
            edit.setStyleSheet(ColorScheme.DEFAULT.as_stylesheet())
            fiat_e.is_last_edited = (edit == fiat_e)
            amount = edit.get_amount()
            rate = self.fx.exchange_rate() if self.fx else Decimal('NaN')
            if rate.is_nan() or amount is None:
                if edit is fiat_e:
                    btc_e.setText("")
                    if fee_e:
                        fee_e.setText("")
                else:
                    fiat_e.setText("")
            else:
                if edit is fiat_e:
                    btc_e.follows = True
                    btc_e.setAmount(int(amount / Decimal(rate) * COIN))
                    btc_e.setStyleSheet(ColorScheme.BLUE.as_stylesheet())
                    btc_e.follows = False
                    if fee_e:
                        window.update_fee()
                else:
                    fiat_e.follows = True
                    fiat_e.setText(self.fx.ccy_amount_str(
                        amount * Decimal(rate) / COIN, False))
                    fiat_e.setStyleSheet(ColorScheme.BLUE.as_stylesheet())
                    fiat_e.follows = False

        btc_e.follows = False
        fiat_e.follows = False
        fiat_e.textChanged.connect(partial(edit_changed, fiat_e))
        btc_e.textChanged.connect(partial(edit_changed, btc_e))
        fiat_e.is_last_edited = False

    def update_status(self):
        if not self.wallet:
            return

        if self.network is None or not self.network.is_running():
            text = _("Offline")
            icon = QIcon(":icons/status_disconnected.png")

        elif self.network.is_connected():
            server_height = self.network.get_server_height()
            server_lag = self.network.get_local_height() - server_height
            num_chains = len(self.network.get_blockchains())
            # Server height can be 0 after switching to a new server
            # until we get a headers subscription request response.
            # Display the synchronizing message in that case.
            if not self.wallet.up_to_date or server_height == 0:
                text = _("Synchronizing...")
                icon = QIcon(":icons/status_waiting.png")
            elif server_lag > 1:
                text = _("Server is lagging ({} blocks)").format(server_lag)
                icon = QIcon(":icons/status_lagging.png") if num_chains <= 1 else QIcon(":icons/status_lagging_fork.png")
            else:
                text = ""
                if not self.is_slp_wallet:
                    text += "Tokens Disabled - "
                else:
                    token_id = self.slp_token_id
                    try:
                        d = self.wallet.token_types[token_id]
                    except (AttributeError, KeyError):
                        pass
                    else:
                        bal = format_satoshis_nofloat(self.wallet.get_slp_token_balance(token_id, { 'user_config': { 'confirmed_only': False } })[0],
                                                    decimal_point=d['decimals'],)
                        text += "%s Token Balance: %s; "%(d['name'], bal)
                c, u, x = self.wallet.get_balance()
                text +=  _("Zclassic Balance" ) + ": %s "%(self.format_amount_and_units(c))
                if u:
                    text +=  " [%s unconfirmed]"%(self.format_amount(u, True).strip())
                if x:
                    text +=  " [%s unmatured]"%(self.format_amount(x, True).strip())

                # append fiat balance and price
                if self.fx.is_enabled():
                    text += self.fx.get_fiat_status_text(c + u + x,
                        self.base_unit(), self.get_decimal_point()) or ''
                if not self.network.proxy:
                    icon = QIcon(":icons/status_connected.png") if num_chains <= 1 else QIcon(":icons/status_connected_fork.png")
                else:
                    icon = QIcon(":icons/status_connected_proxy.png") if num_chains <= 1 else QIcon(":icons/status_connected_proxy_fork.png")
        else:
            text = _("Not connected")
            icon = QIcon(":icons/status_disconnected.png")

        self.tray.setToolTip("%s (%s)" % (text, self.wallet.basename()))
        self.balance_label.setText(text)
        addr_format = self.config.get('addr_format', 0)
        self.setAddrFormatText(addr_format)
        self.status_button.setIcon( icon )


    def update_wallet(self):
        self.update_status()
        if self.wallet.up_to_date or not self.network or not self.network.is_connected():
            self.update_tabs()

    def update_tabs(self):
        self.history_list.update()
        self.request_list.update()
        self.address_list.update()
        self.utxo_list.update()
        self.contact_list.update()
        self.invoice_list.update()
        self.update_completions()
        if self.is_slp_wallet:
            self.slp_history_list.update()
            self.token_list.update()

    def create_history_tab(self):
        from .history_list import HistoryList
        self.history_list = l = HistoryList(self)
        l.searchable_list = l
        return l

    def create_slp_history_tab(self):
        from .slp_history_list import HistoryList
        self.slp_history_list = l = HistoryList(self)
        return self.create_list_tab(l)

    def show_address(self, addr, *, parent=None):
        parent = parent or self.top_level_window()
        from . import address_dialog
        d = address_dialog.AddressDialog(self, addr, windowParent=parent)
        d.exec_()

    def show_transaction(self, tx, tx_desc = None):
        '''tx_desc is set only for txs created in the Send tab'''
        d = show_transaction(tx, self, tx_desc)
        self._tx_dialogs.add(d)

    def addr_toggle_slp(self, force_slp=False):

        def present_slp():
            self.toggle_cashaddr(1, True)
            self.receive_slp_token_type_label.setDisabled(False)
            self.receive_slp_amount_e.setDisabled(False)
            self.receive_slp_amount_label.setDisabled(False)

        if force_slp:
            present_slp()
            return

        if Address.FMT_UI == Address.FMT_SLPADDR:
            self.toggle_cashaddr(0, True)
            self.receive_token_type_combo.setCurrentIndex(0)
        else:
            present_slp()

    def on_toggled_opreturn(self, b):
        ''' toggles opreturn-related widgets for both the receive and send
        tabs'''
        b = bool(b)
        self.config.set_key('enable_opreturn', b)
        # send tab
        if not b:
            self.message_opreturn_e.setText("")
            self.op_return_toolong = False
        for x in self.send_tab_opreturn_widgets:
            x.setVisible(b)
        # receive tab
        for x in self.receive_tab_opreturn_widgets:
            x.setVisible(b)

    def create_receive_tab(self):
        # A 4-column grid layout.  All the stretch is in the last column.
        # The exchange rate plugin adds a fiat widget in column 2
        self.receive_grid = grid = QGridLayout()
        grid.setSpacing(8)
        grid.setColumnStretch(3, 1)

        self.receive_address = None
        self.receive_address_e = ButtonsLineEdit()
        self.receive_address_e.addCopyButton(self.app)
        self.receive_address_e.setReadOnly(True)
        msg = _('Zclassic address where the payment should be received. Note that each payment request uses a different Zclassic address.')
        label = HelpLabel(_('&Receiving address'), msg)
        label.setBuddy(self.receive_address_e)
        self.receive_address_e.textChanged.connect(self.update_receive_qr)
        self.cashaddr_toggled_signal.connect(self.update_receive_address_widget)
        grid.addWidget(label, 0, 0)
        grid.addWidget(self.receive_address_e, 0, 1, 1, -1)

        if self.is_slp_wallet:
            self.show_slp_addr_btn = QPushButton(_('Show Token Address'))
            self.show_slp_addr_btn.clicked.connect(self.addr_toggle_slp)
            grid.addWidget(self.show_slp_addr_btn, 1, 1)

        self.receive_message_e = QLineEdit()
        label = QLabel(_('&Description'))
        label.setBuddy(self.receive_message_e)
        grid.addWidget(label, 2, 0)
        grid.addWidget(self.receive_message_e, 2, 1, 1, -1)
        self.receive_message_e.textChanged.connect(self.update_receive_qr)

        # OP_RETURN requests
        self.receive_opreturn_e = QLineEdit()
        msg = _("You may optionally append an OP_RETURN message to the payment URI and/or QR you generate.\n\nNote: Not all wallets yet support OP_RETURN parameters, so make sure the other party's wallet supports OP_RETURN URIs.")
        self.receive_opreturn_label = label = HelpLabel(_('&OP_RETURN'), msg)
        label.setBuddy(self.receive_opreturn_e)
        self.receive_opreturn_rawhex_cb = QCheckBox(_('Raw &hex script'))
        self.receive_opreturn_rawhex_cb.setToolTip(_('If unchecked, the textbox contents are UTF8-encoded into a single-push script: <tt>OP_RETURN PUSH &lt;text&gt;</tt>. If checked, the text contents will be interpreted as a raw hexadecimal script to be appended after the OP_RETURN opcode: <tt>OP_RETURN &lt;script&gt;</tt>.'))
        grid.addWidget(label, 3, 0)
        grid.addWidget(self.receive_opreturn_e, 3, 1, 1, 3)
        grid.addWidget(self.receive_opreturn_rawhex_cb, 3, 4, Qt.AlignLeft)
        self.receive_opreturn_e.textChanged.connect(self.update_receive_qr)
        self.receive_opreturn_rawhex_cb.clicked.connect(self.update_receive_qr)
        self.receive_tab_opreturn_widgets = [
            self.receive_opreturn_e,
            self.receive_opreturn_rawhex_cb,
            self.receive_opreturn_label,
        ]

        msg = _('Select the ZSLP token to Request.')
        self.receive_token_type_combo = QComboBox()
        if ColorScheme.dark_scheme and sys.platform == 'darwin':
            # Hack/Workaround to QDarkStyle bugs; see https://github.com/ColinDuquesnoy/QDarkStyleSheet/issues/169#issuecomment-494647801
            self.receive_token_type_combo.setItemDelegate(QStyledItemDelegate(self.receive_token_type_combo))
        self.receive_token_type_combo.setFixedWidth(200)
        self.receive_token_type_combo.currentIndexChanged.connect(self.on_slptok_receive)
        #self.receive_token_type_combo.currentIndexChanged.connect(self.update_buttons_on_seed)  # update 'CoinText' button, etc
        self.receive_slp_token_type_label = HelpLabel(_('Token Type'), msg)
        grid.addWidget(self.receive_slp_token_type_label, 4, 0)
        grid.addWidget(self.receive_token_type_combo, 4, 1)

        self.receive_slp_amount_e = SLPAmountEdit('tokens', 0)
        self.receive_slp_amount_e.setFixedWidth(self.receive_token_type_combo.width())
        self.receive_slp_amount_label = QLabel(_('Req. token amount'))
        grid.addWidget(self.receive_slp_amount_label, 5, 0)
        grid.addWidget(self.receive_slp_amount_e, 5, 1)
        self.receive_slp_amount_e.textChanged.connect(self.update_receive_qr)

        self.receive_amount_e = BTCAmountEdit(self.get_decimal_point)
        self.receive_amount_e.setFixedWidth(self.receive_token_type_combo.width())
        self.receive_amount_label = QLabel(_('Requested &amount'))
        self.receive_amount_label.setBuddy(self.receive_amount_e)
        grid.addWidget(self.receive_amount_label, 6, 0)
        grid.addWidget(self.receive_amount_e, 6, 1)
        self.receive_amount_e.textChanged.connect(self.update_receive_qr)

        if Address.FMT_UI != Address.FMT_SLPADDR:
            self.receive_token_type_combo.setDisabled(True)
            self.receive_slp_token_type_label.setDisabled(True)
            self.receive_slp_amount_e.setDisabled(True)
            self.receive_slp_amount_label.setDisabled(True)
        else:
            self.receive_token_type_combo.setDisabled(False)
            self.receive_slp_token_type_label.setDisabled(False)
            self.receive_slp_amount_e.setDisabled(False)
            self.receive_slp_amount_label.setDisabled(False)

        self.fiat_receive_e = AmountEdit(self.fx.get_currency if self.fx else '')
        if not self.fx or not self.fx.is_enabled():
            self.fiat_receive_e.setVisible(False)
        grid.addWidget(self.fiat_receive_e, 6, 2, Qt.AlignLeft)
        self.connect_fields(self, self.receive_amount_e, self.fiat_receive_e, None)

        self.expires_combo = QComboBox()
        self.expires_combo.addItems([i[0] for i in expiration_values])
        self.expires_combo.setCurrentIndex(3)
        self.expires_combo.setFixedWidth(self.receive_amount_e.width())
        msg = ' '.join([
            _('Expiration date of your request.'),
            _('This information is seen by the recipient if you send them a signed payment request.'),
            _('Expired requests have to be deleted manually from your list, in order to free the corresponding Zclassic addresses.'),
            _('The Zclassic address never expires and will always be part of this electrum-zclassic wallet.'),
        ])
        label = HelpLabel(_('Request &expires'), msg)
        label.setBuddy(self.expires_combo)
        grid.addWidget(label, 7, 0)
        grid.addWidget(self.expires_combo, 7, 1)
        self.expires_label = QLineEdit('')
        self.expires_label.setReadOnly(1)
        self.expires_label.hide()
        grid.addWidget(self.expires_label, 7, 1)

        self.save_request_button = QPushButton(_('&Save'))
        self.save_request_button.clicked.connect(self.save_payment_request)

        self.new_request_button = QPushButton(_('&Clear'))
        self.new_request_button.clicked.connect(self.new_payment_request)

        weakSelf = Weak.ref(self)

        class MyQRCodeWidget(QRCodeWidget):
            def mouseReleaseEvent(self, e):
                ''' to make the QRWidget clickable '''
                weakSelf() and weakSelf().toggle_qr_window()

        self.receive_qr = MyQRCodeWidget(fixedSize=200)
        self.receive_qr.setCursor(QCursor(Qt.PointingHandCursor))

        self.receive_buttons = buttons = QHBoxLayout()
        buttons.addWidget(self.save_request_button)
        buttons.addWidget(self.new_request_button)
        buttons.addStretch(1)
        grid.addLayout(buttons, 8, 1, 1, -1)

        self.receive_requests_label = QLabel(_('Re&quests'))

        from .request_list import RequestList
        self.request_list = RequestList(self)
        self.request_list.chkVisible()

        self.receive_requests_label.setBuddy(self.request_list)

        # layout
        vbox_g = QVBoxLayout()
        vbox_g.addLayout(grid)
        vbox_g.addStretch()

        hbox = QHBoxLayout()
        hbox.addLayout(vbox_g)
        vbox2 = QVBoxLayout()
        vbox2.setContentsMargins(0,0,0,0)
        vbox2.setSpacing(4)
        vbox2.addWidget(self.receive_qr, Qt.AlignHCenter|Qt.AlignTop)
        self.receive_qr.setToolTip(_('Receive request QR code (click for details)'))
        but = uribut = QPushButton(_('Copy &URI'))
        def on_copy_uri():
            if self.receive_qr.data:
                uri = str(self.receive_qr.data)
                self.copy_to_clipboard(uri, _('Receive request URI copied to clipboard'), uribut)
        but.clicked.connect(on_copy_uri)
        but.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        but.setToolTip(_('Click to copy the receive request URI to the clipboard'))
        vbox2.addWidget(but)
        vbox2.setAlignment(but, Qt.AlignHCenter|Qt.AlignVCenter)

        hbox.addLayout(vbox2)

        class ReceiveTab(QWidget):
            def showEvent(self, e):
                super().showEvent(e)
                if e.isAccepted():
                    slf = weakSelf()
                    if slf:
                        slf.check_and_reset_receive_address_if_needed()
                if self.main_window.is_slp_wallet:
                    c, u, x = self.main_window.wallet.get_balance()
                    bal = c + u - self.main_window.wallet.get_slp_locked_balance()
                    if bal < 1000:
#                       if not self.low_balance_warning_shown:
#                           self.main_window.show_warning("Low BCH balance.\n\nCreating and sending SLP tokens requires Bitcoin Cash to cover transaction fees.  We recommend a minimum of 0.0001 BCH to get started.\n\nSend BCH to the address displayed in the 'Receive' tab.")
                        self.main_window.toggle_cashaddr(0, True)
                        self.low_balance_warning_shown = False
                    else:
                        self.main_window.toggle_cashaddr(1, True)
                    if Address.FMT_UI == Address.FMT_SLPADDR:
                        self.main_window.show_slp_addr_btn.setText("Show Zclassic Address")
                    else:
                        self.main_window.show_slp_addr_btn.setText("Show Token Address")
                else:
                    self.main_window.toggle_cashaddr(0, True)


        w = ReceiveTab()
        w.low_balance_warning_shown = False
        w.main_window = self
        w.searchable_list = self.request_list
        vbox = QVBoxLayout(w)
        vbox.addLayout(hbox)
        vbox.addStretch(1)
        vbox.addWidget(self.receive_requests_label)
        vbox.addWidget(self.request_list)
        vbox.setStretchFactor(self.request_list, 1000)

        return w


    def delete_payment_request(self, addr):
        self.wallet.remove_payment_request(addr, self.config)
        self.request_list.update()
        self.address_list.update()
        self.clear_receive_tab()

    def get_request_URI(self, addr):
        req = self.wallet.receive_requests[addr]
        message = self.wallet.labels.get(addr.to_storage_string(), '')
        amount = req['amount']
        URI = web.create_URI(addr, amount, message)
        if req.get('time'):
            URI += "&time=%d"%req.get('time')
        if req.get('exp'):
            URI += "&exp=%d"%req.get('exp')
        if req.get('name') and req.get('sig'):
            sig = bfh(req.get('sig'))
            sig = bitcoin.base_encode(sig, base=58)
            URI += "&name=" + req['name'] + "&sig="+sig
        return str(URI)


    def sign_payment_request(self, addr):
        alias = self.config.get('alias')
        alias_privkey = None
        if alias and self.alias_info:
            alias_addr, alias_name, validated = self.alias_info
            if alias_addr:
                if self.wallet.is_mine(alias_addr):
                    msg = _('This payment request will be signed.') + '\n' + _('Please enter your password')
                    password = None
                    if self.wallet.has_keystore_encryption():
                        password = self.password_dialog(msg)
                        if not password:
                            return
                    try:
                        self.wallet.sign_payment_request(addr, alias, alias_addr, password)
                    except Exception as e:
                        self.show_error(str(e))
                        return
                else:
                    return

    def save_payment_request(self):
        addr = Address.from_string(self.receive_address_e.text())
        amount = self.receive_amount_e.get_amount()
        message = self.receive_message_e.text()
        if not message and not amount:
            self.show_error(_('No message or amount'))
            return False
        i = self.expires_combo.currentIndex()
        expiration = list(map(lambda x: x[1], expiration_values))[i]
        req = self.wallet.make_payment_request(addr, amount, message, expiration)
        try:
            self.wallet.add_payment_request(req, self.config)
        except Exception as e:
            traceback.print_exc(file=sys.stderr)
            self.show_error(_('Error adding payment request') + ':\n' + str(e))
        else:
            self.sign_payment_request(addr)
            self.save_request_button.setEnabled(False)
        finally:
            self.request_list.update()
            self.address_list.update()

    def view_and_paste(self, title, msg, data):
        dialog = WindowModalDialog(self, title)
        vbox = QVBoxLayout()
        label = QLabel(msg)
        label.setWordWrap(True)
        vbox.addWidget(label)
        pr_e = ShowQRTextEdit(text=data)
        vbox.addWidget(pr_e)
        vbox.addLayout(Buttons(CopyCloseButton(pr_e.text, self.app, dialog)))
        dialog.setLayout(vbox)
        dialog.exec_()

    def export_payment_request(self, addr):
        r = self.wallet.receive_requests[addr]
        pr = paymentrequest.serialize_request(r).SerializeToString()
        name = r['id'] + '.bip70'
        fileName = self.getSaveFileName(_("Select where to save your payment request"), name, "*.bip70")
        if fileName:
            with open(fileName, "wb+") as f:
                f.write(util.to_bytes(pr))
            self.show_message(_("Request saved successfully"))
            self.saved = True

    def new_payment_request(self):
        addr = self.wallet.get_unused_address()
        if addr is None:
            if not self.wallet.is_deterministic():
                msg = [
                    _('No more addresses in your wallet.'),
                    _('You are using a non-deterministic wallet, which cannot create new addresses.'),
                    _('If you want to create new addresses, use a deterministic wallet instead.')
                   ]
                self.show_message(' '.join(msg))
                return
            if not self.question(_("Warning: The next address will not be recovered automatically if you restore your wallet from seed; you may need to add it manually.\n\nThis occurs because you have too many unused addresses in your wallet. To avoid this situation, use the existing addresses first.\n\nCreate anyway?")):
                return
            addr = self.wallet.create_new_address(False)
        self.set_receive_address(addr)
        self.expires_label.hide()
        self.expires_combo.show()
        self.new_request_button.setEnabled(False)
        self.receive_message_e.setFocus(1)

    def set_receive_address(self, addr):
        self.receive_address = addr
        self.receive_message_e.setText('')
        self.receive_amount_e.setAmount(None)
        self.update_receive_address_widget()

    def update_receive_address_widget(self):
        text = ''
        if self.receive_address:
            text = self.receive_address.to_full_ui_string()
        self.receive_address_e.setText(text)

    @rate_limited(0.250, ts_after=True)  # this function potentially re-computes the QR widget, so it's rate limited to once every 250ms
    def check_and_reset_receive_address_if_needed(self):
        ''' Check to make sure the receive tab is kosher and doesn't contain
        an already-used address. This should be called from the showEvent
        for the tab. '''
        if not self.wallet.use_change or self.cleaned_up:
            # if they don't care about change addresses, they are ok
            # with re-using addresses, so skip this check.
            return
        # ok, they care about anonymity, so make sure the receive address
        # is always an unused address.
        if (not self.receive_address  # this should always be defined but check anyway
            or self.receive_address in self.wallet.frozen_addresses  # make sure it's not frozen
            or (self.wallet.get_address_history(self.receive_address)   # make a new address if it has a history
                and not self.wallet.get_payment_request(self.receive_address, self.config))):  # and if they aren't actively editing one in the request_list widget
            addr = self.wallet.get_unused_address(frozen_ok=False)  # try unused, not frozen
            if addr is None:
                if self.wallet.is_deterministic():
                    # creae a new one if deterministic
                    addr = self.wallet.create_new_address(False)
                else:
                    # otherwise give up and just re-use one.
                    addr = self.wallet.get_receiving_address()
            self.receive_address = addr
            self.update_receive_address_widget()

    def clear_receive_tab(self):
        self.expires_label.hide()
        self.expires_combo.show()
        self.request_list.setCurrentItem(None)
        self.set_receive_address(self.wallet.get_receiving_address(frozen_ok=False))

    def toggle_qr_window(self):
        from . import qrwindow
        if not self.qr_window:
            self.qr_window = qrwindow.QR_Window(self)
            self.qr_window.setVisible(True)
            self.qr_window_geometry = self.qr_window.geometry()
        else:
            if not self.qr_window.isVisible():
                self.qr_window.setVisible(True)
                self.qr_window.setGeometry(self.qr_window_geometry)
            else:
                self.qr_window_geometry = self.qr_window.geometry()
                self.qr_window.setVisible(False)
        self.update_receive_qr()

    def show_send_tab(self):
        self.tabs.setCurrentIndex(self.tabs.indexOf(self.send_tab))

    def show_receive_tab(self):
        self.tabs.setCurrentIndex(self.tabs.indexOf(self.receive_tab))

    def receive_at(self, addr):
        if not bitcoin.is_address(addr):
            return
        self.show_receive_tab()
        self.receive_address_e.setText(addr)
        self.new_request_button.setEnabled(True)

    def update_receive_qr(self):
        amount = self.receive_amount_e.get_amount()
        message = self.receive_message_e.text()
        self.save_request_button.setEnabled((amount is not None) or (message != ""))
        uri = web.create_URI(self.receive_address, amount, message)
        self.receive_qr.setData(uri)
        if self.qr_window and self.qr_window.isVisible():
            self.qr_window.set_content(self.receive_address_e.text(), amount, message, uri)

    def set_feerounding_text(self, num_satoshis_added):
        self.feerounding_text = (_('Additional {} satoshis are going to be added.')
                                 .format(num_satoshis_added))

    def on_slptok(self):
        self.slp_token_id = self.token_type_combo.currentData()
        self.payto_e.check_text()
        self.slp_amount_e.setText("")
        if self.slp_token_id is None:
            self.amount_e.setDisabled(False)
            self.amount_label.setDisabled(False)
            self.max_button.setDisabled(False)
            self.fiat_send_e.setDisabled(False)
            self.slp_extra_zcl_cb.setHidden(True)
            self.slp_amount_e.setDisabled(True)
            self.slp_max_button.setDisabled(True)
            self.slp_amount_label.setDisabled(True)
            self.message_opreturn_e.setEnabled(True)
            self.opreturn_rawhex_cb.setEnabled(True)
            self.opreturn_label.setEnabled(True)
        else:
            self.slp_extra_zcl_cb.setHidden(False)
            self.slp_extra_zcl_cb.setChecked(False)
            self.slp_extra_zcl_cb.clicked.emit()
            self.slp_amount_e.setDisabled(False)
            self.slp_max_button.setDisabled(False)
            self.slp_amount_label.setDisabled(False)
            tok = self.wallet.token_types[self.slp_token_id]
            self.slp_amount_e.set_token(tok['name'][:6],tok['decimals'])
            self.message_opreturn_e.setEnabled(False)
            self.message_opreturn_e.setText('')
            self.opreturn_rawhex_cb.setEnabled(False)
            self.opreturn_label.setEnabled(False)
        self.update_status()
        self.do_update_fee()

    def on_slptok_receive(self):
        self.receive_slp_amount_e.setText("")
        self.receive_amount_e.setText("")
        slp_token_id = self.receive_token_type_combo.currentData()
        self.update_receive_qr()
        if slp_token_id is None:
            self.receive_slp_amount_e.setDisabled(True)
            self.receive_slp_amount_label.setDisabled(True)
            self.receive_amount_e.setDisabled(False)
            self.receive_amount_label.setDisabled(False)
            self.fiat_receive_e.setDisabled(False)
        else:
            self.addr_toggle_slp(True)
            self.receive_slp_amount_e.setDisabled(False)
            self.receive_slp_amount_label.setDisabled(False)
            self.receive_amount_e.setDisabled(True)
            self.receive_amount_label.setDisabled(True)
            self.fiat_receive_e.setDisabled(True)
            tok = self.wallet.token_types[slp_token_id]
            self.receive_slp_amount_e.set_token(tok['name'][:6],tok['decimals'])

    def on_slp_extra_zcl(self):
        if self.slp_extra_zcl_cb.isChecked():
            self.amount_e.setDisabled(False)
            self.amount_label.setDisabled(False)
            self.max_button.setDisabled(False)
            self.fiat_send_e.setDisabled(False)
        else:
            self.amount_e.setText('')
            self.max_button.setChecked(False)
            self.amount_e.setDisabled(True)
            self.amount_label.setDisabled(True)
            self.max_button.setDisabled(True)
            self.fiat_send_e.setDisabled(True)

    def create_send_tab(self):
        # A 4-column grid layout.  All the stretch is in the last column.
        # The exchange rate plugin adds a fiat widget in column 2
        self.send_grid = grid = QGridLayout()
        grid.setSpacing(8)
        grid.setColumnStretch(3, 1)

        from .paytoedit import PayToEdit
        self.amount_e = BTCAmountEdit(self.get_decimal_point)
        self.payto_e = PayToEdit(self)
        self.payto_e.parent = self

        self.slp_send_tab_widgets = []
        if self.is_slp_wallet:
            self.slp_amount_e = SLPAmountEdit('tokens', 0)
            self.token_type_combo = QComboBox()
            if ColorScheme.dark_scheme and sys.platform == 'darwin':
                # Hack/Workaround to QDarkStyle bugs; see https://github.com/ColinDuquesnoy/QDarkStyleSheet/issues/169#issuecomment-494647801
                self.token_type_combo.setItemDelegate(QStyledItemDelegate(self.token_type_combo))
            self.token_type_combo.setFixedWidth(200)
            self.token_type_combo.currentIndexChanged.connect(self.on_slptok)
            self.token_type_combo.currentIndexChanged.connect(self.update_buttons_on_seed)  # update 'CoinText' button, etc
            self.slp_send_tab_widgets += [
                self.slp_amount_e, self.token_type_combo
            ]

        msg = _('Recipient of the funds.') + '\n\n'\
              + _('You may enter a Zclassic address, a label from your list of contacts (a list of completions will be proposed), or an alias (email-like address that forwards to a Zclassic address)')
        self.payto_label = payto_label = HelpLabel(_('Pay &to'), msg)
        payto_label.setBuddy(self.payto_e)
        qmark_help_but = HelpButton(msg)
        # self.payto_e.addWidget(qmark_help_but, index=0)        
        grid.addWidget(payto_label, 1, 0)
        grid.addWidget(self.payto_e, 1, 1, 1, -1)

        completer = QCompleter(self.payto_e)
        completer.setCaseSensitivity(False)
        self.payto_e.set_completer(completer)
        completer.setModel(self.completions)

        msg = _('Description of the transaction (not mandatory).') + '\n\n'\
              + _('The description is not sent to the recipient of the funds. It is stored in your wallet file, and displayed in the \'History\' tab.')
        description_label = HelpLabel(_('&Description'), msg)
        grid.addWidget(description_label, 2, 0)
        self.message_e = MyLineEdit()
        description_label.setBuddy(self.message_e)
        grid.addWidget(self.message_e, 2, 1, 1, -1)

        msg_opreturn = ( _('OP_RETURN data (optional).') + '\n\n'
                        + _('Posts a PERMANENT note to the Zclassic Blockchain as part of this transaction.')
                        + '\n\n' + _('If you specify OP_RETURN text, you may leave the \'Pay to\' field blank.') )
        self.opreturn_label = HelpLabel(_('OP_RETURN'), msg_opreturn)
        grid.addWidget(self.opreturn_label,  3, 0)
        self.message_opreturn_e = MyLineEdit()
        self.opreturn_label.setBuddy(self.message_opreturn_e)
        hbox = QHBoxLayout()
        hbox.addWidget(self.message_opreturn_e)
        self.opreturn_rawhex_cb = QCheckBox(_('&Raw hex script'))
        self.opreturn_rawhex_cb.setToolTip(_('If unchecked, the textbox contents are UTF8-encoded into a single-push script: <tt>OP_RETURN PUSH &lt;text&gt;</tt>. If checked, the text contents will be interpreted as a raw hexadecimal script to be appended after the OP_RETURN opcode: <tt>OP_RETURN &lt;script&gt;</tt>.'))
        hbox.addWidget(self.opreturn_rawhex_cb)        
        grid.addLayout(hbox,  3 , 1, 1, -1)

        self.send_tab_opreturn_widgets = [
            self.message_opreturn_e,
            self.opreturn_rawhex_cb,
            self.opreturn_label,
        ]

        self.from_label = QLabel(_('&From'))
        grid.addWidget(self.from_label, 4, 0)
        self.from_list = MyTreeWidget(self, self.from_list_menu, ['',''])
        self.from_label.setBuddy(self.from_list)
        self.from_list.setHeaderHidden(True)
        self.from_list.setMaximumHeight(80)
        grid.addWidget(self.from_list, 4, 1, 1, -1)
        self.set_pay_from([])

        if self.is_slp_wallet:
            msg = _('Token Amount to be sent.') + '\n\n' \
                + _("To enable make sure 'Address Mode' is set to ZSLP.") + '\n\n' \
                + _('The amount will be displayed in red if you do not have enough funds in your wallet.') + ' ' \
                + _('Note that if you have frozen some of your addresses, the available funds will be lower than your total balance.') + '\n\n' \
                + _('Keyboard shortcut: type "!" to send all your coins.')
            self.slp_amount_label = HelpLabel(_('Token Amount'), msg)

            msg = _('Select the ZSLP token to send.')
            self.slp_token_type_label = HelpLabel(_('Token Type'), msg)
            grid.addWidget(self.slp_token_type_label, 5, 0)
            grid.addWidget(self.token_type_combo, 5, 1)

            grid.addWidget(self.slp_amount_label, 6, 0)
            hbox = QHBoxLayout()
            self.amount_e.setMinimumWidth(195)
            self.slp_amount_e.setMinimumWidth(195)
            self.slp_amount_e.textEdited.connect(self.update_fee)
            hbox.addWidget(self.slp_amount_e)

            self.slp_max_button = EnterButton(_("Max"), self.slp_spend_max)
            hbox.addWidget(self.slp_max_button)
            grid.addLayout(hbox, 6, 1)

            self.slp_extra_zcl_cb = QCheckBox(_('Also send ZCL?'))
            self.slp_extra_zcl_cb.clicked.connect(self.on_slp_extra_zcl)
            self.slp_extra_zcl_cb.setHidden(True)
            grid.addWidget(self.slp_extra_zcl_cb, 6, 2)

            self.slp_send_tab_widgets += [
                self.slp_max_button, self.slp_extra_zcl_cb
            ]

        msg = _('ZCL amount to be sent.') + '\n\n' \
              + _('The amount will be displayed in red if you do not have enough funds in your wallet.') + ' ' \
              + _('Note that if you have frozen some of your addresses, the available funds will be lower than your total balance.') + '\n\n' \
              + _('Keyboard shortcut: type "!" to send all your coins.')
        self.amount_label = HelpLabel(_('ZCL &Amount'), msg)
        self.amount_label.setBuddy(self.amount_e)
        grid.addWidget(self.amount_label, 7, 0)
        hbox = QHBoxLayout()
        hbox.addWidget(self.amount_e)

        self.max_button = EnterButton(_("&Max"), self.spend_max)
        self.max_button.setCheckable(True)
        hbox.addWidget(self.max_button)
        grid.addLayout(hbox, 7, 1)

        self.fiat_send_e = AmountEdit(self.fx.get_currency if self.fx else '')
        if not self.fx or not self.fx.is_enabled():
            self.fiat_send_e.setVisible(False)
        grid.addWidget(self.fiat_send_e, 7, 2)
        self.amount_e.frozen.connect(
            lambda: self.fiat_send_e.setFrozen(self.amount_e.isReadOnly()))

        msg = _('Zclassic transactions are in general not free. A transaction fee is paid by the sender of the funds.') + '\n\n'\
              + _('The amount of fee can be decided freely by the sender. However, transactions with low fees take more time to be processed.') + '\n\n'\
              + _('A suggested fee is automatically added to this field. You may override it. The suggested fee increases with the size of the transaction.')
        self.fee_e_label = HelpLabel(_('F&ee'), msg)

        def fee_cb(dyn, pos, fee_rate):
            if dyn:
                self.config.set_key('fee_level', pos, False)
            else:
                self.config.set_key('fee_per_kb', fee_rate, False)
            self.spend_max() if self.max_button.isChecked() else self.update_fee()

        self.fee_slider = FeeSlider(self, self.config, fee_cb)
        self.fee_e_label.setBuddy(self.fee_slider)
        self.fee_slider.setFixedWidth(140)

        self.fee_custom_lbl = HelpLabel(self.get_custom_fee_text(),
                                        _('This is the fee rate that will be used for this transaction.')
                                        + "\n\n" + _('It is calculated from the Custom Fee Rate in preferences, but can be overridden from the manual fee edit on this form (if enabled).')
                                        + "\n\n" + _('Generally, a fee of 1.0 sats/B is a good minimal rate to ensure your transaction will make it into the next block.'))
        self.fee_custom_lbl.setFixedWidth(140)

        self.fee_slider_mogrifier()

        self.fee_e = BTCAmountEdit(self.get_decimal_point)
        if not self.config.get('show_fee', False):
            self.fee_e.setVisible(False)
        self.fee_e.textEdited.connect(self.update_fee)
        # This is so that when the user blanks the fee and moves on,
        # we go back to auto-calculate mode and put a fee back.
        self.fee_e.editingFinished.connect(self.update_fee)
        self.connect_fields(self, self.amount_e, self.fiat_send_e, self.fee_e)

        grid.addWidget(self.fee_e_label, 9, 0)
        hbox = QHBoxLayout()
        hbox.addWidget(self.fee_slider)
        # hbox.addWidget(self.fee_custom_lbl)
        hbox.addWidget(self.fee_e)
        hbox.addStretch(1)
        grid.addLayout(hbox, 9, 1)

        self.preview_button = EnterButton(_("&Preview"), self.do_preview)
        self.preview_button.setToolTip(_('Display the details of your transaction before signing it.'))
        self.send_button = EnterButton(_("&Send"), self.do_send)
        self.clear_button = EnterButton(_("&Clear"), self.do_clear)
        buttons = QHBoxLayout()
        buttons.addWidget(self.clear_button)
        buttons.addWidget(self.preview_button)
        buttons.addWidget(self.send_button)
        buttons.addStretch(1)
        grid.addLayout(buttons, 11, 1, 1, 3)

        self.payto_e.textChanged.connect(self.update_buttons_on_seed)

        self.amount_e.shortcut.connect(self.spend_max)
        self.payto_e.textChanged.connect(self.update_fee)
        self.amount_e.textEdited.connect(self.update_fee)
        self.message_opreturn_e.textEdited.connect(self.update_fee)
        self.message_opreturn_e.textChanged.connect(self.update_fee)
        self.message_opreturn_e.editingFinished.connect(self.update_fee)
        self.opreturn_rawhex_cb.stateChanged.connect(self.update_fee)

        def reset_max(text):
            self.max_button.setChecked(False)
            if not self.slp_token_id:
                enabled = not bool(text) and not self.amount_e.isReadOnly()
                self.max_button.setEnabled(enabled)
        self.amount_e.textEdited.connect(reset_max)
        self.fiat_send_e.textEdited.connect(reset_max)

        def entry_changed():
            if self.is_slp_wallet:
                hasError = entry_changed_slp()
                if hasError == False:
                    entry_changed_zcl()
            else:
                entry_changed_zcl()

        def entry_changed_zcl():
            text = ""
            if self.not_enough_funds:
                amt_color, fee_color = ColorScheme.RED, ColorScheme.RED
                text = _( "Not enough ZCL" )
                c, u, x = self.wallet.get_frozen_balance()
                if c+u+x:
                    text += ' (' + self.format_amount(c+u+x).strip() + ' ' + self.base_unit() + ' ' +_("are frozen") + ')'
                slp = self.wallet.get_slp_locked_balance()
                if slp > 0:
                    text += " (" + self.format_amount(slp).strip() + " ZCL held in tokens)"
                extra = run_hook("not_enough_funds_extra", self)
                if isinstance(extra, str) and extra:
                    text += " ({})".format(extra)

            elif self.fee_e.isModified():
                amt_color, fee_color = ColorScheme.DEFAULT, ColorScheme.DEFAULT
            elif self.amount_e.isModified():
                amt_color, fee_color = ColorScheme.DEFAULT, ColorScheme.BLUE
            else:
                amt_color, fee_color = ColorScheme.BLUE, ColorScheme.BLUE
            opret_color = ColorScheme.DEFAULT
            if self.op_return_toolong:
                opret_color = ColorScheme.RED
                text = _("OP_RETURN message too large, needs to be no longer than 220 bytes") + (", " if text else "") + text

            self.statusBar().showMessage(text)
            self.amount_e.setStyleSheet(amt_color.as_stylesheet())
            self.fee_e.setStyleSheet(fee_color.as_stylesheet())
            self.message_opreturn_e.setStyleSheet(opret_color.as_stylesheet())

        self.amount_e.textChanged.connect(entry_changed)
        self.fee_e.textChanged.connect(entry_changed)
        self.message_opreturn_e.textChanged.connect(entry_changed)
        self.message_opreturn_e.textEdited.connect(entry_changed)
        self.message_opreturn_e.editingFinished.connect(entry_changed)
        self.opreturn_rawhex_cb.stateChanged.connect(entry_changed)
        if self.is_slp_wallet:
            self.slp_amount_e.textChanged.connect(entry_changed)
            self.slp_amount_e.editingFinished.connect(entry_changed)        

        def entry_changed_slp():
            if self.token_type_combo.currentData():
                text = ""
                name = self.wallet.token_types.get(self.slp_token_id)['name']
                decimals = self.wallet.token_types.get(self.slp_token_id)['decimals']
                if self.not_enough_funds_slp or self.not_enough_unfrozen_funds_slp:
                    bal_avail, x, x, x, frozen_amt = self.wallet.get_slp_token_balance(self.slp_token_id, { 'user_config': { 'confirmed_only': False }})
                    del x
                    if self.not_enough_funds_slp:
                        amt_color = ColorScheme.RED
                        text = "Not enough " + \
                                name + " tokens (" + \
                                format_satoshis_plain_nofloat(bal_avail, decimals) + " valid"
                        if self.config.get('confirmed_only', False):
                            conf_bal_avail = self.wallet.get_slp_token_balance(self.slp_token_id, self.config)[0]
                            unconf_bal = bal_avail - conf_bal_avail
                            if unconf_bal > 0:
                                text += ", " + format_satoshis_plain_nofloat(unconf_bal, decimals) + " unconfirmed)"
                            else:
                                text += ")"
                        else:
                            text += ")"
                    elif self.not_enough_unfrozen_funds_slp:
                        amt_color = ColorScheme.RED
                        text = "Not enough unfrozen " + name + " tokens (" + \
                                format_satoshis_plain_nofloat(bal_avail, decimals) + " valid, " + \
                                format_satoshis_plain_nofloat(frozen_amt, decimals) + " frozen)"
                elif self.slp_amount_e.isModified():
                    amt_color = ColorScheme.DEFAULT
                else:
                    amt_color = ColorScheme.BLUE

                try:
                    if self.slp_amount_e.get_amount() > (2 ** 64) - 1:
                        amt_color = ColorScheme.RED
                        maxqty = format_satoshis_plain_nofloat((2 ** 64) - 1, self.wallet.token_types.get(self.slp_token_id)['decimals'])
                        text = _('Token output quantity is too large. Maximum {maxqty}.').format(maxqty=maxqty)
                except TypeError:
                    pass

                self.statusBar().showMessage(text)
                self.slp_amount_e.setStyleSheet(amt_color.as_stylesheet())
                if text != "":
                    return True
            return False

        self.invoices_label = QLabel(_('Invoices'))
        from .invoice_list import InvoiceList
        self.invoice_list = InvoiceList(self)
        self.invoice_list.chkVisible()

        vbox0 = QVBoxLayout()
        vbox0.addLayout(grid)
        hbox = QHBoxLayout()
        hbox.addLayout(vbox0)

        w = QWidget()
        vbox = QVBoxLayout(w)
        vbox.addLayout(hbox)
        vbox.addStretch(1)
        vbox.addWidget(self.invoices_label)
        vbox.addWidget(self.invoice_list)
        vbox.setStretchFactor(self.invoice_list, 1000)
        w.searchable_list = self.invoice_list
        run_hook('create_send_tab', grid)
        return w

    def spend_max(self):
        self.max_button.setChecked(True)
        self.do_update_fee()

    def slp_spend_max(self):
        self.slp_amount_e.setAmount(self.wallet.get_slp_token_balance(self.slp_token_id, self.config)[3])
        self.do_update_fee()

    def update_fee(self):
        self.require_fee_update = True

    def get_payto_or_dummy(self):
        r = self.payto_e.get_recipient()
        if r:
            return r
        return (TYPE_ADDRESS, self.wallet.dummy_address())

    def get_custom_fee_text(self, fee_rate = None):
        if not self.config.has_custom_fee_rate():
            return ""
        else:
            if fee_rate is None: fee_rate = self.config.custom_fee_rate() / 1000.0
            return str(round(fee_rate*100)/100) + " sats/B"

    @staticmethod
    def output_for_opreturn_stringdata(op_return):
        if not isinstance(op_return, str):
            raise OPReturnError('OP_RETURN parameter needs to be of type str!')
        pushes = op_return.split('<push>')
        script = "OP_RETURN"
        for data in pushes:
            if data.startswith("<hex>"):
                data = data.replace("<hex>", "")
            elif data.startswith("<empty>"):
                pass
            else:
                data = data.encode('utf-8').hex()
            script = script + " " + data 
        scriptBuffer = ScriptOutput.from_string(script)
        if len(scriptBuffer.script) > 223:
            raise OPReturnTooLarge(_("OP_RETURN message too large, needs to be under 220 bytes"))
        amount = 0
        return (TYPE_SCRIPT, scriptBuffer, amount)

    @staticmethod
    def output_for_opreturn_rawhex(op_return):
        if not isinstance(op_return, str):
            raise OPReturnError('OP_RETURN parameter needs to be of type str!')
        if op_return == 'empty':
            op_return = ''
        try:
            op_return_script = b'\x6a' + bytes.fromhex(op_return.strip())
        except ValueError:
            raise OPReturnError(_('OP_RETURN script expected to be hexadecimal bytes'))
        if len(op_return_script) > 223:
            raise OPReturnTooLarge(_("OP_RETURN script too large, needs to be under 223 bytes"))
        amount = 0
        return (TYPE_SCRIPT, ScriptOutput(op_return_script), amount)

    def do_update_fee(self):
        '''Recalculate the fee.  If the fee was manually input, retain it, but
        still build the TX to see if there are enough funds.
        '''
        zcl_outputs = []
        token_output_amts = []
        self.not_enough_funds = False
        self.not_enough_funds_slp = False
        self.not_enough_unfrozen_funds_slp = False
        freeze_fee = (self.fee_e.isModified()
                      and (self.fee_e.text() or self.fee_e.hasFocus()))
        amount = '!' if self.max_button.isChecked() else self.amount_e.get_amount()
        fee_rate = None
        if self.is_slp_wallet:
            slp_amount = self.slp_amount_e.get_amount()
            if amount is None and slp_amount is None:
                if not freeze_fee:
                    self.fee_e.setAmount(None)
                self.statusBar().showMessage('')
                return
        else:
            if amount is None:
                if not freeze_fee:
                    self.fee_e.setAmount(None)
                self.statusBar().showMessage('')
                return

        try:
            selected_slp_coins = []
            if self.slp_token_id:
                amt = slp_amount or 0
                selected_slp_coins, slp_op_return_msg = SlpCoinChooser.select_coins(self.wallet, self.slp_token_id, amt, self.config)
                if slp_op_return_msg:
                    zcl_outputs = [ slp_op_return_msg ]
                    token_output_amts = slp.SlpMessage.parseSlpOutputScript(zcl_outputs[0][1]).op_return_fields['token_output']
                    for amt in token_output_amts:
                        # just grab a dummy address for this fee calculation - safe for imported_privkey wallets
                        zcl_outputs.append((TYPE_ADDRESS, self.wallet.get_addresses()[0], 546))

            zcl_payto_outputs = self.payto_e.get_outputs(self.max_button.isChecked())
            if zcl_payto_outputs and zcl_payto_outputs[0][2]:
                zcl_outputs.extend(zcl_payto_outputs)
            elif self.slp_token_id and amount and not zcl_payto_outputs:
                _type, addr = self.get_payto_or_dummy()
                zcl_outputs.append((_type, addr, amount))
            if not zcl_outputs:
                _type, addr = self.get_payto_or_dummy()
                zcl_outputs.append((_type, addr, amount))

            if not self.slp_token_id:
                opreturn_message = self.message_opreturn_e.text() if self.config.get('enable_opreturn') else None
                if (opreturn_message != '' and opreturn_message is not None):
                    if self.opreturn_rawhex_cb.isChecked():
                        zcl_outputs.insert(0, self.output_for_opreturn_rawhex(opreturn_message))
                    else:
                        zcl_outputs.insert(0, self.output_for_opreturn_stringdata(opreturn_message))

            fee = self.fee_e.get_amount() if freeze_fee else None
            tx = self.wallet.make_unsigned_transaction(self.get_coins(isInvoice = False), zcl_outputs, self.config, fee, mandatory_coins=selected_slp_coins)
            if self.slp_token_id:
                self.wallet.check_sufficient_slp_balance(slp.SlpMessage.parseSlpOutputScript(slp_op_return_msg[1]), self.config)
            self.not_enough_funds = False
            self.op_return_toolong = False
        except NotEnoughFunds:
            self.not_enough_funds = True
            if not freeze_fee:
                self.fee_e.setAmount(None)
            return
        except NotEnoughFundsSlp:
            self.not_enough_funds_slp = True
            if not freeze_fee:
                self.fee_e.setAmount(None)
            return
        except NotEnoughUnfrozenFundsSlp:
            self.not_enough_unfrozen_funds_slp = True
            if not freeze_fee:
                self.fee_e.setAmount(None)
            return
        except OPReturnTooLarge:
            self.op_return_toolong = True
            return
        except OPReturnError as e:
            self.statusBar().showMessage(str(e))
            return
        except BaseException:
            return

        if not freeze_fee:
            fee = None if self.not_enough_funds else tx.get_fee()
            if not self.slp_token_id or len(token_output_amts) > 0:
                self.fee_e.setAmount(fee)

        if self.max_button.isChecked():
            amount = tx.output_value()
            if self.is_slp_wallet:
                amount = tx.output_value() - len(token_output_amts) * 546
            self.amount_e.setAmount(amount)
        if fee is not None:
            fee_rate = fee / tx.estimated_size()
        self.fee_slider_mogrifier(self.get_custom_fee_text(fee_rate))

    def fee_slider_mogrifier(self, text = None):
        fee_slider_hidden = self.config.has_custom_fee_rate()
        self.fee_slider.setHidden(fee_slider_hidden)
        self.fee_custom_lbl.setHidden(not fee_slider_hidden)
        if text is not None: self.fee_custom_lbl.setText(text)

    def from_list_delete(self, item):
        i = self.from_list.indexOfTopLevelItem(item)
        self.pay_from.pop(i)
        self.redraw_from_list()
        self.update_fee()

    def from_list_menu(self, position):
        item = self.from_list.itemAt(position)
        menu = QMenu()
        menu.addAction(_("Remove"), lambda: self.from_list_delete(item))
        menu.exec_(self.from_list.viewport().mapToGlobal(position))

    def set_pay_from(self, coins):
        self.pay_from = list(coins)
        self.redraw_from_list()

    def redraw_from_list(self):
        self.from_list.clear()
        self.from_label.setHidden(len(self.pay_from) == 0)
        self.from_list.setHidden(len(self.pay_from) == 0)

        def format(x):
            h = x['prevout_hash']
            return '{}...{}:{:d}\t{}'.format(h[0:10], h[-10:], x['prevout_n'], x['address'])

        for item in self.pay_from:
            self.from_list.addTopLevelItem(QTreeWidgetItem( [format(item), self.format_amount(item['value']) ]))

    def get_contact_payto(self, key):
        _type, label = self.contacts.get(key)
        return label + '  <' + key + '>' if _type == 'address' else key

    def update_completions(self):
        l = [self.get_contact_payto(key) for key in self.contacts.keys()]
        self.completions.setStringList(l)

    def protected(func):
        '''Password request wrapper.  The password is passed to the function
        as the 'password' named argument.  "None" indicates either an
        unencrypted wallet, or the user cancelled the password request.
        An empty input is passed as the empty string.'''
        def request_password(self, *args, **kwargs):
            parent = self.top_level_window()
            password = None
            while self.wallet.has_keystore_encryption():
                password = self.password_dialog(parent=parent)
                if password is None:
                    # User cancelled password input
                    return
                try:
                    self.wallet.check_password(password)
                    break
                except Exception as e:
                    self.show_error(str(e), parent=parent)
                    continue

            kwargs['password'] = password
            return func(self, *args, **kwargs)
        return request_password

    def is_send_fee_frozen(self):
        return self.fee_e.isVisible() and self.fee_e.isModified() \
               and (self.fee_e.text() or self.fee_e.hasFocus())

    def is_send_feerate_frozen(self):
        return self.feerate_e.isVisible() and self.feerate_e.isModified() \
               and (self.feerate_e.text() or self.feerate_e.hasFocus())

    def get_send_fee_estimator(self):
        if self.is_send_fee_frozen():
            fee_estimator = self.fee_e.get_amount()
        elif self.is_send_feerate_frozen():
            amount = self.feerate_e.get_amount()
            amount = 0 if amount is None else amount
            fee_estimator = partial(
                simple_config.SimpleConfig.estimate_fee_for_feerate, amount)
        else:
            fee_estimator = None
        return fee_estimator

    def read_send_tab(self, preview=False):
        zcl_outputs = []
        selected_slp_coins = []
        opreturn_message = self.message_opreturn_e.text() if self.config.get('enable_opreturn') else None
        if self.slp_token_id:
            if self.slp_amount_e.get_amount() == 0 or self.slp_amount_e.get_amount() is None:
                self.show_message(_("No ZSLP token amount provided."))
                return
            try:
                """ Guard against multiline 'Pay To' field """
                if self.payto_e.is_multiline():
                    self.show_error(_("Too many receivers listed.\n\nCurrently this wallet only supports a single ZSLP token receiver."))
                    return
                """ Guard against bad address encoding """
                if not self.payto_e.payto_address:
                    self.show_error(_("The ZSLP address provided is not encoded properly."))
                    return
                """ Require SLPADDR prefix in 'Pay To' field. """
                if constants.net.SLPADDR_PREFIX not in self.payto_e.address_string_for_slp_check:
                    self.show_error(_("Address provided is not in ZSLP Address format.\n\nThe address should be encoded using 'zslp:' or 'zslptest:' URI prefix."))
                    return
                amt = self.slp_amount_e.get_amount()
                selected_slp_coins, slp_op_return_msg = SlpCoinChooser.select_coins(self.wallet, self.slp_token_id, amt, self.config)
                if slp_op_return_msg:
                    zcl_outputs = [ slp_op_return_msg ]
            except OPReturnTooLarge as e:
                self.show_error(str(e))
                return
            except OPReturnError as e:
                self.show_error(str(e))
                return
            except (NotEnoughFundsSlp, NotEnoughUnfrozenFundsSlp) as e:
                self.show_error(str(e))
                return

        isInvoice = False

        if self.payment_request and self.payment_request.has_expired():
            self.show_error(_('Payment request has expired'))
            return
        label = self.message_e.text()

        if self.payment_request:
            if self.slp_token_id:
                self.show_error('BIP-70 Payment requests are not yet working for ZSLP tokens.')
                return
            isInvoice = True
            outputs.extend(self.payment_request.get_outputs())
        else:
            errors = self.payto_e.get_errors()
            if errors:
                self.show_warning(_("Invalid lines found:") + "\n\n" + '\n'.join([ _("Line #") + str(x[0]+1) + ": " + x[1] for x in errors]))
                return
            if self.slp_token_id:
                _type, _addr = self.payto_e.payto_address
                zcl_outputs.append((_type, _addr, 546))

            if self.payto_e.is_alias and self.payto_e.validated is False:
                alias = self.payto_e.toPlainText()
                msg = _('WARNING: the alias "{}" could not be validated via an additional '
                        'security check, DNSSEC, and thus may not be correct.').format(alias) + '\n'
                msg += _('Do you wish to continue?')
                if not self.question(msg):
                    return

        coins = self.get_coins(isInvoice=isInvoice)

        """ SLP: Add an additional token change output """
        if self.slp_token_id:
            change_addr = None
            token_outputs = slp.SlpMessage.parseSlpOutputScript(zcl_outputs[0][1]).op_return_fields['token_output']
            if len(token_outputs) > 1 and len(zcl_outputs) < len(token_outputs):
                """ start of logic copied from wallet.py """
                addrs = self.wallet.get_change_addresses()[-self.wallet.gap_limit_for_change:]
                if self.wallet.use_change and addrs:
                    # New change addresses are created only after a few
                    # confirmations.  Select the unused addresses within the
                    # gap limit; if none take one at random
                    change_addrs = [addr for addr in addrs if
                                    self.wallet.get_num_tx(addr) == 0]
                    if not change_addrs:
                        import random
                        change_addrs = [random.choice(addrs)]
                        change_addr = change_addrs[0]
                    elif len(change_addrs) > 1:
                        change_addr = change_addrs[1]
                    else:
                        change_addr = change_addrs[0]
                elif coins:
                    change_addr = coins[0]['address']
                else:
                    change_addr = self.wallet.get_addresses()[0]
                zcl_outputs.append((TYPE_ADDRESS, change_addr, 546))

        # add normal BCH amounts
        if not self.payment_request and self.amount_e.get_amount():
            zcl_outputs.extend(self.payto_e.get_outputs(self.max_button.isChecked()))

        """ Only Allow OP_RETURN if SLP is disabled. """
        if not self.slp_token_id:
            try:
                # handle op_return if specified and enabled
                opreturn_message = self.message_opreturn_e.text()
                if opreturn_message:
                    if self.opreturn_rawhex_cb.isChecked():
                        zcl_outputs.append(self.output_for_opreturn_rawhex(opreturn_message))
                    else:
                        zcl_outputs.append(self.output_for_opreturn_stringdata(opreturn_message))
            except OPReturnTooLarge as e:
                self.show_error(str(e))
                return
            except OPReturnError as e:
                self.show_error(str(e))
                return

  
        if not zcl_outputs:
            self.show_error(_('Enter receiver address (No ZCL outputs).'))
            return

        for _type, addr, amount in zcl_outputs:
            if amount is None:
                self.show_error(_('Invalid Amount'))
                return

        freeze_fee = self.fee_e.isVisible() and self.fee_e.isModified() and (self.fee_e.text() or self.fee_e.hasFocus())
        fee = self.fee_e.get_amount() if freeze_fee else None
        return zcl_outputs, fee, label, coins, selected_slp_coins

    def do_preview(self):
        self.do_send(preview = True)

    def do_send(self, preview = False):
        if run_hook('abort_send', self):
            return
        
        r = self.read_send_tab(preview=preview)
        
        if not r:
            return
        outputs, fee, tx_desc, coins, slp_coins = r
        
        if self.slp_token_id:
            try:
                self.wallet.check_sufficient_slp_balance(slp.SlpMessage.parseSlpOutputScript(outputs[0][1]), self.config)
            except slp.SlpInvalidOutputMessage:
                self.show_message(_("No token outputs available.\n\nIf you have unconfirmed tokens wait 1 confirmation or turn off 'Spend only confirmed coins' in preferences, and try again."))
                return
            except NotEnoughFundsSlp:
                self.show_message(_("Token balance too low."))
                return
            except NotEnoughUnfrozenFundsSlp:
                self.show_message(_("Unfrozen ZSLP token balance is too low.  Unfreeze some of the token coins associated with with this token."))
                return        

        try:
            tx = self.wallet.make_unsigned_transaction(coins, outputs, self.config, fee, mandatory_coins=slp_coins)
        except NotEnoughFunds:
            self.show_message(_("Insufficient ZCL balance"))
            return
        except ExcessiveFee:
            self.show_message(_("Your fee is too high.  Max is 50 sat/byte."))
            return
        except BaseException as e:
            traceback.print_exc(file=sys.stderr)
            self.show_message(str(e))
            return

        amount = tx.output_value() if self.max_button.isChecked() else sum(map(lambda x:x[2], outputs))
        fee = tx.get_fee()

        # if fee < self.wallet.relayfee() * tx.estimated_size() / 1000:
        #     self.show_error('\n'.join([
        #         _("This transaction requires a higher fee, or it will not be propagated by your current server"),
        #         _("Try to raise your transaction fee, or use a server with a lower relay fee.")
        #     ]))
        #     return

        if preview:
            self.show_transaction(tx, tx_desc)
            return

        # confirmation dialog
        if self.slp_token_id:
            slp_amt_str = format_satoshis_plain_nofloat(self.slp_amount_e.get_amount(), self.wallet.token_types.get(self.slp_token_id)['decimals'])
            slp_name = self.wallet.token_types[self.slp_token_id]['name']
            msg = [
                _("BCH amount to be sent") + ": " + self.format_amount_and_units(amount),
                "\nToken amount to be sent" + ": " + slp_amt_str + " " + slp_name,
                _("\nMining fee") + ": " + self.format_amount_and_units(fee),
            ]
        else:
            msg = [
                _("Amount to be sent") + ": " + self.format_amount_and_units(amount),
                _("Mining fee") + ": " + self.format_amount_and_units(fee),
            ]

        x_fee = run_hook('get_tx_extra_fee', self.wallet, tx)
        if x_fee:
            x_fee_address, x_fee_amount = x_fee
            msg.append( _("Additional fees") + ": " + self.format_amount_and_units(x_fee_amount) )

        confirm_rate = simple_config.FEERATE_WARNING_HIGH_FEE
        
        # if fee > confirm_rate * tx.estimated_size() / 1000:
        #     msg.append(_('Warning') + ': ' + _("The fee for this transaction seems unusually high."))

        if (fee < (tx.estimated_size())):
            msg.append(_('\nWarning') + ': ' + _("You're using a fee of less than 1.0 sats/B. It may take a very long time to confirm."))
            tx.ephemeral['warned_low_fee_already'] = True

        if self.config.get('enable_opreturn') and self.message_opreturn_e.text():
            msg.append(_("\nYou are using an OP_RETURN message. This gets written permanently written to the blockchain."))

        if self.wallet.has_password():
            msg.append("")
            msg.append(_("\nEnter your password to proceed"))
            password = self.password_dialog('\n'.join(msg))
            if not password:
                return
        else:
            msg.append(_('\nProceed?'))
            password = None
            if not self.question('\n'.join(msg)):
                return

        def sign_done(success):
            if success:
                if not tx.is_complete():
                    self.show_transaction(tx, tx_desc)
                    self.do_clear()
                else:
                    self.broadcast_transaction(tx, tx_desc)
        self.sign_tx_with_password(tx, sign_done, password)

    @protected
    def sign_tx(self, tx, callback, password, *, slp_coins_to_burn=None):
        self.sign_tx_with_password(tx, callback, password, slp_coins_to_burn=slp_coins_to_burn)

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

        def on_signed(result):
            callback(True)
        def on_failed(exc_info):
            self.on_error(exc_info)
            callback(False)

        if self.tx_external_keypairs:
            # can sign directly
            task = partial(Transaction.sign, tx, self.tx_external_keypairs)
        else:
            # call hook to see if plugin needs gui interaction
            run_hook('sign_tx', self, tx)
            task = partial(self.wallet.sign_transaction, tx, password)
        WaitingDialog(self, _('Signing transaction...'), task,
                      on_signed, on_failed)

    def broadcast_transaction(self, tx, tx_desc):

        def broadcast_thread():
            # non-GUI thread
            pr = self.payment_request
            if pr and pr.has_expired():
                self.payment_request = None
                return False, _("Payment request has expired")
            status, msg =  self.network.broadcast(tx)
            if pr and status is True:
                self.invoices.set_paid(pr, tx.txid())
                self.invoices.save()
                self.payment_request = None
                refund_address = self.wallet.get_receiving_addresses()[0]
                ack_status, ack_msg = pr.send_ack(str(tx), refund_address)
                if ack_status:
                    msg = ack_msg
            return status, msg

        # Capture current TL window; override might be removed on return
        parent = self.top_level_window(lambda win: isinstance(win, MessageBoxMixin))

        def broadcast_done(result):
            # GUI thread
            if result:
                status, msg = result
                if status:
                    if tx_desc is not None and tx.is_complete():
                        self.wallet.set_label(tx.txid(), tx_desc)
                    parent.show_message(_('Payment sent.') + '\n' + msg)
                    self.invoice_list.update()
                    self.do_clear()
                else:
                    parent.show_error(msg)

        WaitingDialog(self, _('Broadcasting transaction...'),
                      broadcast_thread, broadcast_done, self.on_error)

    def query_choice(self, msg, choices):
        # Needed by QtHandler for hardware wallets
        dialog = WindowModalDialog(self.top_level_window())
        clayout = ChoicesLayout(msg, choices)
        vbox = QVBoxLayout(dialog)
        vbox.addLayout(clayout.layout())
        vbox.addLayout(Buttons(OkButton(dialog)))
        if not dialog.exec_():
            return None
        return clayout.selected_index()

    def lock_amount(self, b):
        '''
        This if-statement was added for SLP around the following two lines
        in order to keep the amount field locked and Max button disabled
        when the payto field is edited when a token is selected.
        '''
        if self.token_type_combo.currentData():
            self.amount_e.setFrozen(True)
            self.max_button.setEnabled(False)

    def prepare_for_payment_request(self):
        self.show_send_tab()
        self.payto_e.is_pr = True
        for e in [self.payto_e, self.amount_e, self.message_e]:
            e.setFrozen(True)
        self.payto_e.setText(_("please wait..."))
        return True

    def delete_invoice(self, key):
        self.invoices.remove(key)
        self.invoice_list.update()

    def payment_request_ok(self):
        pr = self.payment_request
        key = self.invoices.add(pr)
        status = self.invoices.get_status(key)
        self.invoice_list.update()
        if status == PR_PAID:
            self.show_message("invoice already paid")
            self.do_clear()
            self.payment_request = None
            return
        self.payto_e.is_pr = True
        if not pr.has_expired():
            self.payto_e.setGreen()
        else:
            self.payto_e.setExpired()
        self.payto_e.setText(pr.get_requestor())
        self.amount_e.setText(format_satoshis_plain(pr.get_amount(), self.decimal_point))
        self.message_e.setText(pr.get_memo())
        # signal to set fee
        self.amount_e.textEdited.emit("")

    def payment_request_error(self):
        self.show_message(self.payment_request.error)
        self.payment_request = None
        self.do_clear()

    def on_pr(self, request):
        self.payment_request = request
        if self.payment_request.verify(self.contacts):
            self.payment_request_ok_signal.emit()
        else:
            self.payment_request_error_signal.emit()

    def pay_to_URI(self, URI):
        if not URI:
            return
        try:
            out = web.parse_URI(URI, self.on_pr)
        except BaseException as e:
            self.show_error(_('Invalid Address URI:') + '\n' + str(e))
            return
        self.show_send_tab()
        r = out.get('r')
        sig = out.get('sig')
        name = out.get('name')
        if r or (name and sig):
            self.prepare_for_payment_request()
            return
        address = out.get('address')
        amount = out.get('amount')
        label = out.get('label')
        message = out.get('message')
        op_return = out.get('op_return')
        op_return_raw = out.get('op_return_raw')

        # use label as description (not BIP21 compliant)
        if label and not message:
            message = label
        if address:
            self.payto_e.setText(URI.split('?')[0])
        if message:
            self.message_e.setText(message)
        if amount:
            self.amount_e.setAmount(amount)
            self.amount_e.textEdited.emit("")
        if op_return:
            self.message_opreturn_e.setText(op_return)
            self.message_opreturn_e.setHidden(False)
            self.opreturn_rawhex_cb.setHidden(False)
            self.opreturn_rawhex_cb.setChecked(False)
            self.opreturn_label.setHidden(False)
        elif op_return_raw is not None:
            # 'is not None' allows blank value.
            # op_return_raw is secondary precedence to op_return
            if not op_return_raw:
                op_return_raw='empty'
            self.message_opreturn_e.setText(op_return_raw)
            self.message_opreturn_e.setHidden(False)
            self.opreturn_rawhex_cb.setHidden(False)
            self.opreturn_rawhex_cb.setChecked(True)
            self.opreturn_label.setHidden(False)
        elif not self.config.get('enable_opreturn'):
            self.message_opreturn_e.setText('')
            self.message_opreturn_e.setHidden(True)
            self.opreturn_label.setHidden(True)

    def do_clear(self):
        """
        If SLP token is not selected proceed as normal, otherwise see
        the else-statement below which provides modified "do_clear" behavior
        after a payment is sent
        """
        if self.token_type_combo.currentData() is None:
            self.is_max = False
            self.not_enough_funds = False
            self.not_enough_funds_slp = False
            self.not_enough_unfrozen_funds_slp = False
            self.op_return_toolong = False
            self.payment_request = None
            self.payto_e.is_pr = False
            for e in [self.payto_e, self.message_e, self.amount_e, self.fiat_send_e, self.fee_e, self.message_opreturn_e]:
                e.setText('')
                e.setFrozen(False)
            self.max_button.setDisabled(False)
            self.set_pay_from([])
            self.tx_external_keypairs = {}
            self.update_status()
            self.slp_amount_e.setText('')
            run_hook('do_clear', self)
        else:
            self.not_enough_funds = False
            self.not_enough_funds_slp = False
            self.not_enough_unfrozen_funds_slp = False
            self.payment_request = None
            self.payto_e.is_pr = False
            for e in [self.payto_e, self.message_e, self.message_opreturn_e]:
                e.setText('')
                e.setFrozen(False)
            self.max_button.setDisabled(True)
            self.set_pay_from([])
            self.tx_external_keypairs = {}
            self.message_opreturn_e.setVisible(self.config.get('enable_opreturn', False))
            self.opreturn_label.setVisible(self.config.get('enable_opreturn', False))
            self.update_status()
            self.slp_amount_e.setText('')
            #run_hook('do_clear', self)

    def set_frozen_state(self, addrs, freeze):
        self.wallet.set_frozen_state(addrs, freeze)
        self.address_list.update()
        self.utxo_list.update()
        self.update_fee()

    def set_frozen_coin_state(self, utxos, freeze):
        self.wallet.set_frozen_coin_state(utxos, freeze)
        self.utxo_list.update()
        self.update_fee()

    def create_converter_tab(self):

        source_address = QLineEdit()
        zclassic_address = ButtonsLineEdit()
        zclassic_address.addCopyButton(self.app)
        zclassic_address.setReadOnly(True)
        slp_address = ButtonsLineEdit()
        slp_address.setReadOnly(True)
        slp_address.addCopyButton(self.app)
        widgets = [
            (zclassic_address, Address.FMT_ZCLASSIC),
            (slp_address, Address.FMT_SLPADDR)
        ]

        def convert_address():
            try:
                addr = Address.from_string(source_address.text().strip())
            except:
                addr = None
            for widget, fmt in widgets:
                if addr:
                    widget.setText(addr.to_full_string(fmt))
                else:
                    widget.setText('')

        source_address.textChanged.connect(convert_address)

        w = QWidget()
        grid = QGridLayout()
        grid.setSpacing(15)
        grid.setColumnStretch(1, 2)
        grid.setColumnStretch(2, 1)

        label = QLabel(_('&Address to convert'))
        label.setBuddy(source_address)
        grid.addWidget(label, 0, 0)
        grid.addWidget(source_address, 0, 1)

        label = QLabel(_('&Zclassic address'))
        label.setBuddy(zclassic_address)
        grid.addWidget(label, 1, 0)
        grid.addWidget(zclassic_address, 1, 1)

        grid.addWidget(QLabel(_('ZSLP address')), 3, 0)
        grid.addWidget(slp_address, 3, 1)
        w.setLayout(grid)

        label = WWLabel(_(
            "This tool helps convert between address formats for Zclassic addresses. "
        ))

        vbox = QVBoxLayout()
        vbox.addWidget(label)
        vbox.addWidget(w)
        vbox.addStretch(1)

        w = QWidget()
        w.setLayout(vbox)

        return w

    def create_list_tab(self, l, list_header=None):
        class ListTab(QWidget):
            def showEvent(self, e):
                super().showEvent(e)
                if self.main_window.is_slp_wallet:
                    self.main_window.toggle_cashaddr(1, True)
                else:
                    self.main_window.toggle_cashaddr(0, True)

        w = ListTab()
        w.main_window = self
        w.searchable_list = l
        vbox = QVBoxLayout()
        w.setLayout(vbox)
        vbox.setContentsMargins(0, 0, 0, 0)
        vbox.setSpacing(0)
        if list_header:
            hbox = QHBoxLayout()
            for b in list_header:
                hbox.addWidget(b)
            hbox.addStretch()
            vbox.addLayout(hbox)
        vbox.addWidget(l)
        return w

    def create_addresses_tab(self):
        from .address_list import AddressList
        self.address_list = l = AddressList(self)
        self.cashaddr_toggled_signal.connect(l.update)
        return self.create_list_tab(l)

    def create_utxo_tab(self):
        from .utxo_list import UTXOList
        self.utxo_list = l = UTXOList(self)
        self.cashaddr_toggled_signal.connect(l.update)
        return self.create_list_tab(l)

    def create_slp_mgt_tab(self):
        self.create_token_dialog = None
        from .slp_mgt import SlpMgt
        self.token_list = l = SlpMgt(self)
        w = self.create_list_tab(l)
        vbox = w.layout()
        vbox.setSpacing(10)
        create_button = b = QPushButton(_("Create New Token"))
        create_button.setAutoDefault(False)
        create_button.setDefault(False)
        b.clicked.connect(self.show_create_token_dialog)
        vbox.addWidget(create_button)
        w.setLayout(vbox)
        return w

    def show_create_token_dialog(self):
        c, u, x = self.wallet.get_balance()
        bal = c + u - self.wallet.get_slp_locked_balance()
        if bal < 1000:
            self.receive_tab.low_balance_warning_shown = True
            self.show_warning("Low ZCL balance.\n\nBefore creating a new token you must add Zclassic to this wallet.  We recommend a minimum of 0.0001 ZCL to get started.\n\nSend ZCL to the address displayed in the 'Receive' tab.")
            self.show_receive_tab()
            self.toggle_cashaddr(1, True)
            return
        try:
            self.create_token_dialog.show()
            self.create_token_dialog.raise_()
            self.create_token_dialog.activateWindow()
        except AttributeError:
            self.create_token_dialog = d = SlpCreateTokenGenesisDialog(self,)

    def create_contacts_tab(self):
        from .contact_list import ContactList
        self.contact_list = l = ContactList(self)
        return self.create_list_tab(l)

    def remove_address(self, addr):
        if self.question(_("Do you want to remove")+" %s "%addr +_("from your wallet?")):
            self.wallet.delete_address(addr)
            self.need_update.set()  # history, addresses, coins
            self.clear_receive_tab()

    def get_coins(self, isInvoice = False, *, slpTokenId = None):
        if self.pay_from:
            return self.pay_from
        else:
            return self.wallet.get_spendable_coins(None, self.config, isInvoice)

    def spend_coins(self, coins):
        self.set_pay_from(coins)
        self.show_send_tab()
        self.update_fee()

    def paytomany(self):
        self.show_send_tab()
        self.payto_e.paytomany()
        msg = '\n'.join([
            _('Enter a list of outputs in the \'Pay to\' field.'),
            _('One output per line.'),
            _('Format: address, amount'),
            _('You may load a CSV file using the file icon.')
        ])
        self.show_message(msg, title=_('Pay to many'))

    def payto_contacts(self, labels):
        paytos = [self.get_contact_payto(label) for label in labels]
        self.show_send_tab()
        if len(paytos) == 1:
            self.payto_e.setText(paytos[0])
            self.amount_e.setFocus()
        else:
            text = "\n".join([payto + ", 0" for payto in paytos])
            self.payto_e.setText(text)
            self.payto_e.setFocus()

    def set_contact(self, label, address):
        if not is_address(address):
            self.show_error(_('Invalid Address'))
            self.contact_list.update()  # Displays original unchanged value
            return False
        self.contacts[address] = ('address', label)
        self.contact_list.update()
        self.history_list.update()
        self.update_completions()
        return True

    def delete_contacts(self, labels):
        if not self.question(_("Remove {} from your list of contacts?")
                             .format(" + ".join(labels))):
            return
        for label in labels:
            self.contacts.pop(label)
        self.history_list.update()
        self.contact_list.update()
        self.update_completions()

    def add_token_type(self, token_class, token_id, token_name, decimals_divisibility, *, error_callback=None, show_errors=True, allow_overwrite=False):
        # FIXME: are both args error_callback and show_errors both necessary?
        # Maybe so if we want the default to be self.show_error...

        if not show_errors:
            # setting error_callback to None will suppress errors being shown
            # iff show_errors is False
            error_callback = None
        if error_callback is None and show_errors:
            # They asked for errors but supplied no callback. Use the standard
            # one for main_window
            error_callback = self.show_error

        # The below call checks sanity and calls error_callback for us
        # with an error message argument on failure, returning False.
        # On success it will add the token, write to wallet storage,
        # and potentially kick off the verifier.
        if not self.wallet.add_token_safe(
                token_class, token_id, token_name, decimals_divisibility,
                error_callback=error_callback, allow_overwrite=allow_overwrite,
                write_storage=True):
            return False

        # Great success! Update GUI.
        self.token_list.update()
        self.update_token_type_combo()
        self.slp_history_list.update()
        return True

    def delete_slp_token(self, token_ids):
        if not self.question(_("Remove {} from your list of tokens?")
                             .format(" + ".join(token_ids))):
            return

        for tid in token_ids:
            self.wallet.token_types.pop(tid)
        
        self.token_list.update()
        self.update_token_type_combo()
        self.slp_history_list.update()
        self.wallet.save_transactions(True)

    def show_invoice(self, key):
        pr = self.invoices.get(key)
        if pr is None:
            self.show_error('Cannot find payment request in wallet.')
            return
        pr.verify(self.contacts)
        self.show_pr_details(pr)

    def show_pr_details(self, pr):
        key = pr.get_id()
        d = WindowModalDialog(self, _("Invoice"))
        vbox = QVBoxLayout(d)
        grid = QGridLayout()
        grid.addWidget(QLabel(_("Requestor") + ':'), 0, 0)
        grid.addWidget(QLabel(pr.get_requestor()), 0, 1)
        grid.addWidget(QLabel(_("Amount") + ':'), 1, 0)
        outputs_str = '\n'.join(map(lambda x: self.format_amount(x[2])+ self.base_unit() + ' @ ' + x[1], pr.get_outputs()))
        grid.addWidget(QLabel(outputs_str), 1, 1)
        expires = pr.get_expiration_date()
        grid.addWidget(QLabel(_("Memo") + ':'), 2, 0)
        grid.addWidget(QLabel(pr.get_memo()), 2, 1)
        grid.addWidget(QLabel(_("Signature") + ':'), 3, 0)
        grid.addWidget(QLabel(pr.get_verify_status()), 3, 1)
        if expires:
            grid.addWidget(QLabel(_("Expires") + ':'), 4, 0)
            grid.addWidget(QLabel(format_time(expires)), 4, 1)
        vbox.addLayout(grid)
        def do_export():
            fn = self.getSaveFileName(_("Save invoice to file"), "*.bip70")
            if not fn:
                return
            with open(fn, 'wb') as f:
                data = f.write(pr.raw)
            self.show_message(_('Invoice saved as' + ' ' + fn))
        exportButton = EnterButton(_('Save'), do_export)
        def do_delete():
            if self.question(_('Delete invoice?')):
                self.invoices.remove(key)
                self.history_list.update()
                self.invoice_list.update()
                d.close()
        deleteButton = EnterButton(_('Delete'), do_delete)
        vbox.addLayout(Buttons(exportButton, deleteButton, CloseButton(d)))
        d.exec_()

    def do_pay_invoice(self, key):
        pr = self.invoices.get(key)
        self.payment_request = pr
        self.prepare_for_payment_request()
        pr.error = None  # this forces verify() to re-run
        if pr.verify(self.contacts):
            self.payment_request_ok()
        else:
            self.payment_request_error()

    def create_console_tab(self):
        from .console import Console
        self.console = console = Console()
        return console

    def update_console(self):
        console = self.console
        console.history = self.config.get("console-history",[])
        console.history_index = len(console.history)

        console.updateNamespace({'wallet' : self.wallet,
                                 'network' : self.network,
                                 'plugins' : self.gui_object.plugins,
                                 'window': self})
        console.updateNamespace({'util' : util, 'bitcoin':bitcoin})

        c = commands.Commands(self.config, self.wallet, self.network, lambda: self.console.set_json(True))
        methods = {}
        def mkfunc(f, method):
            return lambda *args: f(method, args, self.password_dialog)
        for m in dir(c):
            if m[0]=='_' or m in ['network','wallet']: continue
            methods[m] = mkfunc(c._run, m)

        console.updateNamespace(methods)

    def create_status_bar(self):

        sb = QStatusBar()
        sb.setFixedHeight(35)
        qtVersion = qVersion()

        self.balance_label = QLabel("")
        sb.addWidget(self.balance_label)

        self._search_box_spacer = QWidget()
        self._search_box_spacer.setFixedWidth(6)  # 6 px spacer
        self.search_box = QLineEdit()
        self.search_box.setPlaceholderText(_("Search wallet, {key}F to hide").format(key='Ctrl+' if sys.platform != 'darwin' else '⌘'))
        self.search_box.textChanged.connect(self.do_search)
        self.search_box.hide()
        sb.addPermanentWidget(self.search_box, 1)

        self.addr_format_label = QLabel("")
        sb.addPermanentWidget(self.addr_format_label)

        self.lock_icon = QIcon()
        self.password_button = StatusBarButton(self.lock_icon, _("Password"), self.change_password_dialog )
        sb.addPermanentWidget(self.password_button)

        self.addr_converter_button = StatusBarButton(
            self.cashaddr_icon(),
            _("Toggle Zclassic Display"),
            self.toggle_cashaddr_status_bar
        )
        sb.addPermanentWidget(self.addr_converter_button)

        sb.addPermanentWidget(StatusBarButton(QIcon(":icons/preferences.png"), _("Preferences"), self.settings_dialog ) )
        self.seed_button = StatusBarButton(QIcon(":icons/seed.png"), _("Seed"), self.show_seed_dialog )
        sb.addPermanentWidget(self.seed_button)
        weekSelf = Weak(self)
        gui_object = self.gui_object
        self.status_button = StatusBarButton(QIcon(":icons/status_disconnected.png"), _("Network"), lambda: self.gui_object.show_network_dialog(self))
        sb.addPermanentWidget(self.status_button)
        run_hook('create_status_bar', sb)
        self.setStatusBar(sb)

    def update_lock_icon(self):
        icon = QIcon(":icons/lock.png") if self.wallet.has_password() else QIcon(":icons/unlock.png")
        self.password_button.setIcon(icon)

    def update_buttons_on_seed(self):
        self.seed_button.setVisible(self.wallet.has_seed())
        self.password_button.setVisible(self.wallet.may_have_password())
        self.send_button.setVisible(not self.wallet.is_watching_only())

    def change_password_dialog(self):
        from electrum_zclassic.storage import STO_EV_XPUB_PW
        if self.wallet.get_available_storage_encryption_version() == STO_EV_XPUB_PW:
            from .password_dialog import ChangePasswordDialogForHW
            d = ChangePasswordDialogForHW(self, self.wallet)
            ok, encrypt_file = d.run()
            if not ok:
                return

            try:
                hw_dev_pw = self.wallet.keystore.get_password_for_storage_encryption()
            except UserCancelled:
                return
            except BaseException as e:
                traceback.print_exc(file=sys.stderr)
                self.show_error(str(e))
                return
            old_password = hw_dev_pw if self.wallet.has_password() else None
            new_password = hw_dev_pw if encrypt_file else None
        else:
            from .password_dialog import ChangePasswordDialogForSW
            d = ChangePasswordDialogForSW(self, self.wallet)
            ok, old_password, new_password, encrypt_file = d.run()

        if not ok:
            return
        try:
            self.wallet.update_password(old_password, new_password, encrypt_file)
        except InvalidPassword as e:
            self.show_error(str(e))
            return
        except BaseException:
            traceback.print_exc(file=sys.stdout)
            self.show_error(_('Failed to update password'))
            return
        msg = _('Password was updated successfully') if self.wallet.has_password() else _('Password is disabled, this wallet is not protected')
        self.show_message(msg, title=_("Success"))
        self.update_lock_icon()

    def toggle_search(self):
        tab = self.tabs.currentWidget()
        #if hasattr(tab, 'searchable_list'):
        #    tab.searchable_list.toggle_toolbar()
        #return
        self.search_box.setHidden(not self.search_box.isHidden())
        if not self.search_box.isHidden():
            self.search_box.setFocus(1)
        else:
            self.do_search('')

    def do_search(self, t):
        tab = self.tabs.currentWidget()
        if hasattr(tab, 'searchable_list'):
            tab.searchable_list.filter(t)

    def new_contact_dialog(self):
        d = WindowModalDialog(self, _("New Contact"))
        vbox = QVBoxLayout(d)
        vbox.addWidget(QLabel(_('New Contact') + ':'))
        grid = QGridLayout()
        line1 = QLineEdit()
        line1.setFixedWidth(280)
        line2 = QLineEdit()
        line2.setFixedWidth(280)
        grid.addWidget(QLabel(_("Address")), 1, 0)
        grid.addWidget(line1, 1, 1)
        grid.addWidget(QLabel(_("Name")), 2, 0)
        grid.addWidget(line2, 2, 1)
        vbox.addLayout(grid)
        vbox.addLayout(Buttons(CancelButton(d), OkButton(d)))
        if d.exec_():
            self.set_contact(line2.text(), line1.text())

    def show_master_public_keys(self):
        dialog = WindowModalDialog(self, _("Wallet Information"))
        dialog.setMinimumSize(500, 100)
        mpk_list = self.wallet.get_master_public_keys()
        vbox = QVBoxLayout()
        wallet_type = self.wallet.storage.get('wallet_type', '')
        grid = QGridLayout()
        basename = os.path.basename(self.wallet.storage.path)
        grid.addWidget(QLabel(_("Wallet name")+ ':'), 0, 0)
        grid.addWidget(QLabel(basename), 0, 1)
        grid.addWidget(QLabel(_("Wallet type")+ ':'), 1, 0)
        grid.addWidget(QLabel(wallet_type), 1, 1)
        grid.addWidget(QLabel(_("Script type")+ ':'), 2, 0)
        grid.addWidget(QLabel(self.wallet.txin_type), 2, 1)
        vbox.addLayout(grid)
        if self.wallet.is_deterministic():
            mpk_text = ShowQRTextEdit()
            mpk_text.setMaximumHeight(150)
            mpk_text.addCopyButton(self.app)
            def show_mpk(index):
                mpk_text.setText(mpk_list[index])
            # only show the combobox in case multiple accounts are available
            if len(mpk_list) > 1:
                def label(key):
                    if isinstance(self.wallet, Multisig_Wallet):
                        return _("cosigner") + ' ' + str(key+1)
                    return ''
                labels = [label(i) for i in range(len(mpk_list))]
                on_click = lambda clayout: show_mpk(clayout.selected_index())
                labels_clayout = ChoicesLayout(_("Master Public Keys"), labels, on_click)
                vbox.addLayout(labels_clayout.layout())
            else:
                vbox.addWidget(QLabel(_("Master Public Key")))
            show_mpk(0)
            vbox.addWidget(mpk_text)
        vbox.addStretch(1)
        vbox.addLayout(Buttons(CloseButton(dialog)))
        dialog.setLayout(vbox)
        dialog.exec_()

    def remove_wallet(self):
        if self.question('\n'.join([
                _('Delete wallet file?'),
                "%s"%self.wallet.storage.path,
                _('If your wallet contains funds, make sure you have saved its seed.')])):
            self._delete_wallet()

    @protected
    def _delete_wallet(self, password):
        wallet_path = self.wallet.storage.path
        basename = os.path.basename(wallet_path)
        r = self.gui_object.daemon.delete_wallet(wallet_path)  # implicitly also calls stop_wallet
        self.close()
        self.update_recently_visited(wallet_path) # this ensures it's deleted from the menu
        if r:
            self.show_error(_("Wallet removed: {}").format(basename))
        else:
            self.show_error(_("Wallet file not found: {}").format(basename))

    @protected
    def show_seed_dialog(self, password):
        if not self.wallet.has_seed():
            self.show_message(_('This wallet has no seed'))
            return
        keystore = self.wallet.get_keystore()
        try:
            seed = keystore.get_seed(password)
            passphrase = keystore.get_passphrase(password)
        except BaseException as e:
            self.show_error(str(e))
            return
        from .seed_dialog import SeedDialog
        d = SeedDialog(self, seed, passphrase)
        d.exec_()

    def show_qrcode(self, data, title = _("QR code"), parent=None):
        if not data:
            return
        d = QRDialog(data, parent or self, title)
        d.exec_()

    @protected
    def show_private_key(self, address, password):
        if not address:
            return
        try:
            pk = self.wallet.export_private_key(address, password)
        except Exception as e:
            traceback.print_exc(file=sys.stdout)
            self.show_message(str(e))
            return
        xtype = bitcoin.deserialize_privkey(pk)[0]
        d = WindowModalDialog(self, _("Private key"))
        d.setMinimumSize(600, 150)
        vbox = QVBoxLayout()
        vbox.addWidget(QLabel(_("Address") + ': ' + address))
        vbox.addWidget(QLabel(_("Script type") + ': ' + xtype))
        vbox.addWidget(QLabel(_("Private key") + ':'))
        keys_e = ShowQRTextEdit(text=pk)
        keys_e.addCopyButton(self.app)
        vbox.addWidget(keys_e)
        vbox.addWidget(QLabel(_("Redeem Script") + ':'))
        rds_e = ShowQRTextEdit(text=address.to_script().hex())
        rds_e.addCopyButton(self.app)
        vbox.addWidget(rds_e)
        vbox.addLayout(Buttons(CloseButton(d)))
        d.setLayout(vbox)
        d.exec_()

    msg_sign = _("Signing with an address actually means signing with the corresponding "
                "private key, and verifying with the corresponding public key. The "
                "address you have entered does not have a unique public key, so these "
                "operations cannot be performed.") + '\n\n' + \
               _('The operation is undefined. Not just in Electrum, but in general.')

    @protected
    def do_sign(self, address, message, signature, password):
        address  = address.text().strip()
        message = message.toPlainText().strip()
        try:
            addr = Address.from_string(address)
        except:
            self.show_message(_('Invalid Zclassic address.'))
            return
        if self.wallet.is_watching_only():
            self.show_message(_('This is a watching-only wallet.'))
            return
        if not self.wallet.is_mine(addr):
            self.show_message(_('Address not in wallet.'))
            return
        if addr.kind != addr.ADDR_P2PKH:
            self.show_message(_('Cannot sign messages with this type of address:') + \
                              ' ' + txin_type + '\n\n' + self.msg_sign)
            return
        task = partial(self.wallet.sign_message, addr, message, password)

        def show_signed_message(sig):
            try:
                signature.setText(base64.b64encode(sig).decode('ascii'))
            except RuntimeError:
                # (signature) wrapped C/C++ object has been deleted
                pass

        self.wallet.thread.add(task, on_success=show_signed_message)

    def do_verify(self, address, message, signature):
        address  = address.text().strip()
        message = message.toPlainText().strip().encode('utf-8')
        if not bitcoin.is_address(address):
            self.show_message(_('Invalid Zclassic address.'))
            return
        try:
            # This can throw on invalid base64
            sig = base64.b64decode(str(signature.toPlainText()))
            verified = bitcoin.verify_message(address, sig, message)
        except Exception as e:
            verified = False
        if verified:
            self.show_message(_("Signature verified"))
        else:
            self.show_error(_("Wrong signature"))

    def sign_verify_message(self, address=None):
        d = WindowModalDialog(self, _('Sign/verify Message'))
        d.setMinimumSize(610, 290)

        layout = QGridLayout(d)

        message_e = QTextEdit()
        layout.addWidget(QLabel(_('Message')), 1, 0)
        layout.addWidget(message_e, 1, 1)
        layout.setRowStretch(2,3)

        address_e = QLineEdit()
        address_e.setText(address.to_ui_string() if address else '')
        layout.addWidget(QLabel(_('Address')), 2, 0)
        layout.addWidget(address_e, 2, 1)

        signature_e = QTextEdit()
        layout.addWidget(QLabel(_('Signature')), 3, 0)
        layout.addWidget(signature_e, 3, 1)
        layout.setRowStretch(3,1)

        hbox = QHBoxLayout()

        b = QPushButton(_("Sign"))
        b.clicked.connect(lambda: self.do_sign(address_e, message_e, signature_e))
        hbox.addWidget(b)

        b = QPushButton(_("Verify"))
        b.clicked.connect(lambda: self.do_verify(address_e, message_e, signature_e))
        hbox.addWidget(b)

        b = QPushButton(_("Close"))
        b.clicked.connect(d.accept)
        hbox.addWidget(b)
        layout.addLayout(hbox, 4, 1)
        d.exec_()

    @protected
    def do_decrypt(self, message_e, pubkey_e, encrypted_e, password):
        if self.wallet.is_watching_only():
            self.show_message(_('This is a watching-only wallet.'))
            return
        cyphertext = encrypted_e.toPlainText()
        task = partial(self.wallet.decrypt_message, pubkey_e.text(), cyphertext, password)

        def setText(text):
            try:
                message_e.setText(text.decode('utf-8'))
            except RuntimeError:
                # (message_e) wrapped C/C++ object has been deleted
                pass

        self.wallet.thread.add(task, on_success=setText)

    def do_encrypt(self, message_e, pubkey_e, encrypted_e):
        message = message_e.toPlainText()
        message = message.encode('utf-8')
        try:
            encrypted = bitcoin.encrypt_message(message, pubkey_e.text())
            encrypted_e.setText(encrypted.decode('ascii'))
        except BaseException as e:
            traceback.print_exc(file=sys.stdout)
            self.show_warning(str(e))

    def encrypt_message(self, address=None):
        d = WindowModalDialog(self, _('Encrypt/decrypt Message'))
        d.setMinimumSize(610, 490)

        layout = QGridLayout(d)

        message_e = QTextEdit()
        layout.addWidget(QLabel(_('Message')), 1, 0)
        layout.addWidget(message_e, 1, 1)
        layout.setRowStretch(2,3)

        pubkey_e = QLineEdit()
        if address:
            pubkey = self.wallet.get_public_key(address)
            if not isinstance(pubkey, str):
                pubkey = pubkey.to_ui_string()
            pubkey_e.setText(pubkey)
        layout.addWidget(QLabel(_('Public key')), 2, 0)
        layout.addWidget(pubkey_e, 2, 1)

        encrypted_e = QTextEdit()
        layout.addWidget(QLabel(_('Encrypted')), 3, 0)
        layout.addWidget(encrypted_e, 3, 1)
        layout.setRowStretch(3,1)

        hbox = QHBoxLayout()
        b = QPushButton(_("Encrypt"))
        b.clicked.connect(lambda: self.do_encrypt(message_e, pubkey_e, encrypted_e))
        hbox.addWidget(b)

        b = QPushButton(_("Decrypt"))
        b.clicked.connect(lambda: self.do_decrypt(message_e, pubkey_e, encrypted_e))
        hbox.addWidget(b)

        b = QPushButton(_("Close"))
        b.clicked.connect(d.accept)
        hbox.addWidget(b)

        layout.addLayout(hbox, 4, 1)
        d.exec_()

    def password_dialog(self, msg=None, parent=None):
        from .password_dialog import PasswordDialog
        parent = parent or self
        d = PasswordDialog(parent, msg)
        return d.run()

    def tx_from_text(self, txt):
        from electrum_zclassic.transaction import tx_from_str
        try:
            tx = tx_from_str(txt)
            return Transaction(tx)
        except BaseException as e:
            self.show_critical(_("Electrum-Zclassic was unable to parse your transaction") + ":\n" + str(e))
            return

    def read_tx_from_qrcode(self):
        from electrum_zclassic import qrscanner
        try:
            data = qrscanner.scan_barcode(self.config.get_video_device())
        except BaseException as e:
            self.show_error(str(e))
            return
        if not data:
            return
        # if the user scanned a zclassic URI
        if data.lower().startswith("zclassic:") or data.lower().startswith(constants.net.SLPADDR_PREFIX + ':'):
            self.pay_to_URI(data)
            return
        # else if the user scanned an offline signed tx
        try:
            data = bh2u(bitcoin.base_decode(data, length=None, base=43))
        except BaseException as e:
            self.show_error((_('Could not decode QR code')+':\n{}').format(e))
            return
        tx = self.tx_from_text(data)
        if not tx:
            return
        self.show_transaction(tx)

    def read_tx_from_file(self):
        fileName = self.getOpenFileName(_("Select your transaction file"), "*.txn")
        if not fileName:
            return
        try:
            with open(fileName, "r") as f:
                file_content = f.read()
        except (ValueError, IOError, os.error) as reason:
            self.show_critical(_("Electrum-Zclassic was unable to open your transaction file") + "\n" + str(reason), title=_("Unable to read file or no transaction found"))
            return
        return self.tx_from_text(file_content)

    def do_process_from_text(self):
        text = text_dialog(self, _('Input raw transaction'), _("Transaction:"), _("Load transaction"))
        if not text:
            return
        tx = self.tx_from_text(text)
        if tx:
            self.show_transaction(tx)

    def do_process_from_file(self):
        tx = self.read_tx_from_file()
        if tx:
            self.show_transaction(tx)

    def do_process_from_txid(self):
        from electrum_zclassic import transaction
        txid, ok = QInputDialog.getText(self, _('Lookup transaction'), _('Transaction ID') + ':')
        if ok and txid:
            txid = str(txid).strip()
            try:
                r = self.network.synchronous_get(('blockchain.transaction.get',[txid]))
            except BaseException as e:
                self.show_message(str(e))
                return
            tx = transaction.Transaction(r)
            self.show_transaction(tx)

    @protected
    def export_privkeys_dialog(self, password):
        if self.wallet.is_watching_only():
            self.show_message(_("This is a watching-only wallet"))
            return

        if isinstance(self.wallet, Multisig_Wallet):
            self.show_message(_('WARNING: This is a multi-signature wallet.') + '\n' +
                              _('It cannot be "backed up" by simply exporting these private keys.'))

        d = WindowModalDialog(self, _('Private keys'))
        d.setMinimumSize(980, 300)
        vbox = QVBoxLayout(d)

        msg = "%s\n%s\n%s" % (_("WARNING: ALL your private keys are secret."),
                              _("Exposing a single private key can compromise your entire wallet!"),
                              _("In particular, DO NOT use 'redeem private key' services proposed by third parties."))
        vbox.addWidget(QLabel(msg))

        e = QTextEdit()
        e.setReadOnly(True)
        vbox.addWidget(e)

        defaultname = 'electrum-zclassic-private-keys.csv'
        select_msg = _('Select file to export your private keys to')
        hbox, filename_e, csv_button = filename_field(self, self.config, defaultname, select_msg)
        vbox.addLayout(hbox)

        b = OkButton(d, _('Export'))
        b.setEnabled(False)
        vbox.addLayout(Buttons(CancelButton(d), b))

        private_keys = {}
        addresses = self.wallet.get_addresses()
        done = False
        cancelled = False
        def privkeys_thread():
            for addr in addresses:
                time.sleep(0.1)
                if done or cancelled:
                    break
                privkey = self.wallet.export_private_key(addr, password)
                private_keys[addr] = privkey
                self.computing_privkeys_signal.emit()
            if not cancelled:
                self.computing_privkeys_signal.disconnect()
                self.show_privkeys_signal.emit()

        def show_privkeys():
            s = "\n".join('{:45} {}'.format(addr.to_ui_string(), privkey)
                          for addr, privkey in private_keys.items())
            e.setText(s)
            b.setEnabled(True)
            self.show_privkeys_signal.disconnect()
            nonlocal done
            done = True

        def on_dialog_closed(*args):
            nonlocal done
            nonlocal cancelled
            if not done:
                cancelled = True
                self.computing_privkeys_signal.disconnect()
                self.show_privkeys_signal.disconnect()

        self.computing_privkeys_signal.connect(lambda: e.setText("Please wait... %d/%d"%(len(private_keys),len(addresses))))
        self.show_privkeys_signal.connect(show_privkeys)
        d.finished.connect(on_dialog_closed)
        threading.Thread(target=privkeys_thread).start()

        if not d.exec_():
            done = True
            return

        filename = filename_e.text()
        if not filename:
            return

        try:
            self.do_export_privkeys(filename, private_keys, csv_button.isChecked())
        except (IOError, os.error) as reason:
            txt = "\n".join([
                _("Electrum-Zclassic was unable to produce a private key-export."),
                str(reason)
            ])
            self.show_critical(txt, title=_("Unable to create csv"))

        except Exception as e:
            self.show_message(str(e))
            return

        self.show_message(_("Private keys exported."))

    def do_export_privkeys(self, fileName, pklist, is_csv):
        with open(fileName, "w+") as f:
            if is_csv:
                transaction = csv.writer(f)
                transaction.writerow(["address", "private_key"])
                for addr, pk in pklist.items():
                    transaction.writerow(["%34s"%addr,pk])
            else:
                import json
                f.write(json.dumps(pklist, indent = 4))

    def do_import_labels(self):
        def import_labels(path):
            def _validate(data):
                return data  # TODO

            def import_labels_assign(data):
                for key, value in data.items():
                    self.wallet.set_label(key, value)
            import_meta(path, _validate, import_labels_assign)

        def on_import():
            self.need_update.set()
        import_meta_gui(self, _('labels'), import_labels, on_import)

    def do_export_labels(self):
        def export_labels(filename):
            export_meta(self.wallet.labels, filename)
        export_meta_gui(self, _('labels'), export_labels)

    def sweep_key_dialog(self):
        d = WindowModalDialog(self, title=_('Sweep private keys'))
        d.setMinimumSize(600, 300)

        vbox = QVBoxLayout(d)
        vbox.addWidget(QLabel(_("Enter private keys:")))

        keys_e = ScanQRTextEdit(allow_multi=True)
        keys_e.setTabChangesFocus(True)
        vbox.addWidget(keys_e)

        addresses = self.wallet.get_unused_addresses()
        if not addresses:
            try:
                addresses = self.wallet.get_receiving_addresses()
            except AttributeError:
                addresses = self.wallet.get_addresses()
        h, address_e = address_field(addresses)
        vbox.addLayout(h)

        vbox.addStretch(1)
        button = OkButton(d, _('Sweep'))
        vbox.addLayout(Buttons(CancelButton(d), button))
        button.setEnabled(False)

        def get_address():
            addr = str(address_e.text()).strip()
            if bitcoin.is_address(addr):
                return addr

        def get_pk():
            text = str(keys_e.toPlainText())
            return keystore.get_private_keys(text)

        f = lambda: button.setEnabled(get_address() is not None and get_pk() is not None)
        on_address = lambda text: address_e.setStyleSheet((ColorScheme.DEFAULT if get_address() else ColorScheme.RED).as_stylesheet())
        keys_e.textChanged.connect(f)
        address_e.textChanged.connect(f)
        address_e.textChanged.connect(on_address)
        if not d.exec_():
            return
        from electrum_zclassic.wallet import sweep_preparations
        try:
            self.do_clear()
            coins, keypairs = sweep_preparations(get_pk(), self.network)
            self.tx_external_keypairs = keypairs
            self.spend_coins(coins)
            self.payto_e.setText(get_address())
            self.spend_max()
            self.payto_e.setFrozen(True)
            self.amount_e.setFrozen(True)
        except BaseException as e:
            self.show_message(str(e))
            return
        self.warn_if_watching_only()

    def _do_import(self, title, msg, func):
        text = text_dialog(self, title, msg + ' :', _('Import'),
                           allow_multi=True)
        if not text:
            return
        bad = []
        good = []
        for key in str(text).split():
            try:
                addr = func(key)
                good.append(addr)
            except BaseException as e:
                bad.append(key)
                continue
        if good:
            self.show_message(_("The following addresses were added") + ':\n' + '\n'.join(good))
        if bad:
            self.show_critical(_("The following inputs could not be imported") + ':\n'+ '\n'.join(bad))
        self.address_list.update()
        self.history_list.update()

    def import_addresses(self):
        if not self.wallet.can_import_address():
            return
        title, msg = _('Import addresses'), _("Enter addresses")
        self._do_import(title, msg, self.wallet.import_address)

    @protected
    def do_import_privkey(self, password):
        if not self.wallet.can_import_privkey():
            return
        title, msg = _('Import private keys'), _("Enter private keys")
        self._do_import(title, msg, lambda x: self.wallet.import_private_key(x, password))

    def update_fiat(self):
        b = self.fx and self.fx.is_enabled()
        self.fiat_send_e.setVisible(b)
        self.fiat_receive_e.setVisible(b)
        self.history_list.refresh_headers()
        self.history_list.update()
        self.address_list.refresh_headers()
        self.address_list.update()
        self.update_status()

    def cashaddr_icon(self):
        if self.config.get('addr_format', 0) == 1:
            return QIcon(":icons/tab_converter.svg")
        elif self.config.get('addr_format', 0)==2:
            return QIcon(":icons/tab_converter_slp.svg")
        else:
            return QIcon(":icons/tab_converter_bw.svg")

    def update_cashaddr_icon(self):
        self.addr_converter_button.setIcon(self.cashaddr_icon())

    def toggle_cashaddr_status_bar(self):
        self.toggle_cashaddr(self.config.get('addr_format', 2))

    def toggle_cashaddr_settings(self,state):
        self.toggle_cashaddr(state, True)

    def toggle_cashaddr(self, format, specified = False):
        #Gui toggle should just increment, if "specified" is True it is being set from preferences, so leave the value as is.
        if specified==False:
            if self.is_slp_wallet:
                max_format=1
            else:
                max_format=0
            format+=1
            if format > max_format:
                format=0
        self.config.set_key('addr_format', format)
        Address.show_cashaddr(format)
        self.setAddrFormatText(format)
        for window in self.gui_object.windows:
            window.cashaddr_toggled_signal.emit()

    def setAddrFormatText(self, format):
        try:
            if format == 0:
                self.addr_format_label.setText("Addr Format: Zclassic")
            else:
                self.addr_format_label.setText("Addr Format: ZSLP")
        except AttributeError:
            pass

    def settings_dialog(self):
        self.need_restart = False
        d = WindowModalDialog(self, _('Preferences'))
        vbox = QVBoxLayout()
        tabs = QTabWidget()
        gui_widgets = []
        fee_widgets = []
        tx_widgets = []
        id_widgets = []

        addr_format_choices = ["Zclassic Format","ZSLP Format"]
        addr_format_dict={'Zclassic Format':0,'ZSLP Format':1}
        msg = _('Choose which format the wallet displays for Zclassic addresses')
        addr_format_label = HelpLabel(_('Address Format') + ':', msg)
        addr_format_combo = QComboBox()
        addr_format_combo.addItems(addr_format_choices)
        addr_format_combo.setCurrentIndex(self.config.get("addr_format", 0))
        addr_format_combo.currentIndexChanged.connect(self.toggle_cashaddr_settings)

        gui_widgets.append((addr_format_label,addr_format_combo))
 
        # language
        lang_help = _('Select which language is used in the GUI (after restart).')
        lang_label = HelpLabel(_('Language') + ':', lang_help)
        lang_combo = QComboBox()
        from electrum_zclassic.i18n import languages
        lang_combo.addItems(list(languages.values()))
        try:
            index = languages.keys().index(self.config.get("language",''))
        except Exception:
            index = 0
        lang_combo.setCurrentIndex(index)
        if not self.config.is_modifiable('language'):
            for w in [lang_combo, lang_label]: w.setEnabled(False)
        def on_lang(x):
            lang_request = list(languages.keys())[lang_combo.currentIndex()]
            if lang_request != self.config.get('language'):
                self.config.set_key("language", lang_request, True)
                self.need_restart = True
        lang_combo.currentIndexChanged.connect(on_lang)
        gui_widgets.append((lang_label, lang_combo))

        nz_help = _('Number of zeros displayed after the decimal point. For example, if this is set to 2, "1." will be displayed as "1.00"')
        nz_label = HelpLabel(_('Zeros after decimal point') + ':', nz_help)
        nz = QSpinBox()
        nz.setMinimum(0)
        nz.setMaximum(self.decimal_point)
        nz.setValue(self.num_zeros)
        if not self.config.is_modifiable('num_zeros'):
            for w in [nz, nz_label]: w.setEnabled(False)
        def on_nz():
            value = nz.value()
            if self.num_zeros != value:
                self.num_zeros = value
                self.config.set_key('num_zeros', value, True)
                self.history_list.update()
                self.address_list.update()
        nz.valueChanged.connect(on_nz)
        gui_widgets.append((nz_label, nz))

        msg = '\n'.join([
            _('Time based: fee rate is based on average confirmation time estimates'),
            ]
        )
        fee_type_label = HelpLabel(_('Fee estimation') + ':', msg)
        fee_type_combo = QComboBox()
        fee_type_combo.addItems([_('Static'), _('ETA')])
        fee_type_combo.setCurrentIndex((2 if self.config.use_mempool_fees() else 1) if self.config.is_dynfee() else 0)
        def on_fee_type(x):
            self.config.set_key('mempool_fees', False)
            self.config.set_key('dynamic_fees', x>0)
            self.fee_slider.update()
        fee_type_combo.currentIndexChanged.connect(on_fee_type)
        fee_widgets.append((fee_type_label, fee_type_combo))

        feebox_cb = QCheckBox(_('Edit fees manually'))
        feebox_cb.setChecked(self.config.get('show_fee', True))
        feebox_cb.setToolTip(_("Show fee edit box in send tab."))
        def on_feebox(x):
            self.config.set_key('show_fee', x == Qt.Checked)
            self.fee_adv_controls.setVisible(bool(x))
        feebox_cb.stateChanged.connect(on_feebox)
        fee_widgets.append((feebox_cb, None))

        msg = _('OpenAlias record, used to receive coins and to sign payment requests.') + '\n\n'\
              + _('The following alias providers are available:') + '\n'\
              + '\n'.join(['https://cryptoname.co/', 'http://xmr.link']) + '\n\n'\
              + 'For more information, see https://openalias.org'
        alias_label = HelpLabel(_('OpenAlias') + ':', msg)
        alias = self.config.get('alias','')
        alias_e = QLineEdit(alias)
        def set_alias_color():
            if not self.config.get('alias'):
                alias_e.setStyleSheet("")
                return
            if self.alias_info:
                alias_addr, alias_name, validated = self.alias_info
                alias_e.setStyleSheet((ColorScheme.GREEN if validated else ColorScheme.RED).as_stylesheet(True))
            else:
                alias_e.setStyleSheet(ColorScheme.RED.as_stylesheet(True))
        def on_alias_edit():
            alias_e.setStyleSheet("")
            alias = str(alias_e.text())
            self.config.set_key('alias', alias, True)
            if alias:
                self.fetch_alias()
        set_alias_color()
        self.alias_received_signal.connect(set_alias_color)
        alias_e.editingFinished.connect(on_alias_edit)
        id_widgets.append((alias_label, alias_e))

        # SSL certificate
        msg = ' '.join([
            _('SSL certificate used to sign payment requests.'),
            _('Use setconfig to set ssl_chain and ssl_privkey.'),
        ])
        if self.config.get('ssl_privkey') or self.config.get('ssl_chain'):
            try:
                SSL_identity = paymentrequest.check_ssl_config(self.config)
                SSL_error = None
            except BaseException as e:
                SSL_identity = "error"
                SSL_error = str(e)
        else:
            SSL_identity = ""
            SSL_error = None
        SSL_id_label = HelpLabel(_('SSL certificate') + ':', msg)
        SSL_id_e = QLineEdit(SSL_identity)
        SSL_id_e.setStyleSheet((ColorScheme.RED if SSL_error else ColorScheme.GREEN).as_stylesheet(True) if SSL_identity else '')
        if SSL_error:
            SSL_id_e.setToolTip(SSL_error)
        SSL_id_e.setReadOnly(True)
        id_widgets.append((SSL_id_label, SSL_id_e))

        units = ['ZCL', 'mZCL', 'uZCL']
        msg = (_('Base unit of your wallet.')
               + '\n1 ZCL = 1000 mZCL. 1 mZCL = 1000 uZCL.\n'
               + _('This setting affects the Send tab, and all balance related fields.'))
        unit_label = HelpLabel(_('Base unit') + ':', msg)
        unit_combo = QComboBox()
        unit_combo.addItems(units)
        unit_combo.setCurrentIndex(units.index(self.base_unit()))
        def on_unit(x, nz):
            unit_result = units[unit_combo.currentIndex()]
            if self.base_unit() == unit_result:
                return
            edits = self.amount_e, self.fee_e, self.receive_amount_e
            amounts = [edit.get_amount() for edit in edits]
            if unit_result == 'ZCL':
                self.decimal_point = 8
            elif unit_result == 'mZCL':
                self.decimal_point = 5
            elif unit_result == 'uZCL':
                self.decimal_point = 2
            else:
                raise Exception('Unknown base unit')
            self.config.set_key('decimal_point', self.decimal_point, True)
            nz.setMaximum(self.decimal_point)
            self.history_list.update()
            self.request_list.update()
            self.address_list.update()
            for edit, amount in zip(edits, amounts):
                edit.setAmount(amount)
            self.update_status()
        unit_combo.currentIndexChanged.connect(lambda x: on_unit(x, nz))
        gui_widgets.append((unit_label, unit_combo))

        block_explorers = sorted(web.block_explorer_info().keys())
        msg = _('Choose which online block explorer to use for functions that open a web browser')
        block_ex_label = HelpLabel(_('Online Block Explorer') + ':', msg)
        block_ex_combo = QComboBox()
        block_ex_combo.addItems(block_explorers)
        block_ex_combo.setCurrentIndex(block_ex_combo.findText(web.block_explorer(self.config)))
        def on_be(x):
            be_result = block_explorers[block_ex_combo.currentIndex()]
            self.config.set_key('block_explorer', be_result, True)
        block_ex_combo.currentIndexChanged.connect(on_be)
        gui_widgets.append((block_ex_label, block_ex_combo))

        from electrum_zclassic import qrscanner
        system_cameras = qrscanner._find_system_cameras()
        qr_combo = QComboBox()
        qr_combo.addItem("Default","default")
        for camera, device in system_cameras.items():
            qr_combo.addItem(camera, device)
        #combo.addItem("Manually specify a device", config.get("video_device"))
        index = qr_combo.findData(self.config.get("video_device"))
        qr_combo.setCurrentIndex(index)
        msg = _("Install the zbar package to enable this.")
        qr_label = HelpLabel(_('Video Device') + ':', msg)
        qr_combo.setEnabled(qrscanner.libzbar is not None)
        on_video_device = lambda x: self.config.set_key("video_device", qr_combo.itemData(x), True)
        qr_combo.currentIndexChanged.connect(on_video_device)
        gui_widgets.append((qr_label, qr_combo))

        usechange_cb = QCheckBox(_('Use change addresses'))
        usechange_cb.setChecked(self.wallet.use_change)
        if not self.config.is_modifiable('use_change'): usechange_cb.setEnabled(False)
        def on_usechange(x):
            usechange_result = x == Qt.Checked
            if self.wallet.use_change != usechange_result:
                self.wallet.use_change = usechange_result
                self.wallet.storage.put('use_change', self.wallet.use_change)
                multiple_cb.setEnabled(self.wallet.use_change)
        usechange_cb.stateChanged.connect(on_usechange)
        usechange_cb.setToolTip(_('Using change addresses makes it more difficult for other people to track your transactions.'))
        tx_widgets.append((usechange_cb, None))

        def on_multiple(x):
            multiple = x == Qt.Checked
            if self.wallet.multiple_change != multiple:
                self.wallet.multiple_change = multiple
                self.wallet.storage.put('multiple_change', multiple)
        multiple_change = self.wallet.multiple_change
        multiple_cb = QCheckBox(_('Use multiple change addresses'))
        multiple_cb.setEnabled(self.wallet.use_change)
        multiple_cb.setToolTip('\n'.join([
            _('In some cases, use up to 3 change addresses in order to break '
              'up large coin amounts and obfuscate the recipient address.'),
            _('This may result in higher transactions fees.')
        ]))
        multiple_cb.setChecked(multiple_change)
        multiple_cb.stateChanged.connect(on_multiple)
        tx_widgets.append((multiple_cb, None))

        def fmt_docs(key, klass):
            lines = [ln.lstrip(" ") for ln in klass.__doc__.split("\n")]
            return '\n'.join([key, "", " ".join(lines)])

        choosers = sorted(coinchooser.COIN_CHOOSERS.keys())
        if len(choosers) > 1:
            chooser_name = coinchooser.get_name(self.config)
            msg = _('Choose coin (UTXO) selection method.  The following are available:\n\n')
            msg += '\n\n'.join(fmt_docs(*item) for item in coinchooser.COIN_CHOOSERS.items())
            chooser_label = HelpLabel(_('Coin selection') + ':', msg)
            chooser_combo = QComboBox()
            chooser_combo.addItems(choosers)
            i = choosers.index(chooser_name) if chooser_name in choosers else 0
            chooser_combo.setCurrentIndex(i)
            def on_chooser(x):
                chooser_name = choosers[chooser_combo.currentIndex()]
                self.config.set_key('coin_chooser', chooser_name)
            chooser_combo.currentIndexChanged.connect(on_chooser)
            tx_widgets.append((chooser_label, chooser_combo))

        def on_unconf(x):
            self.config.set_key('confirmed_only', bool(x))
        conf_only = self.config.get('confirmed_only', False)
        unconf_cb = QCheckBox(_('Spend only confirmed coins'))
        unconf_cb.setToolTip(_('Spend only confirmed inputs.'))
        unconf_cb.setChecked(conf_only)
        unconf_cb.stateChanged.connect(on_unconf)
        tx_widgets.append((unconf_cb, None))

        def on_outrounding(x):
            self.config.set_key('coin_chooser_output_rounding', bool(x))
        enable_outrounding = self.config.get('coin_chooser_output_rounding', False)
        outrounding_cb = QCheckBox(_('Enable output value rounding'))
        outrounding_cb.setToolTip(
            _('Set the value of the change output so that it has similar precision to the other outputs.') + '\n' +
            _('This might improve your privacy somewhat.') + '\n' +
            _('If enabled, at most 100 satoshis might be lost due to this, per transaction.'))
        outrounding_cb.setChecked(enable_outrounding)
        outrounding_cb.stateChanged.connect(on_outrounding)
        tx_widgets.append((outrounding_cb, None))

        # Fiat Currency
        hist_checkbox = QCheckBox()
        hist_capgains_checkbox = QCheckBox()
        fiat_address_checkbox = QCheckBox()
        ccy_combo = QComboBox()
        ex_combo = QComboBox()

        def on_opret(x):
            self.config.set_key('enable_opreturn', bool(x))
            if not x:
                self.message_opreturn_e.setText("")
                self.op_return_toolong = False
            self.message_opreturn_e.setHidden(not x)
            self.opreturn_rawhex_cb.setHidden(not x)
            self.opreturn_label.setHidden(not x)

        enable_opreturn = bool(self.config.get('enable_opreturn'))
        opret_cb = QCheckBox(_('Enable OP_RETURN output'))
        opret_cb.setToolTip(_('Enable posting messages with OP_RETURN.'))
        opret_cb.setChecked(enable_opreturn)
        opret_cb.stateChanged.connect(on_opret)
        tx_widgets.append((opret_cb,None))

        def on_slptok_pref(x):
            x = bool(x)
            self.config.set_key('enable_slp', x)

            wallet = self.wallet

            self.slp_amount_e.setHidden(not x)
            self.slp_max_button.setHidden(not x)
            self.token_type_combo.setHidden(not x)
            self.slp_amount_label.setHidden(not x)
            self.slp_token_type_label.setHidden(not x)

            if x:
                self.toggle_tab(self.slp_mgt_tab, 1)
                self.toggle_tab(self.slp_history_tab, 1)
                opret_cb.setChecked(False)
                opret_cb.setDisabled(True)
                self.config.set_key('enable_opreturn',False)
                self.toggle_cashaddr(2, True)
            else:
                self.toggle_tab(self.slp_mgt_tab, 2)
                self.toggle_tab(self.slp_history_tab, 2)
                opret_cb.setEnabled(True)
                self.slp_amount_e.setAmount(0)
                self.slp_amount_e.setText("")
                self.token_type_combo.setCurrentIndex(0)
                self.toggle_cashaddr(1, True)
            
            # wallet.activate_slp() if x else pass

            self.update_token_type_combo()
            self.update_cashaddr_icon()
            self.update_tabs()

        def update_currencies():
            if not self.fx: return
            currencies = sorted(self.fx.get_currencies(self.fx.get_history_config()))
            ccy_combo.clear()
            ccy_combo.addItems([_('None')] + currencies)
            if self.fx.is_enabled():
                ccy_combo.setCurrentIndex(ccy_combo.findText(self.fx.get_currency()))

        def update_history_cb():
            if not self.fx: return
            hist_checkbox.setChecked(self.fx.get_history_config())
            hist_checkbox.setEnabled(self.fx.is_enabled())

        def update_fiat_address_cb():
            if not self.fx: return
            fiat_address_checkbox.setChecked(self.fx.get_fiat_address_config())

        def update_history_capgains_cb():
            if not self.fx: return
            hist_capgains_checkbox.setChecked(self.fx.get_history_capital_gains_config())
            hist_capgains_checkbox.setEnabled(hist_checkbox.isChecked())

        def update_exchanges():
            if not self.fx: return
            b = self.fx.is_enabled()
            ex_combo.setEnabled(b)
            if b:
                h = self.fx.get_history_config()
                c = self.fx.get_currency()
                exchanges = self.fx.get_exchanges_by_ccy(c, h)
            else:
                exchanges = self.fx.get_exchanges_by_ccy('USD', False)
            ex_combo.clear()
            ex_combo.addItems(sorted(exchanges))
            ex_combo.setCurrentIndex(ex_combo.findText(self.fx.config_exchange()))

        def on_currency(hh):
            if not self.fx: return
            b = bool(ccy_combo.currentIndex())
            ccy = str(ccy_combo.currentText()) if b else None
            self.fx.set_enabled(b)
            if b and ccy != self.fx.ccy:
                self.fx.set_currency(ccy)
            update_history_cb()
            update_exchanges()
            self.update_fiat()

        def on_exchange(idx):
            exchange = str(ex_combo.currentText())
            if self.fx and self.fx.is_enabled() and exchange and exchange != self.fx.exchange.name():
                self.fx.set_exchange(exchange)

        def on_history(checked):
            if not self.fx: return
            self.fx.set_history_config(checked)
            update_exchanges()
            self.history_list.refresh_headers()
            self.slp_history_list.refresh_headers()
            if self.fx.is_enabled() and checked:
                # reset timeout to get historical rates
                self.fx.timeout = 0
            update_history_capgains_cb()

        def on_history_capgains(checked):
            if not self.fx: return
            self.fx.set_history_capital_gains_config(checked)
            self.history_list.refresh_headers()

        def on_fiat_address(checked):
            if not self.fx: return
            self.fx.set_fiat_address_config(checked)
            self.address_list.refresh_headers()
            self.address_list.update()

        update_currencies()
        update_history_cb()
        update_history_capgains_cb()
        update_fiat_address_cb()
        update_exchanges()
        ccy_combo.currentIndexChanged.connect(on_currency)
        hist_checkbox.stateChanged.connect(on_history)
        hist_capgains_checkbox.stateChanged.connect(on_history_capgains)
        fiat_address_checkbox.stateChanged.connect(on_fiat_address)
        ex_combo.currentIndexChanged.connect(on_exchange)

        fiat_widgets = []
        fiat_widgets.append((QLabel(_('Fiat currency')), ccy_combo))
        fiat_widgets.append((QLabel(_('Show history rates')), hist_checkbox))
        fiat_widgets.append((QLabel(_('Show capital gains in history')), hist_capgains_checkbox))
        fiat_widgets.append((QLabel(_('Show Fiat balance for addresses')), fiat_address_checkbox))
        fiat_widgets.append((QLabel(_('Source')), ex_combo))

        tabs_info = [
            (fee_widgets, _('Fees')),
            (tx_widgets, _('Transactions')),
            (gui_widgets, _('Appearance')),
            (fiat_widgets, _('Fiat')),
            (id_widgets, _('Identity')),
        ]
        for widgets, name in tabs_info:
            tab = QWidget()
            grid = QGridLayout(tab)
            grid.setColumnStretch(0,1)
            for a,b in widgets:
                i = grid.rowCount()
                if b:
                    if a:
                        grid.addWidget(a, i, 0)
                    grid.addWidget(b, i, 1)
                else:
                    grid.addWidget(a, i, 0, 1, 2)
            tabs.addTab(tab, name)

        vbox.addWidget(tabs)
        vbox.addStretch(1)
        vbox.addLayout(Buttons(CloseButton(d)))
        d.setLayout(vbox)

        # run the dialog
        d.exec_()

        if self.fx:
            self.fx.timeout = 0

        self.alias_received_signal.disconnect(set_alias_color)

        run_hook('close_settings_dialog')
        if self.need_restart:
            self.show_warning(_('Please restart Electrum-Zclassic to activate the new GUI settings'), title=_('Success'))


    def closeEvent(self, event):
        # It seems in some rare cases this closeEvent() is called twice
        if not self.cleaned_up:
            self.cleaned_up = True
            self.clean_up()
        event.accept()

    def clean_up_connections(self):
        def _disconnect_signals():
            for attr_name in dir(self):
                if attr_name.endswith("_signal"):
                    sig = getattr(self, attr_name)
                    if isinstance(sig, pyqtBoundSignal):
                        try:
                            sig.disconnect()
                            #self.print_error("Disconnected signal:",attr_name)
                        except TypeError: # no connections
                            pass
        def _disconnect_network_callbacks():
            if self.network:
                self.network.unregister_callback(self.on_network)
                self.network.unregister_callback(self.on_quotes)
                self.network.unregister_callback(self.on_history)
        # /
        _disconnect_network_callbacks()
        _disconnect_signals()

    def clean_up(self):
        self.wallet.thread.stop()
        self.clean_up_connections()
        self.config.set_key("is_maximized", self.isMaximized())
        if not self.isMaximized():
            g = self.geometry()
            self.wallet.storage.put("winpos-qt", [g.left(),g.top(),
                                                  g.width(),g.height()])
        self.config.set_key("console-history", self.console.history[-50:],
                            True)
        if self.qr_window:
            self.qr_window.close()
        self.close_wallet()
        self.gui_object.close_window(self)

    def plugins_dialog(self):
        self.pluginsdialog = d = WindowModalDialog(self, _('Electrum-Zclassic Plugins'))

        plugins = self.gui_object.plugins

        vbox = QVBoxLayout(d)

        # plugins
        scroll = QScrollArea()
        scroll.setEnabled(True)
        scroll.setWidgetResizable(True)
        scroll.setMinimumSize(400,250)
        vbox.addWidget(scroll)

        w = QWidget()
        scroll.setWidget(w)
        w.setMinimumHeight(plugins.count() * 35)

        grid = QGridLayout()
        grid.setColumnStretch(0,1)
        w.setLayout(grid)

        settings_widgets = {}

        def enable_settings_widget(p, name, i):
            widget = settings_widgets.get(name)
            if not widget and p and p.requires_settings():
                widget = settings_widgets[name] = p.settings_widget(d)
                grid.addWidget(widget, i, 1)
            if widget:
                widget.setEnabled(bool(p and p.is_enabled()))

        def do_toggle(cb, name, i):
            p = plugins.toggle(name)
            cb.setChecked(bool(p))
            enable_settings_widget(p, name, i)
            run_hook('init_qt', self.gui_object)

        for i, descr in enumerate(plugins.descriptions.values()):
            name = descr['__name__']
            p = plugins.get(name)
            if descr.get('registers_keystore'):
                continue
            try:
                cb = QCheckBox(descr['fullname'])
                plugin_is_loaded = p is not None
                cb_enabled = (not plugin_is_loaded and plugins.is_available(name, self.wallet)
                              or plugin_is_loaded and p.can_user_disable())
                cb.setEnabled(cb_enabled)
                cb.setChecked(plugin_is_loaded and p.is_enabled())
                grid.addWidget(cb, i, 0)
                enable_settings_widget(p, name, i)
                cb.clicked.connect(partial(do_toggle, cb, name, i))
                msg = descr['description']
                if descr.get('requires'):
                    msg += '\n\n' + _('Requires') + ':\n' + '\n'.join(map(lambda x: x[1], descr.get('requires')))
                grid.addWidget(HelpButton(msg), i, 2)
            except Exception:
                self.print_msg("error: cannot display plugin", name)
                traceback.print_exc(file=sys.stdout)
        grid.setRowStretch(len(plugins.descriptions.values()), 1)
        vbox.addLayout(Buttons(CloseButton(d)))
        d.exec_()

    def save_transaction_into_wallet(self, tx):
        try:
            if not self.wallet.add_transaction(tx.txid(), tx):
                self.show_error(_("Transaction could not be saved.") + "\n" +
                                       _("It conflicts with current history."))
                return False
        except AddTransactionException as e:
            self.show_error(e)
            return False
        else:
            self.wallet.save_transactions(write=True)
            # need to update at least: history_list, utxo_list, address_list
            self.need_update.set()
            self.msg_box(QPixmap(":icons/offline_tx.png"), None, _('Success'), _("Transaction added to wallet history"))
            return True

    def copy_to_clipboard(self, text, tooltip=None, widget=None):
        tooltip = tooltip or _("Text copied to clipboard")
        widget = widget or self
        qApp.clipboard().setText(text)
        QToolTip.showText(QCursor.pos(), tooltip, widget)

class TxUpdateMgr(QObject, PrintError):
    ''' Manages new transaction notifications and transaction verified
    notifications from the network thread. It collates them and sends them to
    the appropriate GUI controls in the main_window in an efficient manner. '''
    def __init__(self, main_window_parent):
        assert isinstance(main_window_parent, ElectrumWindow), "TxUpdateMgr must be constructed with an ElectrumWindow as its parent"
        super().__init__(main_window_parent)
        self.cleaned_up = False
        self.lock = threading.Lock()  # used to lock thread-shared attrs below
        # begin thread-shared attributes
        self.notif_q = []
        self.verif_q = []
        self.need_process_v, self.need_process_n = False, False
        # /end thread-shared attributes
        self.weakParent = Weak.ref(main_window_parent)
        main_window_parent.history_updated_signal.connect(self.verifs_get_and_clear, Qt.DirectConnection)  # immediately clear verif_q on history update because it would be redundant to keep the verify queue around after a history list update
        main_window_parent.on_timer_signal.connect(self.do_check, Qt.DirectConnection)  # hook into main_window's timer_actions function
        self.full_hist_refresh_timer = QTimer(self)
        self.full_hist_refresh_timer.setInterval(1000); self.full_hist_refresh_timer.setSingleShot(False)
        self.full_hist_refresh_timer.timeout.connect(self.schedule_full_hist_refresh_maybe)

    def diagnostic_name(self):
        return ((self.weakParent() and self.weakParent().diagnostic_name()) or "???") + "." + __class__.__name__

    def clean_up(self):
        self.cleaned_up = True
        main_window_parent = self.weakParent()  # weak -> strong ref
        if main_window_parent:
            try: main_window_parent.history_updated_signal.disconnect(self.verifs_get_and_clear)
            except TypeError: pass
            try: main_window_parent.on_timer_signal.disconnect(self.do_check)
            except TypeError: pass

    def do_check(self):
        ''' Called from timer_actions in main_window to check if notifs or
        verifs need to update the GUI.
          - Checks the need_process_[v|n] flags
          - If either flag is set, call the @rate_limited process_verifs
            and/or process_notifs functions which update GUI parent in a
            rate-limited (collated) fashion (for decent GUI responsiveness). '''
        with self.lock:
            bV, bN = self.need_process_v, self.need_process_n
            self.need_process_v, self.need_process_n = False, False
        if bV: self.process_verifs()  # rate_limited call (1 per second)
        if bN: self.process_notifs()  # rate_limited call (1 per 15 seconds)

    def verifs_get_and_clear(self):
        ''' Clears the verif_q. This is called from the network
        thread for the 'verified2' event as well as from the below
        update_verifs (GUI thread), hence the lock. '''
        with self.lock:
            ret = self.verif_q
            self.verif_q = []
            self.need_process_v = False
            return ret

    def notifs_get_and_clear(self):
        with self.lock:
            ret = self.notif_q
            self.notif_q = []
            self.need_process_n = False
            return ret

    def verif_add(self, args):
        # args: [wallet, tx_hash, height, conf, timestamp]
        # filter out tx's not for this wallet
        parent = self.weakParent()
        if not parent or parent.cleaned_up:
            return
        if args[0] is parent.wallet:
            with self.lock:
                self.verif_q.append(args[1:])
                self.need_process_v = True

    def notif_add(self, args):
        parent = self.weakParent()
        if not parent or parent.cleaned_up:
            return
        tx, wallet = args
        # filter out tx's not for this wallet
        if wallet is parent.wallet:
            with self.lock:
                self.notif_q.append(tx)
                self.need_process_n = True

    @rate_limited(1.0, ts_after=True)
    def process_verifs(self):
        ''' Update history list with tx's from verifs_q, but limit the
        GUI update rate to once per second. '''
        parent = self.weakParent()
        if not parent or parent.cleaned_up:
            return
        items = self.verifs_get_and_clear()
        if items:
            t0 = time.time()
            parent.history_list.setUpdatesEnabled(False)
            parent.slp_history_list.setUpdatesEnabled(False)
            had_sorting = [ parent.history_list.isSortingEnabled(),
                            parent.slp_history_list.isSortingEnabled() ]
            if had_sorting[0]:
                parent.history_list.setSortingEnabled(False)
            if had_sorting[1]:
                parent.slp_history_list.setSortingEnabled(False)
            n_updates = 0
            for item in items:
                did_update = parent.history_list.update_item(*item)
                parent.slp_history_list.update_item_netupdate(*item)
                n_updates += 1 if did_update else 0
            self.print_error("Updated {}/{} verified txs in GUI in {:0.2f} ms"
                             .format(n_updates, len(items), (time.time()-t0)*1e3))
            if had_sorting[0]:
                parent.history_list.setSortingEnabled(True)
            if had_sorting[1]:
                parent.slp_history_list.setSortingEnabled(True)
            parent.slp_history_list.setUpdatesEnabled(True)
            parent.history_list.setUpdatesEnabled(True)
            parent.update_status()
            if parent.history_list.has_unknown_balances:
                self.print_error("History tab: 'Unknown' balances detected, will schedule a GUI refresh after wallet settles")
                self._full_refresh_ctr = 0
                self.full_hist_refresh_timer.start()

    _full_refresh_ctr = 0
    def schedule_full_hist_refresh_maybe(self):
        ''' self.full_hist_refresh_timer timeout slot. May schedule a full
        history refresh after wallet settles if we have "Unknown" balances. '''
        parent = self.weakParent()
        if self._full_refresh_ctr > 60:
            # Too many retries. Give up.
            self.print_error("History tab: Full refresh scheduler timed out.. wallet hasn't settled in 1 minute. Giving up.")
            self.full_hist_refresh_timer.stop()
        elif parent and parent.history_list.has_unknown_balances:
            # Still have 'Unknown' balance. Check if wallet is settled.
            if self.need_process_v or not parent.wallet.is_fully_settled_down():
                # Wallet not fully settled down yet... schedule this function to run later
                self.print_error("History tab: Wallet not yet settled.. will try again in 1 second...")
            else:
                # Wallet has settled. Schedule an update. Note this function may be called again
                # in 1 second to check if the 'Unknown' situation has corrected itself.
                self.print_error("History tab: Wallet has settled down, latching need_update to true")
                parent.need_update.set()
            self._full_refresh_ctr += 1
        else:
            # No more polling is required. 'Unknown' balance disappeared from
            # GUI (or parent window was just closed).
            self.full_hist_refresh_timer.stop()
            self._full_refresh_ctr = 0

    @rate_limited(5.0, classlevel=True)
    def process_notifs(self):
        parent = self.weakParent()
        if not parent or parent.cleaned_up:
            return
        if parent.network:
            n_ok = 0
            txns = self.notifs_get_and_clear()
            if txns and parent.wallet.storage.get('gui_notify_tx', True):
                # Combine the transactions
                total_amount = 0
                tokens_included = set()
                for tx in txns:
                    if tx:
                        is_relevant, is_mine, v, fee = parent.wallet.get_wallet_delta(tx)
                        if is_relevant:
                            total_amount += v
                            n_ok += 1
                        if parent.is_slp_wallet:
                            try:
                                tti = parent.wallet.get_slp_token_info(tx.txid())
                                tokens_included.add(parent.wallet.token_types.get(tti['token_id'],{}).get('name','unknown'))
                            except KeyError:
                                pass
                if tokens_included:
                    tokstring = _('. Tokens included: ') + ', '.join(sorted(tokens_included))
                else:
                    tokstring = ''
                if total_amount > 0:
                    self.print_error("Notifying GUI %d tx"%(n_ok))
                    if n_ok > 1:
                        parent.notify(_("{} new transactions: {}{}")
                                    .format(n_ok, parent.format_amount_and_units(total_amount, is_diff=True), tokstring))
                    else:
                        parent.notify(_("New transaction: {}{}").format(parent.format_amount_and_units(total_amount, is_diff=True), tokstring))
