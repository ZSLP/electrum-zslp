#!/usr/bin/env python
#
# Electrum - lightweight ZClassic client
# Copyright (C) 2015 Thomas Voegtlin
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
import webbrowser

from electrum_zclassic.i18n import _
from electrum_zclassic.web import block_explorer_URL
from electrum_zclassic.plugins import run_hook
from electrum_zclassic.address import Address

from .util import *


class AddressList(MyTreeWidget):
    filter_columns = [0, 1, 2]  # Address, Label, Balance

    def __init__(self, parent=None):
        MyTreeWidget.__init__(self, parent, self.create_menu, [], 2)
        self.refresh_headers()
        self.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.setSortingEnabled(True)
        self.show_change = 0
        self.show_used = 0
        self.change_button = QComboBox(self)
        self.change_button.currentIndexChanged.connect(self.toggle_change)
        for t in [_('All'), _('Receiving'), _('Change')]:
            self.change_button.addItem(t)
        self.used_button = QComboBox(self)
        self.used_button.currentIndexChanged.connect(self.toggle_used)
        for t in [_('All'), _('Unused'), _('Funded'), _('Used')]:
            self.used_button.addItem(t)

    def get_toolbar_buttons(self):
        return QLabel(_("Filter:")), self.change_button, self.used_button

    def on_hide_toolbar(self):
        self.show_change = 0
        self.show_used = 0
        self.update()

    def save_toolbar_state(self, state, config):
        config.set_key('show_toolbar_addresses', state)

    def refresh_headers(self):
        headers = [ _('Address'), _('Index'), _('Label'), _('Balance')]
        fx = self.parent.fx
        if fx and fx.get_fiat_address_config():
            headers.extend([_(fx.get_currency()+' Balance')])
        headers.extend([_('Tx')])
        self.update_headers(headers)

    def toggle_change(self, state):
        if state == self.show_change:
            return
        self.show_change = state
        self.update()

    def toggle_used(self, state):
        if state == self.show_used:
            return
        self.show_used = state
        self.update()

    def on_update(self):
        def item_path(item): # Recursively builds the path for an item eg 'parent_name/item_name'
            return item.text(0) if not item.parent() else item_path(item.parent()) + "/" + item.text(0)
        def remember_expanded_items(root):
            # Save the set of expanded items... so that address list updates don't annoyingly collapse
            # our tree list widget due to the update. This function recurses. Pass self.invisibleRootItem().
            expanded_item_names = set()
            for i in range(0, root.childCount()):
                it = root.child(i)
                if it and it.childCount():
                    if it.isExpanded():
                        expanded_item_names.add(item_path(it))
                    expanded_item_names |= remember_expanded_items(it) # recurse
            return expanded_item_names
        def restore_expanded_items(root, expanded_item_names):
            # Recursively restore the expanded state saved previously. Pass self.invisibleRootItem().
            for i in range(0, root.childCount()):
                it = root.child(i)
                if it and it.childCount():
                    restore_expanded_items(it, expanded_item_names) # recurse, do leaves first
                    old = bool(it.isExpanded())
                    new = bool(item_path(it) in expanded_item_names)
                    if old != new:
                        it.setExpanded(new)
        self.wallet = self.parent.wallet
        had_item_count = self.topLevelItemCount()
        sels = self.selectedItems()
        addresses_to_re_select = {item.data(0, Qt.UserRole) for item in sels}
        expanded_item_names = remember_expanded_items(self.invisibleRootItem())
        del sels  # avoid keeping reference to about-to-be delete C++ objects
        self.clear()
        # Note we take a shallow list-copy because we want to avoid
        # race conditions with the wallet while iterating here. The wallet may
        # touch/grow the returned lists at any time if a history comes (it
        # basically returns a reference to its own internal lists). The wallet
        # may then, in another thread such as the Synchronizer thread, grow
        # the receiving or change addresses on Deterministic wallets.  While
        # probably safe in a language like Python -- and especially since
        # the lists only grow at the end, we want to avoid bad habits.
        # The performance cost of the shallow copy below is negligible for 10k+
        # addresses even on huge wallets because, I suspect, internally CPython
        # does this type of operation extremely cheaply (probably returning
        # some copy-on-write-semantics handle to the same list).        
        receiving_addresses = list(self.wallet.get_receiving_addresses())
        change_addresses = list(self.wallet.get_change_addresses())

        if self.parent.fx and self.parent.fx.get_fiat_address_config():
            fx = self.parent.fx
        else:
            fx = None
        account_item = self
        sequences = [0,1] if change_addresses else [0]
        items_to_re_select = []
        for is_change in sequences:
            if len(sequences) > 1:
                name = _("Receiving") if not is_change else _("Change")
                seq_item = QTreeWidgetItem( [ name, '', '', '', ''] )
                account_item.addChild(seq_item)
                if not is_change and not had_item_count: # first time we create this widget, auto-expand the default address list
                    seq_item.setExpanded(True)
                    expanded_item_names.add(item_path(seq_item))
            else:
                seq_item = account_item
            used_item = QTreeWidgetItem( [ _("Used"), '', '', '', ''] )
            used_flag = False
            addr_list = change_addresses if is_change else receiving_addresses
            for n, address in enumerate(addr_list):
                num = len(self.wallet.get_address_history(address))
                is_used = self.wallet.is_used(address)
                balance = sum(self.wallet.get_addr_balance(address))
                address_text = address.to_ui_string()
                label = self.wallet.labels.get(address.to_storage_string(),'')
                balance_text = self.parent.format_amount(balance, whitespaces=True)
                columns = [address_text, str(n), label, balance_text, str(num)]
                if fx:
                    rate = fx.exchange_rate()
                    fiat_balance = fx.value_str(balance, rate)
                    columns.insert(4, fiat_balance)
                address_item = SortableTreeWidgetItem(columns)
                address_item.setTextAlignment(3, Qt.AlignRight)
                address_item.setFont(3, QFont(MONOSPACE_FONT))
                if fx:
                    address_item.setTextAlignment(4, Qt.AlignRight)
                    address_item.setFont(4, QFont(MONOSPACE_FONT))                

                address_item.setFont(0, QFont(MONOSPACE_FONT))
                address_item.setData(0, Qt.UserRole, address)
                address_item.setData(0, Qt.UserRole+1, True) # label can be edited
                if self.wallet.is_frozen(address):
                    address_item.setBackground(0, QColor('lightblue'))
                if self.wallet.is_beyond_limit(address, is_change):
                    address_item.setBackground(0, QColor('red'))
                if is_used:
                    if not used_flag:
                        seq_item.insertChild(0, used_item)
                        used_flag = True
                    used_item.addChild(address_item)
                else:
                    seq_item.addChild(address_item)
                if address in addresses_to_re_select:
                    items_to_re_select.append(address_item)

        for item in items_to_re_select:
            # NB: Need to select the item at the end becasue internally Qt does some index magic
            # to pick out the selected item and the above code mutates the TreeList, invalidating indices
            # and other craziness, which might produce UI glitches. See #1042
            item.setSelected(True)

        # Now, at the very end, enforce previous UI state with respect to what was expanded or not. See #1042
        restore_expanded_items(self.invisibleRootItem(), expanded_item_names)

    def create_menu(self, position):
        from electrum_zclassic.wallet import Multisig_Wallet
        is_multisig = isinstance(self.wallet, Multisig_Wallet)
        can_delete = self.wallet.can_delete_address()
        selected = self.selectedItems()
        multi_select = len(selected) > 1
        addrs = [item.data(0, Qt.UserRole) for item in selected]
        if not addrs:
            return
        if not multi_select:
            item = self.itemAt(position)
            col = self.currentColumn()
            if not item:
                return
            addr = addrs[0]
            if not isinstance(addr, Address):
                item.setExpanded(not item.isExpanded())
                return

        menu = QMenu()
        if not multi_select:
            column_title = self.headerItem().text(col)
            copy_text = item.text(col)
            menu.addAction(_("Copy {}").format(column_title), lambda: self.parent.app.clipboard().setText(copy_text))
            menu.addAction(_('Details'), lambda: self.parent.show_address(addr))
            if col in self.editable_columns:
                menu.addAction(_("Edit {}").format(column_title), lambda: self.editItem(item, col))
            menu.addAction(_("Request payment"), lambda: self.parent.receive_at(addr))
            if self.wallet.can_export():
                menu.addAction(_("Private key"), lambda: self.parent.show_private_key(addr))
            if not is_multisig and not self.wallet.is_watching_only():
                menu.addAction(_("Sign/verify message"), lambda: self.parent.sign_verify_message(addr))
                menu.addAction(_("Encrypt/decrypt message"), lambda: self.parent.encrypt_message(addr))
            if can_delete:
                menu.addAction(_("Remove from wallet"), lambda: self.parent.remove_address(addr))
            addr_URL = block_explorer_URL(self.config, 'addr', addr)
            if addr_URL:
                menu.addAction(_("View on block explorer"), lambda: webbrowser.open(addr_URL))

            if not self.wallet.is_frozen(addr):
                menu.addAction(_("Freeze"), lambda: self.parent.set_frozen_state([addr], True))
            else:
                menu.addAction(_("Unfreeze"), lambda: self.parent.set_frozen_state([addr], False))

        coins = self.wallet.get_spendable_coins(domain = addrs, config = self.config)
        if coins:
            menu.addAction(_("Spend from"), lambda: self.parent.spend_coins(coins))

        run_hook('receive_menu', menu, addrs, self.wallet)
        menu.exec_(self.viewport().mapToGlobal(position))

    def on_permit_edit(self, item, column):
        # labels for headings, e.g. "receiving" or "used" should not be editable
        return item.childCount() == 0
