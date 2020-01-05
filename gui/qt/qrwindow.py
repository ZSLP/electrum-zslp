#!/usr/bin/env python
#
# Electrum - lightweight ZClassic client
# Copyright (C) 2014 Thomas Voegtlin
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

from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QHBoxLayout, QVBoxLayout, QWidget

from electrum_zclassic_gui.qt.qrcodewidget import QRCodeWidget
from electrum_zclassic.i18n import _

class QR_Window(QWidget):

    def __init__(self, win):
        QWidget.__init__(self)
        self.win = win
        self.setWindowTitle('Electrum-ZSLP - '+_('Payment Request'))
        self.setMinimumSize(800, 250)
        self.address = ''
        self.label = ''
        self.amount = 0
        self.setFocusPolicy(Qt.NoFocus)

        main_box = QHBoxLayout()

        self.qrw = QRCodeWidget()
        main_box.addWidget(self.qrw, 1)

        vbox = QVBoxLayout()
        main_box.addLayout(vbox)
        main_box.addStretch(1)

        self.address_label = WWLabel()
        self.address_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        vbox.addWidget(self.address_label)

        self.msg_label = WWLabel()
        self.msg_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        vbox.addWidget(self.msg_label)

        self.amount_label = WWLabel()
        self.amount_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        vbox.addWidget(self.amount_label)

        vbox.addStretch(1)
        self.setLayout(main_box)


    def set_content(self, address_text, amount, message, url):
        self.address_label.setText(address_text)
        if amount:
            amount_text = '{} {}'.format(self.win.format_amount(amount), self.win.base_unit())
        else:
            amount_text = ''
        self.amount_label.setText(amount_text)
        self.msg_label.setText(message)
        self.qrw.setData(url)
