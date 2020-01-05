# -*- coding: utf-8 -*-

from PyQt5.QtCore import *
from PyQt5.QtGui import *
from PyQt5.QtWidgets import (QLineEdit, QStyle, QStyleOptionFrame)

from decimal import Decimal
from electrum_zclassic.util import format_satoshis_plain, format_satoshis_plain_nofloat, get_satoshis_nofloat


class MyLineEdit(QLineEdit):
    frozen = pyqtSignal()

    def setFrozen(self, b):
        self.setReadOnly(b)
        self.setFrame(not b)
        self.frozen.emit()

class AmountEdit(MyLineEdit):
    shortcut = pyqtSignal()

    def __init__(self, base_unit, is_int = False, parent=None):
        QLineEdit.__init__(self, parent)
        # This seems sufficient for hundred-BTC amounts with 8 decimals
        self.setFixedWidth(180)
        self.base_unit = base_unit
        self.textChanged.connect(self.numbify)
        self.is_int = is_int
        self.is_shortcut = False
        self.help_palette = QPalette()

    def decimal_point(self):
        return 8

    def numbify(self):
        text = self.text().strip()
        if text == '!':
            self.shortcut.emit()
            return
        pos = self.cursorPosition()
        chars = '0123456789'
        if not self.is_int: chars +='.'
        s = ''.join([i for i in text if i in chars])
        if not self.is_int:
            if '.' in s:
                p = s.find('.')
                s = s.replace('.','')
                s = s[:p] + '.' + s[p:p+self.decimal_point()]
        self.setText(s)
        # setText sets Modified to False.  Instead we want to remember
        # if updates were because of user modification.
        self.setModified(self.hasFocus())
        self.setCursorPosition(pos)

    def paintEvent(self, event):
        QLineEdit.paintEvent(self, event)
        if self.base_unit:
            panel = QStyleOptionFrame()
            self.initStyleOption(panel)
            textRect = self.style().subElementRect(QStyle.SE_LineEditContents, panel, self)
            textRect.adjust(2, 0, -10, 0)
            painter = QPainter(self)
            painter.setPen(self.help_palette.brush(QPalette.Disabled, QPalette.Text).color())
            painter.drawText(textRect, Qt.AlignRight | Qt.AlignVCenter, self.base_unit())

    def get_amount(self):
        try:
            return (int if self.is_int else Decimal)(str(self.text()))
        except:
            return None

    def setAmount(self, x):
        self.setText("%d"%x)


class SLPAmountEdit(AmountEdit):

    def __init__(self, token_name, token_decimals, is_int = False, parent=None):
        AmountEdit.__init__(self, self._base_unit, is_int, parent)
        self.set_token(token_name, token_decimals)

    def set_token(self, token_name, token_decimals):
        self.token_name = token_name
        self.token_decimals = token_decimals

    def _base_unit(self,):
        return self.token_name

    def decimal_point(self,):
        return self.token_decimals

    def get_amount(self):
        try:
            return get_satoshis_nofloat(str(self.text()), self.decimal_point())
        except:
            return None

    def setAmount(self, amount):
        if amount is None:
            self.setText(" ") # Space forces repaint in case units changed
        else:
            self.setText(format_satoshis_plain_nofloat(amount, self.decimal_point()))


class BTCAmountEdit(AmountEdit):

    def __init__(self, decimal_point, is_int = False, parent=None):
        AmountEdit.__init__(self, self._base_unit, is_int, parent)
        self.decimal_point = decimal_point

    def _base_unit(self):
        p = self.decimal_point()
        if p == 8:
            return 'ZCL'
        if p == 5:
            return 'mZCL'
        if p == 2:
            return 'uZCL'
        raise Exception('Unknown base unit')

    def get_amount(self):
        try:
            x = Decimal(str(self.text()))
        except:
            return None
        p = pow(10, self.decimal_point())
        return int( p * x )

    def setAmount(self, amount):
        if amount is None:
            self.setText(" ") # Space forces repaint in case units changed
        else:
            self.setText(format_satoshis_plain(amount, self.decimal_point()))


class FeerateEdit(BTCAmountEdit):
    def _base_unit(self):
        return 'sat/kB'

    def get_amount(self):
        sat_per_kb_amount = BTCAmountEdit.get_amount(self)
        if sat_per_kb_amount is None:
            return None
        return sat_per_kb_amount
