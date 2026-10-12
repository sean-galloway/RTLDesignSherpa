# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: AXIS5ChkMixin
# Purpose: Drive and check the AXI5-Stream interface-parity check signals
# Subsystem: framework
#
# IHI 0051B ch. 5 (Check_Type = Odd_Parity_Byte_All). The parity arithmetic
# is the RDS-DV framework's (CocoTBFramework.components.axis5.axis5_check);
# this mixin only knows the DUT pin names, so the axis5 TBs share one copy.

from cocotb.triggers import ReadOnly, RisingEdge

from CocoTBFramework.components.axis5.axis5_check import (
    PAYLOAD_CHECK_FIELDS, odd_parity_chk, start_inverse_driver)


class AXIS5ChkMixin:
    """
    Check-signal helpers for an axis5 TB.

    Needs ``self.dut``, ``self.log`` and the DUT widths ``self.DATA_WIDTH``,
    ``self.ID_WIDTH``, ``self.DEST_WIDTH``, ``self.USER_WIDTH``.
    """

    def chk_widths(self):
        """Protected-signal width in bits per payload field (tied fields are 1 bit)."""
        return {
            'data': self.DATA_WIDTH,
            'strb': self.DATA_WIDTH // 8,
            'last': 1,
            'id':   max(self.ID_WIDTH, 1),
            'dest': max(self.DEST_WIDTH, 1),
            'user': max(self.USER_WIDTH, 1),
        }

    def _pin(self, name):
        return getattr(self.dut, name) if hasattr(self.dut, name) else None

    def drive_payload_chk(self, prefix, values, corrupt=None):
        """
        Drive ``{prefix}t<field>chk`` with the odd parity of ``values``.

        ``corrupt`` maps a field name to an XOR mask applied to its check.
        """
        corrupt = corrupt or {}
        widths = self.chk_widths()
        for name in PAYLOAD_CHECK_FIELDS:
            pin = self._pin(f'{prefix}t{name}chk')
            if pin is None:
                continue
            pin.value = odd_parity_chk(values.get(name, 0), widths[name]) ^ corrupt.get(name, 0)

    def payload_chk_mismatches(self, prefix):
        """
        Sample ``{prefix}t<field>`` and its check, return every piece that does
        NOT hold an odd number of ones (empty list = all odd).
        """
        bad = []
        widths = self.chk_widths()
        for name in PAYLOAD_CHECK_FIELDS:
            sig, chk = self._pin(f'{prefix}t{name}'), self._pin(f'{prefix}t{name}chk')
            if sig is None or chk is None:
                continue
            value, got = int(sig.value), int(chk.value)
            exp = odd_parity_chk(value, widths[name])
            if got != exp:
                bad.append(f'{prefix}t{name}chk=0x{got:X} expected 0x{exp:X} '
                           f'(t{name}=0x{value:X})')
        return bad

    def ctrl_chk_mismatches(self, prefix, signals=('valid', 'ready', 'wakeup')):
        """Single-bit checks: return each ``{prefix}t<sig>chk`` that is not ~t<sig>."""
        bad = []
        for sig in signals:
            s, c = self._pin(f'{prefix}t{sig}'), self._pin(f'{prefix}t{sig}chk')
            if s is None or c is None:
                continue
            if int(c.value) == int(s.value):
                bad.append(f'{prefix}t{sig}chk={int(c.value)} with t{sig}={int(s.value)}')
        return bad

    def start_chk_mirror(self, clock, prefix, signal):
        """Keep ``{prefix}t<signal>chk`` = ~``{prefix}t<signal>`` every cycle."""
        return start_inverse_driver(self.dut, clock, prefix, signal, self.log)

    async def drive_beat(self, clock, prefix, values, corrupt=None, timeout=200):
        """
        Drive one beat on ``{prefix}t*`` with its odd-parity checks and hold
        TVALID until the READY handshake. Returns True on handshake.
        """
        widths = self.chk_widths()
        for name, value in values.items():
            pin = self._pin(f'{prefix}t{name}')
            if pin is not None:
                pin.value = value & ((1 << widths.get(name, len(pin))) - 1)
        self.drive_payload_chk(prefix, values, corrupt)
        valid, ready = self._pin(f'{prefix}tvalid'), self._pin(f'{prefix}tready')
        valid.value = 1
        for _ in range(timeout):
            await ReadOnly()
            accepted = int(ready.value) == 1
            await RisingEdge(clock)
            if accepted:
                valid.value = 0
                return True
        valid.value = 0
        return False
