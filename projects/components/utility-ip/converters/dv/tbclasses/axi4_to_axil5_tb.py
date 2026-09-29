# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi4_to_axil5_tb
# Purpose: Testbench class for the axi4_to_axil5 converter (sideband contract)
#
# Author: sean galloway
# Created: 2026-09-05

"""Testbench for ``axi4_to_axil5`` -- the AXI5-Lite sideband contract.

What this does NOT re-test: burst decomposition, address incrementing,
response folding, data integrity. Those live in ``axi4_to_axil4_{rd,wr}``,
which this converter wraps unchanged, and they already have their own suites
(``test_axi4_to_axil4_rd.py`` / ``_wr.py``). Duplicating them here would buy
coverage of code this module does not contain.

What it DOES test is the only thing the wrapper adds -- where each AXI5-Lite
sideband signal gets its value:

* **FORWARDED** (``awlock``/``arlock``, ``awuser``/``aruser``, ``wuser``):
  carries the AXI4 value, and carries the value belonging to the burst the
  beat is part of.
* **TIED** (``awloop``, ``awmpam``, ``awmecid``, ``awnsaid``, ``awtrace``,
  ``wpoison``, and the AR equivalents): reads 0 on every beat, never X.
* **Gated off**: with ``ENABLE_*`` at 0 the corresponding signal reads 0 even
  when the AXI4 side is driving something non-zero.

The case worth spelling out is ``test_sideband_holds_across_a_burst``. The
core decomposes: one AXI4 AW handshake becomes N AXI5-Lite AW handshakes, and
``s_axi_awready`` drops as soon as the AW is accepted, so an AXI4 master is
free to present the NEXT transaction's AW while beats 2..N are still going
out. A combinational passthrough of the sideband therefore stamps those later
beats with the wrong USER -- which is what the first version of this RTL did.
Catching that needs two OVERLAPPING bursts with different USER values; two
sequential ones cannot see it, because nothing is driving the AXI4 AW during
the decomposition.

Known gap: the response-side return path (``m_axil_buser`` -> ``s_axi_buser``,
``m_axil_ruser`` -> ``s_axi_ruser``) is checked against a non-zero constant
installed as the B/R channel field default, because the AXIL5 slave BFM builds
its response packets with ``create_packet(resp=...)`` and has no hook for
per-transaction response sideband. A varying-value check needs that hook added
in RDS-DV first.
"""

import os
import sys

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead,
    AXI4MasterWrite,
)
from CocoTBFramework.components.axil5.axil5_interfaces import (
    AXIL5SlaveRead,
    AXIL5SlaveWrite,
)


# The wrapper ties these to zero on every beat: AXI4 has no source for them.
TIED_WRITE = ('awloop', 'awmpam', 'awmecid', 'awnsaid', 'awtrace', 'wpoison')
TIED_READ = ('arloop', 'armpam', 'armecid', 'arnsaid', 'artrace')

# Response sideband the slave returns, installed as a channel field default.
BUSER_CONST = 0x5
RUSER_CONST = 0xA


class AXI4ToAXIL5TB(TBBase):
    """Drives AXI4, completes AXI5-Lite, and audits the sideband between."""

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.axi_user_width = self.convert_to_int(os.environ.get('AXI_USER_WIDTH', '4'))
        self.user_width = self.convert_to_int(os.environ.get('USER_WIDTH', '4'))
        self.loop_width = self.convert_to_int(os.environ.get('LOOP_WIDTH', '3'))
        # ENABLE_USER / ENABLE_LOCK are elaboration parameters; the TB has to
        # know which build it is looking at to know what to expect.
        self.enable_user = self.convert_to_int(os.environ.get('ENABLE_USER', '1'))
        self.enable_lock = self.convert_to_int(os.environ.get('ENABLE_LOCK', '1'))

        self.errors = []
        self.aw_beats = []   # (awuser, awlock, awaddr) per AXI5-Lite AW handshake
        self.ar_beats = []
        self.w_beats = []    # (wuser,) per AXI5-Lite W handshake
        # s_axi_buser/ruser are combinational functions of the AXI5-Lite
        # response sideband, so they mean something only while the response
        # is on the wire. Sampled at the handshake, not read afterwards.
        self.b_user = []
        self.r_user = []

        self.axi4_wr = AXI4MasterWrite(
            dut=dut, clock=self.clk, prefix="s_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=self.axi_user_width,
            multi_sig=True,
        )
        self.axi4_rd = AXI4MasterRead(
            dut=dut, clock=self.clk, prefix="s_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=self.axi_user_width,
            multi_sig=True,
        )

        # Every optional group on, so an accidentally-undriven one shows up as
        # X rather than passing by absence.
        features = dict(
            user_width=self.user_width, trace=True, loop_width=self.loop_width,
            mpam_width=11, mecid_width=16, nsaid_width=4, poison=True,
            exclusive=True,
        )
        self.axil5_wr = AXIL5SlaveWrite(
            dut=dut, clock=self.clk, prefix="m_axil_", log=self.log,
            data_width=self.data_width, addr_width=self.addr_width,
            multi_sig=True, response_delay=1, **features,
        )
        self.axil5_rd = AXIL5SlaveRead(
            dut=dut, clock=self.clk, prefix="m_axil_", log=self.log,
            data_width=self.data_width, addr_width=self.addr_width,
            multi_sig=True, response_delay=1, **features,
        )

        # The slave BFM builds responses with create_packet(resp=...) and has
        # no per-transaction sideband hook, so pin the constants as the B/R
        # field defaults. That is the documented meaning of a FieldDefinition
        # default, not a poke at BFM internals.
        self._set_field_default(self.axil5_wr.b_channel, 'user', BUSER_CONST)
        self._set_field_default(self.axil5_rd.r_channel, 'user', RUSER_CONST)

        self.log.info(
            f"AXI4->AXI5-Lite TB: dw={self.data_width} aw={self.addr_width} "
            f"id={self.id_width} axi_user={self.axi_user_width} "
            f"user={self.user_width} ENABLE_USER={self.enable_user} "
            f"ENABLE_LOCK={self.enable_lock}"
        )

    @staticmethod
    def _set_field_default(channel, field_name, value):
        """Pin a channel field's default so generated packets carry it."""
        config = channel.field_config
        if field_name in config:
            config[field_name].default = value

    # ------------------------------------------------------------------
    # MANDATORY METHODS
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ------------------------------------------------------------------
    # Sideband audit
    # ------------------------------------------------------------------

    def _fail(self, message):
        self.errors.append(message)
        self.log.error(message)

    def _sample(self, name):
        """Read a DUT signal, reporting X/Z as a failure rather than a crash."""
        handle = getattr(self.dut, name)
        try:
            return int(handle.value)
        except ValueError:
            self._fail(f"{name} is X/Z -- a tied sideband signal must be driven")
            return None

    async def sideband_monitor(self):
        """Record the sideband on every AXI5-Lite AW/AR/W handshake.

        Tied signals are checked here, at the handshake, because that is the
        only moment their value is architecturally meaningful.
        """
        while True:
            await RisingEdge(self.clk)

            if self._hs('m_axil_aw'):
                self.aw_beats.append((
                    self._sample('m_axil_awuser'),
                    self._sample('m_axil_awlock'),
                    self._sample('m_axil_awaddr'),
                ))
                self._check_tied(TIED_WRITE[:-1])   # wpoison is a W-channel signal

            if self._hs('m_axil_ar'):
                self.ar_beats.append((
                    self._sample('m_axil_aruser'),
                    self._sample('m_axil_arlock'),
                    self._sample('m_axil_araddr'),
                ))
                self._check_tied(TIED_READ)

            if self._hs('m_axil_w'):
                self.w_beats.append((self._sample('m_axil_wuser'),))
                self._check_tied(('wpoison',))

            if self._hs('s_axi_b'):
                self.b_user.append(self._sample('s_axi_buser'))

            if self._hs('s_axi_r'):
                self.r_user.append(self._sample('s_axi_ruser'))

    def _hs(self, channel):
        """True when this channel handshakes on the current edge."""
        try:
            return (int(getattr(self.dut, f"{channel}valid").value) == 1
                    and int(getattr(self.dut, f"{channel}ready").value) == 1)
        except ValueError:
            return False

    def _check_tied(self, names):
        for name in names:
            value = self._sample(f"m_axil_{name}")
            if value not in (None, 0):
                self._fail(f"m_axil_{name} = 0x{value:X} on a handshake; "
                           f"it has no AXI4 source and must be tied to 0")

    # ------------------------------------------------------------------
    # Expectations
    # ------------------------------------------------------------------

    def expected_user(self, axi_user):
        """What the AXI5-Lite side should show for a given AXI4 USER value."""
        if not self.enable_user:
            return 0
        return axi_user & ((1 << self.user_width) - 1)

    def expected_lock(self, axi_lock):
        return axi_lock if self.enable_lock else 0

    def check_response_user(self, samples, label, constant):
        """The completer's USER must come back on the matching AXI4 channel."""
        want = (constant & ((1 << self.axi_user_width) - 1)) if self.enable_user else 0
        if not samples:
            self._fail(f"{label}: no response handshake was observed")
        for index, got in enumerate(samples):
            if got != want:
                self._fail(f"{label} response {index}: user=0x{got:X}, "
                           f"expected 0x{want:X}")

    def check_beats(self, beats, label, axi_user, axi_lock, count):
        """Every beat of one burst carries that burst's sideband."""
        want_user = self.expected_user(axi_user)
        want_lock = self.expected_lock(axi_lock)
        if len(beats) != count:
            self._fail(f"{label}: expected {count} beat(s), saw {len(beats)}")
        for index, (user, lock, addr) in enumerate(beats):
            if user != want_user:
                self._fail(f"{label} beat {index} (addr=0x{addr:X}): user="
                           f"0x{user:X}, expected 0x{want_user:X}")
            if lock != want_lock:
                self._fail(f"{label} beat {index} (addr=0x{addr:X}): lock="
                           f"{lock}, expected {want_lock}")
