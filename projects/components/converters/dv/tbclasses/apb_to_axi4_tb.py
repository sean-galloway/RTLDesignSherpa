# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: apb_to_axi4_tb
# Purpose: Testbench class for apb4_to_axi4 / apb5_to_axi4 (APB completer in,
#          AXI4 requester out)
#
# Author: sean galloway
# Created: 2026-09-11

"""Testbench for ``apb4_to_axi4`` and ``apb5_to_axi4``.

One class for both: the two converters differ only in the APB sideband, and
``APB_PROTOCOL`` in the environment picks the requester BFM. An APB master
BFM drives the converter's completer surface; memory-backed AXI4 slave BFMs
sit on its requester surface; a monitor samples the AXI4 request channels at
every handshake.

What is checked, and why each check is there:

* **Data round trip** -- an APB write lands in the AXI4 slave's memory at the
  same address, and an APB read returns what the memory holds. The memory
  model is read directly as well as through a second APB transfer, so a
  converter that echoed its own write data would still be caught.
* **Single-beat shape** -- every AW/AR carries ``len=0``, ``size`` = the full
  data width, ``burst=INCR``, the constant ID, and every W has ``wlast=1``.
  These are the fields the converter invents; nothing upstream checks them.
* **PPROT** travels to ``AxPROT`` and ``PSTRB`` to ``WSTRB`` -- verified
  with partial writes against a byte-accurate shadow of the memory.
* **Error folding** -- an address past the slave's memory is answered SLVERR
  (the shared out-of-range contract) and must come back as ``PSLVERR=1``,
  with nothing written, and the port must keep working afterwards.
* **APB5 USER** -- ``PAUSER``/``PWUSER`` reach ``awuser``/``aruser``/``wuser``
  (low bits, per the size-cast contract) and the completer's ``buser``/
  ``ruser`` come back on ``PBUSER``/``PRUSER``. The AXI4 slave BFM has no
  per-transaction response-sideband hook, so the response constants are
  pinned as the B/R channel field defaults, the same way the AXIL5 shim TB
  does it.
* **Backpressure** -- a slow slave (large response delay) exercises the
  hold-until-ready on AW/W/AR and the PREADY wait on the APB side.
"""

import os
import random
import sys

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb5.apb5_components import APB5Master
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4SlaveRead,
    AXI4SlaveWrite,
)
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Response sideband the AXI4 completer returns, installed as field defaults.
BUSER_CONST = 0x5
RUSER_CONST = 0xA


class APBToAXI4TB(TBBase):
    """Drives APB4/APB5, completes AXI4, and audits the requester between."""

    MEM_LINES = 256

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.protocol = os.environ.get('APB_PROTOCOL', 'apb4').lower()
        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '1'))
        self.axi_user_width = self.convert_to_int(os.environ.get('AXI_USER_WIDTH', '1'))
        self.apb_user_width = self.convert_to_int(os.environ.get('APB_USER_WIDTH', '4'))
        self.default_id = self.convert_to_int(os.environ.get('DEFAULT_ID', '0'))
        self.slave_delay = self.convert_to_int(os.environ.get('SLAVE_DELAY', '1'))

        self.bytes_per_beat = self.data_width // 8
        self.axsize = self.bytes_per_beat.bit_length() - 1
        self.data_mask = (1 << self.data_width) - 1
        self.axi_user_mask = (1 << self.axi_user_width) - 1
        self.apb_user_mask = (1 << self.apb_user_width) - 1
        self.mem_bytes = self.MEM_LINES * self.bytes_per_beat

        self.errors = []
        self.aw_beats = []   # (addr, prot, user)
        self.ar_beats = []
        self.w_beats = []    # (strb, user)
        self.shadow = bytearray(self.mem_bytes)

        if self.protocol == 'apb5':
            self.apb = APB5Master(
                entity=dut, title="APB5_M", prefix="s_apb", clock=self.clk,
                bus_width=self.data_width, addr_width=self.addr_width,
                auser_width=self.apb_user_width, wuser_width=self.apb_user_width,
                ruser_width=self.apb_user_width, buser_width=self.apb_user_width,
                log=self.log,
            )
        else:
            self.apb = APBMaster(
                entity=dut, title="APB_M", prefix="s_apb", clock=self.clk,
                bus_width=self.data_width, addr_width=self.addr_width,
                log=self.log,
            )

        self.mem = MemoryModel(num_lines=self.MEM_LINES,
                               bytes_per_line=self.bytes_per_beat, log=self.log)

        self.axi_wr = AXI4SlaveWrite(
            dut=dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=self.axi_user_width,
            multi_sig=True, memory_model=self.mem,
            response_delay=self.slave_delay,
        )
        self.axi_rd = AXI4SlaveRead(
            dut=dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=self.axi_user_width,
            multi_sig=True, memory_model=self.mem,
            response_delay=self.slave_delay,
        )
        self._set_field_default(self.axi_wr.b_channel, 'user',
                                BUSER_CONST & self.axi_user_mask)
        self._set_field_default(self.axi_rd.r_channel, 'user',
                                RUSER_CONST & self.axi_user_mask)

        self.log.info(
            f"APB->AXI4 TB: protocol={self.protocol} dw={self.data_width} "
            f"aw={self.addr_width} id={self.id_width} axi_user={self.axi_user_width} "
            f"apb_user={self.apb_user_width} slave_delay={self.slave_delay}"
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
    # Requester audit
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
            self._fail(f"{name} is X/Z at a handshake")
            return None

    def _hs(self, channel):
        try:
            return (int(getattr(self.dut, f"{channel}valid").value) == 1
                    and int(getattr(self.dut, f"{channel}ready").value) == 1)
        except ValueError:
            return False

    def _check_single_beat(self, chan):
        """The fields the converter invents on every AW/AR."""
        want = {
            f"m_axi_{chan}len": 0,
            f"m_axi_{chan}size": self.axsize,
            f"m_axi_{chan}burst": 1,
            f"m_axi_{chan}id": self.default_id,
            f"m_axi_{chan}lock": 0,
            f"m_axi_{chan}qos": 0,
            f"m_axi_{chan}region": 0,
        }
        for name, expect in want.items():
            got = self._sample(name)
            if got is not None and got != expect:
                self._fail(f"{name} = {got} on a handshake, expected {expect}")

    async def axi_monitor(self):
        """Record and check the AXI4 request channels on every handshake."""
        while True:
            await RisingEdge(self.clk)
            if self._hs('m_axi_aw'):
                self._check_single_beat('aw')
                self.aw_beats.append((self._sample('m_axi_awaddr'),
                                      self._sample('m_axi_awprot'),
                                      self._sample('m_axi_awuser')))
            if self._hs('m_axi_w'):
                if self._sample('m_axi_wlast') != 1:
                    self._fail("m_axi_wlast = 0 on a W handshake; every write is one beat")
                self.w_beats.append((self._sample('m_axi_wstrb'),
                                     self._sample('m_axi_wuser')))
            if self._hs('m_axi_ar'):
                self._check_single_beat('ar')
                self.ar_beats.append((self._sample('m_axi_araddr'),
                                      self._sample('m_axi_arprot'),
                                      self._sample('m_axi_aruser')))

    # ------------------------------------------------------------------
    # APB helpers
    # ------------------------------------------------------------------

    def _rand_user(self, rng):
        return rng.randrange(1 << self.apb_user_width) if self.protocol == 'apb5' else 0

    def expected_axi_user(self, apb_user):
        """Low bits travel (size cast); APB4 has no USER and drives 0."""
        if self.protocol != 'apb5':
            return 0
        return apb_user & self.axi_user_mask

    def expected_apb_user(self, axi_const):
        """What PRUSER/PBUSER show for the completer's constant."""
        return (axi_const & self.axi_user_mask) & self.apb_user_mask

    async def apb_write(self, addr, data, strb=None, pprot=0, pauser=0, pwuser=0):
        if self.protocol == 'apb5':
            txn = await self.apb.write(addr, data, strb=strb, pprot=pprot,
                                       pauser=pauser, pwuser=pwuser)
        else:
            txn = await self.apb.write(addr, data, strb=strb, pprot=pprot)
        return txn

    async def apb_read(self, addr, pprot=0, pauser=0):
        if self.protocol == 'apb5':
            txn = await self.apb.read(addr, pprot=pprot, pauser=pauser)
        else:
            txn = await self.apb.read(addr, pprot=pprot)
        return txn

    def _shadow_write(self, addr, data, strb):
        for b in range(self.bytes_per_beat):
            if (strb >> b) & 1:
                self.shadow[addr + b] = (data >> (8 * b)) & 0xFF

    def _shadow_read(self, addr):
        return int.from_bytes(bytes(self.shadow[addr:addr + self.bytes_per_beat]), 'little')

    def _mem_read(self, addr):
        return int.from_bytes(bytes(self.mem.read(addr, self.bytes_per_beat)), 'little')

    def _rand_addr(self, rng):
        return rng.randrange(0, self.mem_bytes, self.bytes_per_beat)

    # ------------------------------------------------------------------
    # Phases
    # ------------------------------------------------------------------

    async def run_write_read(self, count, rng):
        """Full-width write, check memory, read back, check PPROT/USER."""
        for i in range(count):
            addr = self._rand_addr(rng)
            data = rng.getrandbits(self.data_width)
            prot = rng.randrange(8)
            auser = self._rand_user(rng)
            wuser = self._rand_user(rng)
            n_aw, n_w, n_ar = len(self.aw_beats), len(self.w_beats), len(self.ar_beats)

            txn = await self.apb_write(addr, data, pprot=prot, pauser=auser, pwuser=wuser)
            self._shadow_write(addr, data, (1 << self.bytes_per_beat) - 1)
            if txn.fields['pslverr']:
                self._fail(f"write {i} @0x{addr:X}: PSLVERR on an in-range write")
            got = self._mem_read(addr)
            if got != data:
                self._fail(f"write {i} @0x{addr:X}: memory holds 0x{got:X}, wrote 0x{data:X}")
            if len(self.aw_beats) != n_aw + 1 or len(self.w_beats) != n_w + 1:
                self._fail(f"write {i}: expected exactly one AW and one W handshake "
                           f"(saw +{len(self.aw_beats)-n_aw} AW, +{len(self.w_beats)-n_w} W)")
            else:
                aw_addr, aw_prot, aw_user = self.aw_beats[-1]
                _w_strb, w_user = self.w_beats[-1]
                if aw_addr != addr:
                    self._fail(f"write {i}: awaddr 0x{aw_addr:X} != PADDR 0x{addr:X}")
                if aw_prot != prot:
                    self._fail(f"write {i}: awprot {aw_prot} != PPROT {prot}")
                if aw_user != self.expected_axi_user(auser):
                    self._fail(f"write {i}: awuser 0x{aw_user:X} != expected "
                               f"0x{self.expected_axi_user(auser):X} (PAUSER 0x{auser:X})")
                if w_user != self.expected_axi_user(wuser):
                    self._fail(f"write {i}: wuser 0x{w_user:X} != expected "
                               f"0x{self.expected_axi_user(wuser):X} (PWUSER 0x{wuser:X})")
            if self.protocol == 'apb5':
                want = self.expected_apb_user(BUSER_CONST)
                if txn.fields.get('pbuser', 0) != want:
                    self._fail(f"write {i}: PBUSER 0x{txn.fields.get('pbuser', 0):X}, "
                               f"expected 0x{want:X}")

            rtxn = await self.apb_read(addr, pprot=prot, pauser=auser)
            rdata = rtxn.fields['prdata']
            if rtxn.fields['pslverr']:
                self._fail(f"read {i} @0x{addr:X}: PSLVERR on an in-range read")
            if rdata != data:
                self._fail(f"read {i} @0x{addr:X}: PRDATA 0x{rdata:X}, expected 0x{data:X}")
            if len(self.ar_beats) != n_ar + 1:
                self._fail(f"read {i}: expected exactly one AR handshake "
                           f"(saw +{len(self.ar_beats)-n_ar})")
            else:
                ar_addr, ar_prot, ar_user = self.ar_beats[-1]
                if ar_addr != addr:
                    self._fail(f"read {i}: araddr 0x{ar_addr:X} != PADDR 0x{addr:X}")
                if ar_prot != prot:
                    self._fail(f"read {i}: arprot {ar_prot} != PPROT {prot}")
                if ar_user != self.expected_axi_user(auser):
                    self._fail(f"read {i}: aruser 0x{ar_user:X} != expected "
                               f"0x{self.expected_axi_user(auser):X}")
            if self.protocol == 'apb5':
                want = self.expected_apb_user(RUSER_CONST)
                if rtxn.fields.get('pruser', 0) != want:
                    self._fail(f"read {i}: PRUSER 0x{rtxn.fields.get('pruser', 0):X}, "
                               f"expected 0x{want:X}")

    async def run_strobes(self, count, rng):
        """Partial writes: PSTRB must become WSTRB and only those lanes change."""
        for i in range(count):
            addr = self._rand_addr(rng)
            data = rng.getrandbits(self.data_width)
            strb = rng.randrange(1, 1 << self.bytes_per_beat)
            n_w = len(self.w_beats)
            txn = await self.apb_write(addr, data, strb=strb)
            self._shadow_write(addr, data, strb)
            if txn.fields['pslverr']:
                self._fail(f"strobe write {i} @0x{addr:X}: PSLVERR")
            if len(self.w_beats) == n_w + 1:
                w_strb, _ = self.w_beats[-1]
                if w_strb != strb:
                    self._fail(f"strobe write {i}: WSTRB 0x{w_strb:X} != PSTRB 0x{strb:X}")
            got, want = self._mem_read(addr), self._shadow_read(addr)
            if got != want:
                self._fail(f"strobe write {i} @0x{addr:X} strb=0x{strb:X}: memory "
                           f"0x{got:X}, expected 0x{want:X}")
            rtxn = await self.apb_read(addr)
            if rtxn.fields['prdata'] != want:
                self._fail(f"strobe read {i} @0x{addr:X}: PRDATA 0x{rtxn.fields['prdata']:X}, "
                           f"expected 0x{want:X}")

    async def run_errors(self, count, rng):
        """Out-of-range: SLVERR from the completer folds to PSLVERR, nothing
        written, and the port keeps working."""
        for i in range(count):
            bad = self.mem_bytes + rng.randrange(0, self.mem_bytes, self.bytes_per_beat)
            data = rng.getrandbits(self.data_width)
            txn = await self.apb_write(bad, data)
            if not txn.fields['pslverr']:
                self._fail(f"error write {i} @0x{bad:X}: PSLVERR not set on an "
                           f"out-of-range write")
            rtxn = await self.apb_read(bad)
            if not rtxn.fields['pslverr']:
                self._fail(f"error read {i} @0x{bad:X}: PSLVERR not set on an "
                           f"out-of-range read")
            # In-range memory is untouched and the port still answers.
            probe = self._rand_addr(rng)
            got, want = self._mem_read(probe), self._shadow_read(probe)
            if got != want:
                self._fail(f"error {i}: in-range 0x{probe:X} changed to 0x{got:X} "
                           f"(expected 0x{want:X}) around an out-of-range access")
            good = rng.getrandbits(self.data_width)
            gtxn = await self.apb_write(probe, good)
            self._shadow_write(probe, good, (1 << self.bytes_per_beat) - 1)
            if gtxn.fields['pslverr']:
                self._fail(f"error {i}: in-range write after an error answered PSLVERR")
            grtxn = await self.apb_read(probe)
            if grtxn.fields['prdata'] != good or grtxn.fields['pslverr']:
                self._fail(f"error {i}: port did not recover after an out-of-range "
                           f"access (read 0x{grtxn.fields['prdata']:X}, "
                           f"err {grtxn.fields['pslverr']})")

    async def run_backpressure(self, count, rng, delay):
        """A slow completer: AW/W/AR are held to their handshakes, PREADY waits."""
        self.axi_wr.response_delay_cycles = delay
        self.axi_rd.response_delay_cycles = delay
        try:
            await self.run_write_read(count, rng)
        finally:
            self.axi_wr.response_delay_cycles = self.slave_delay
            self.axi_rd.response_delay_cycles = self.slave_delay

    # ------------------------------------------------------------------
    # Suites
    # ------------------------------------------------------------------

    async def run_suite(self, level, seed):
        rng = random.Random(seed)
        plan = {
            'gate': dict(rw=8, strobes=0, errors=2, bp=0),
            'func': dict(rw=30, strobes=20, errors=4, bp=8),
            'full': dict(rw=100, strobes=60, errors=10, bp=30),
        }[level]
        self.log.info(f"APB->AXI4 {level.upper()} plan: {plan}")
        await self.run_write_read(plan['rw'], rng)
        if plan['strobes']:
            await self.run_strobes(plan['strobes'], rng)
        await self.run_errors(plan['errors'], rng)
        if plan['bp']:
            await self.run_backpressure(plan['bp'], rng, delay=12)
        self.log.info(
            f"observed AW={len(self.aw_beats)} W={len(self.w_beats)} "
            f"AR={len(self.ar_beats)} errors={len(self.errors)}")
        # A monitor that saw nothing is not a passing monitor.
        if not self.aw_beats or not self.ar_beats:
            self._fail("requester monitor saw no AW or no AR handshake")
        return not self.errors
