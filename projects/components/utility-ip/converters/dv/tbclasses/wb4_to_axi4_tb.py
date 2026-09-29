# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: wb4_to_axi4_tb
# Purpose: Testbench class for wb4_to_axi4 (Wishbone B4 completer in, AXI4
#          requester out)
#
# Author: sean galloway
# Created: 2026-09-11

"""Testbench for ``wb4_to_axi4``.

``wb4_to_axil4`` is already tested (``test_wb4_to_axil4.py``: the in-order
response merge, STALL, abort, the ordering probe). This wrapper adds only the
AXI4 promotion of that AXI4-Lite face, so this bench checks exactly that:

* every ``AW``/``AR`` carries the single-beat shape the wrapper invents
  (``len=0``, ``size`` = the full width, INCR, the constant ID, lock/qos/
  region 0) and every ``W`` has ``wlast=1``;
* ``SEL`` becomes ``WSTRB`` and only those lanes change (byte shadow);
* the data round trip through a memory-backed AXI4 completer, memory read
  directly as well as through a second transfer;
* ``SLVERR`` (the completer's out-of-range answer) terminates ``ERR`` with
  nothing written, and the port keeps working;
* a slow completer holds ``AW``/``W``/``AR`` to their handshakes.
"""

import os
import random
import sys

from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.wb4.wb4_components import WB4Master
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead, AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


class WB4ToAXI4TB(TBBase):
    """Drives Wishbone B4, completes AXI4, audits the requester between."""

    MEM_LINES = 256

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.data_width = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '1'))
        self.default_id = self.convert_to_int(os.environ.get('DEFAULT_ID', '0'))
        self.slave_delay = self.convert_to_int(os.environ.get('SLAVE_DELAY', '1'))
        self.classic = bool(self.convert_to_int(os.environ.get('CLASSIC', '0')))

        self.bytes_per_beat = self.data_width // 8
        self.axsize = self.bytes_per_beat.bit_length() - 1
        self.mem_bytes = self.MEM_LINES * self.bytes_per_beat
        self.shadow = bytearray(self.mem_bytes)
        self.errors = []
        self.aw_beats = []     # (addr, prot)
        self.ar_beats = []
        self.w_beats = []      # (strb,)

        self.wb = WB4Master(
            entity=dut, title="WB4_M", prefix="s_wb", clock=self.clk,
            addr_width=self.addr_width, data_width=self.data_width,
            max_outstanding=8, classic=self.classic,
            randomizer=FlexRandomizer({'stb': ([(0, 0), (1, 2)], [4, 1])}),
            log=self.log,
        )
        self.mem = MemoryModel(num_lines=self.MEM_LINES, bytes_per_line=self.bytes_per_beat,
                               log=self.log)
        self.axi_wr = AXI4SlaveWrite(
            dut=dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=1, multi_sig=True,
            memory_model=self.mem, response_delay=self.slave_delay,
        )
        self.axi_rd = AXI4SlaveRead(
            dut=dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.data_width, id_width=self.id_width,
            addr_width=self.addr_width, user_width=1, multi_sig=True,
            memory_model=self.mem, response_delay=self.slave_delay,
        )
        self.log.info(f"WB4->AXI4 TB: dw={self.data_width} aw={self.addr_width} "
                      f"id={self.id_width} classic={self.classic} delay={self.slave_delay}")

    # ---- mandatory ------------------------------------------------------

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- monitor --------------------------------------------------------

    def _fail(self, msg):
        self.errors.append(msg)
        self.log.error(msg)

    def _sample(self, name):
        try:
            return int(getattr(self.dut, name).value)
        except ValueError:
            self._fail(f"{name} is X/Z at a handshake")
            return None

    def _hs(self, ch):
        try:
            return (int(getattr(self.dut, f"{ch}valid").value) == 1
                    and int(getattr(self.dut, f"{ch}ready").value) == 1)
        except ValueError:
            return False

    def _check_single_beat(self, chan):
        want = {f"m_axi_{chan}len": 0, f"m_axi_{chan}size": self.axsize,
                f"m_axi_{chan}burst": 1, f"m_axi_{chan}id": self.default_id,
                f"m_axi_{chan}lock": 0, f"m_axi_{chan}qos": 0, f"m_axi_{chan}region": 0}
        for name, expect in want.items():
            got = self._sample(name)
            if got is not None and got != expect:
                self._fail(f"{name} = {got} on a handshake, expected {expect}")

    async def axi_monitor(self):
        while True:
            await RisingEdge(self.clk)
            if self._hs('m_axi_aw'):
                self._check_single_beat('aw')
                self.aw_beats.append((self._sample('m_axi_awaddr'), self._sample('m_axi_awprot')))
            if self._hs('m_axi_w'):
                if self._sample('m_axi_wlast') != 1:
                    self._fail("m_axi_wlast = 0 on a W handshake")
                self.w_beats.append((self._sample('m_axi_wstrb'),))
            if self._hs('m_axi_ar'):
                self._check_single_beat('ar')
                self.ar_beats.append((self._sample('m_axi_araddr'), self._sample('m_axi_arprot')))

    # ---- helpers --------------------------------------------------------

    def _shadow_write(self, addr, data, sel):
        for b in range(self.bytes_per_beat):
            if (sel >> b) & 1:
                self.shadow[addr + b] = (data >> (8 * b)) & 0xFF

    def _shadow_read(self, addr):
        return int.from_bytes(bytes(self.shadow[addr:addr + self.bytes_per_beat]), 'little')

    def _mem_read(self, addr):
        return int.from_bytes(bytes(self.mem.read(addr, self.bytes_per_beat)), 'little')

    def _rand_addr(self, rng):
        return rng.randrange(0, self.mem_bytes, self.bytes_per_beat)

    # ---- phases ---------------------------------------------------------

    async def run_write_read(self, count, rng):
        for i in range(count):
            addr = self._rand_addr(rng)
            data = rng.getrandbits(self.data_width)
            n_aw, n_w, n_ar = len(self.aw_beats), len(self.w_beats), len(self.ar_beats)
            pkt = await self.wb.write(addr, data)
            self._shadow_write(addr, data, (1 << self.bytes_per_beat) - 1)
            if int(pkt.fields['status']) != WB4_STATUS_ACK:
                self._fail(f"write {i} @0x{addr:X}: status {pkt.fields['status']}, expected ACK")
            if (got := self._mem_read(addr)) != data:
                self._fail(f"write {i} @0x{addr:X}: memory 0x{got:X}, wrote 0x{data:X}")
            if len(self.aw_beats) != n_aw + 1 or len(self.w_beats) != n_w + 1:
                self._fail(f"write {i}: expected one AW and one W (+{len(self.aw_beats)-n_aw}/+{len(self.w_beats)-n_w})")
            elif self.aw_beats[-1][0] != addr:
                self._fail(f"write {i}: awaddr 0x{self.aw_beats[-1][0]:X} != ADR 0x{addr:X}")
            rpkt = await self.wb.read(addr)
            if int(rpkt.fields['status']) != WB4_STATUS_ACK:
                self._fail(f"read {i} @0x{addr:X}: status {rpkt.fields['status']}, expected ACK")
            if int(rpkt.fields['dat_r']) != data:
                self._fail(f"read {i} @0x{addr:X}: DAT_R 0x{int(rpkt.fields['dat_r']):X}, expected 0x{data:X}")
            if len(self.ar_beats) != n_ar + 1:
                self._fail(f"read {i}: expected one AR (+{len(self.ar_beats)-n_ar})")
            elif self.ar_beats[-1][0] != addr:
                self._fail(f"read {i}: araddr 0x{self.ar_beats[-1][0]:X} != ADR 0x{addr:X}")

    async def run_sel(self, count, rng):
        for i in range(count):
            addr = self._rand_addr(rng)
            data = rng.getrandbits(self.data_width)
            sel = rng.randrange(1, 1 << self.bytes_per_beat)
            n_w = len(self.w_beats)
            pkt = await self.wb.write(addr, data, sel=sel)
            self._shadow_write(addr, data, sel)
            if int(pkt.fields['status']) != WB4_STATUS_ACK:
                self._fail(f"sel write {i}: status {pkt.fields['status']}")
            if len(self.w_beats) == n_w + 1 and self.w_beats[-1][0] != sel:
                self._fail(f"sel write {i}: WSTRB 0x{self.w_beats[-1][0]:X} != SEL 0x{sel:X}")
            got, want = self._mem_read(addr), self._shadow_read(addr)
            if got != want:
                self._fail(f"sel write {i} @0x{addr:X} sel=0x{sel:X}: memory 0x{got:X}, expected 0x{want:X}")

    async def run_errors(self, count, rng):
        for i in range(count):
            bad = self.mem_bytes + rng.randrange(0, self.mem_bytes, self.bytes_per_beat)
            wpkt = await self.wb.write(bad, rng.getrandbits(self.data_width))
            if int(wpkt.fields['status']) != WB4_STATUS_ERR:
                self._fail(f"error write {i} @0x{bad:X}: status {wpkt.fields['status']}, expected ERR")
            rpkt = await self.wb.read(bad)
            if int(rpkt.fields['status']) != WB4_STATUS_ERR:
                self._fail(f"error read {i} @0x{bad:X}: status {rpkt.fields['status']}, expected ERR")
            probe = self._rand_addr(rng)
            good = rng.getrandbits(self.data_width)
            gpkt = await self.wb.write(probe, good)
            self._shadow_write(probe, good, (1 << self.bytes_per_beat) - 1)
            grpkt = await self.wb.read(probe)
            if int(gpkt.fields['status']) or int(grpkt.fields['status']) or int(grpkt.fields['dat_r']) != good:
                self._fail(f"error {i}: port did not recover after ERR "
                           f"(w {gpkt.fields['status']}, r {grpkt.fields['status']}, "
                           f"data 0x{int(grpkt.fields['dat_r']):X})")

    async def run_backpressure(self, count, rng, delay):
        self.axi_wr.response_delay_cycles = delay
        self.axi_rd.response_delay_cycles = delay
        try:
            await self.run_write_read(count, rng)
        finally:
            self.axi_wr.response_delay_cycles = self.slave_delay
            self.axi_rd.response_delay_cycles = self.slave_delay

    async def run_suite(self, level, seed):
        rng = random.Random(seed)
        plan = {'gate': dict(rw=8, sel=4, err=2, bp=0),
                'func': dict(rw=30, sel=20, err=4, bp=8),
                'full': dict(rw=100, sel=60, err=10, bp=30)}[level]
        self.log.info(f"WB4->AXI4 {level.upper()} plan: {plan}")
        await self.run_write_read(plan['rw'], rng)
        await self.run_sel(plan['sel'], rng)
        await self.run_errors(plan['err'], rng)
        if plan['bp']:
            await self.run_backpressure(plan['bp'], rng, delay=12)
        if not self.aw_beats or not self.ar_beats:
            self._fail("requester monitor saw no AW or no AR handshake")
        self.log.info(f"observed AW={len(self.aw_beats)} W={len(self.w_beats)} "
                      f"AR={len(self.ar_beats)} errors={len(self.errors)}")
        return not self.errors
