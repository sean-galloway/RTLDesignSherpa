# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axi4_to_wb4_tb
# Purpose: Testbench class for axi4_to_wb4 (AXI4 completer in, Wishbone B4
#          requester out)
#
# Author: sean galloway
# Created: 2026-09-11

"""Testbench for ``axi4_to_wb4``.

The pieces are tested on their own (``axi4_to_axil4_{rd,wr}`` for the burst
decomposition, ``axil4_to_wb4`` for the AXI4-Lite to Wishbone step); this
bench checks the composition from the AXI4 requester's point of view:

* an N-beat AXI4 burst becomes exactly N Wishbone transfers, in address
  order, each landing in the completer's memory; the read burst returns the
  memory contents beat by beat;
* ``WSTRB`` becomes ``SEL`` (byte shadow);
* a completer ``ERR`` comes back as ``SLVERR`` on B / R, an ``RTY`` as
  ``RTY_RESP`` (``SLVERR`` by default), both without wedging the port;
* a stalling / slow completer (WB4Slave randomizer profiles).

The Wishbone completer is the RDS-DV ``WB4Slave`` with a ``status_hook``
that turns two address windows into ERR and RTY, the way ``axil4_to_wb4``'s
own bench does.
"""

import os
import random
import sys

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead, AXI4MasterWrite
from CocoTBFramework.components.wb4.wb4_components import WB4Slave
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR, WB4_STATUS_RTY
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

MEM_BYTES = 0x1_0000
ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)
DATA_TOP = 0x0000_E000                    # random traffic stays below the windows
OKAY, SLVERR, DECERR = 0, 2, 3

SLAVE_PROFILES = {
    'fixed':  {'stall': ([(0, 0)], [1]), 'ack': ([(1, 1)], [1]), 'status': ([(0, 0)], [1])},
    'slow':   {'stall': ([(0, 0)], [1]), 'ack': ([(2, 6)], [1]), 'status': ([(0, 0)], [1])},
    'stally': {'stall': ([(0, 0), (1, 4)], [1, 1]), 'ack': ([(1, 2)], [1]), 'status': ([(0, 0)], [1])},
}


def _status_for(adr):
    if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
        return WB4_STATUS_ERR
    if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
        return WB4_STATUS_RTY
    return WB4_STATUS_ACK


class AXI4ToWB4TB(TBBase):

    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '4'))
        self.classic = bool(self.convert_to_int(os.environ.get('CLASSIC', '0')))
        self.rty_resp = self.convert_to_int(os.environ.get('RTY_RESP', '2'))
        self.SW = self.data_width // 8
        self.axsize = self.SW.bit_length() - 1
        self.shadow = bytearray(MEM_BYTES)
        self.errors = []

        self.axi_wr = AXI4MasterWrite(dut=dut, clock=self.clk, prefix='s_axi_', log=self.log,
                                      data_width=self.data_width, id_width=self.id_width,
                                      addr_width=self.addr_width, user_width=1, multi_sig=True)
        self.axi_rd = AXI4MasterRead(dut=dut, clock=self.clk, prefix='s_axi_', log=self.log,
                                     data_width=self.data_width, id_width=self.id_width,
                                     addr_width=self.addr_width, user_width=1, multi_sig=True)
        self.wb = WB4Slave(entity=dut, title='WB4_S', prefix='m_wb', clock=self.clk,
                           addr_width=self.addr_width, data_width=self.data_width,
                           num_lines=MEM_BYTES // self.SW, max_outstanding=16,
                           status_hook=self._status_hook,
                           randomizer=FlexRandomizer(SLAVE_PROFILES['fixed']),
                           classic=self.classic, log=self.log)

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

    @staticmethod
    def _status_hook(pkt):
        return _status_for(int(pkt.fields['adr']))

    def set_profile(self, name):
        self.wb.set_randomizer(FlexRandomizer(SLAVE_PROFILES[name]))

    def _fail(self, msg):
        self.errors.append(msg)
        self.log.error(msg)

    def _shadow_write(self, addr, data, strb):
        for b in range(self.SW):
            if (strb >> b) & 1:
                self.shadow[addr + b] = (data >> (8 * b)) & 0xFF

    def _shadow_read(self, addr):
        return int.from_bytes(bytes(self.shadow[addr:addr + self.SW]), 'little')

    def _mem_read(self, addr):
        return int.from_bytes(bytes(self.wb.mem.read(addr, self.SW)), 'little')

    def _resp_of(self, result):
        """Normalise the AXI4 write BFM's three ways of reporting a response."""
        if isinstance(result, dict):
            return int(result.get('response', 0 if result.get('success', True) else 2))
        return int(result)

    # ---- phases ---------------------------------------------------------

    async def run_bursts(self, count, rng, max_beats):
        """N-beat write burst -> N Wishbone transfers in order; read burst
        returns the memory."""
        for i in range(count):
            beats = rng.randint(1, max_beats)
            # keep the burst inside a 4 KB page and below the windows
            span = beats * self.SW
            addr = rng.randrange(0, DATA_TOP - span, self.SW)
            addr -= addr % span if (addr // 0x1000) != ((addr + span - 1) // 0x1000) else 0
            data = [rng.getrandbits(self.data_width) for _ in range(beats)]
            accepted0 = self.wb.stats['accepted']
            res = await self.axi_wr.write_transaction(addr, data, id=(i % (1 << self.id_width)),
                                                      size=self.axsize)
            if self._resp_of(res) != OKAY:
                self._fail(f"burst {i} @0x{addr:X} x{beats}: B resp {self._resp_of(res)}")
            for k, d in enumerate(data):
                self._shadow_write(addr + k * self.SW, d, (1 << self.SW) - 1)
            got_txns = self.wb.stats['accepted'] - accepted0
            if got_txns != beats:
                self._fail(f"burst {i}: {beats} AXI beats became {got_txns} Wishbone transfers")
            adrs = [int(p.fields['adr']) for p in list(self.wb.sentQ)[-beats:]]
            want = [addr + k * self.SW for k in range(beats)]
            if adrs != want:
                self._fail(f"burst {i}: Wishbone addresses {[hex(a) for a in adrs]}, "
                           f"expected {[hex(a) for a in want]}")
            for k, d in enumerate(data):
                if (got := self._mem_read(addr + k * self.SW)) != d:
                    self._fail(f"burst {i} beat {k}: memory 0x{got:X}, wrote 0x{d:X}")
            rd = await self.axi_rd.read_transaction(addr, burst_len=beats,
                                                    id=(i % (1 << self.id_width)), size=self.axsize)
            if list(rd) != data:
                self._fail(f"burst {i} read x{beats} @0x{addr:X}: {[hex(x) for x in rd]} != {[hex(x) for x in data]}")

    async def run_strobes(self, count, rng):
        for i in range(count):
            addr = rng.randrange(0, DATA_TOP, self.SW)
            data = rng.getrandbits(self.data_width)
            strb = rng.randrange(1, 1 << self.SW)
            res = await self.axi_wr.single_write(addr, data, strb=strb, size=self.axsize)
            if self._resp_of(res) != OKAY:
                self._fail(f"strobe write {i}: B resp {self._resp_of(res)}")
            self._shadow_write(addr, data, strb)
            sel = int(self.wb.sentQ[-1].fields['sel'])
            if sel != strb:
                self._fail(f"strobe write {i}: SEL 0x{sel:X} != WSTRB 0x{strb:X}")
            got, want = self._mem_read(addr), self._shadow_read(addr)
            if got != want:
                self._fail(f"strobe write {i} @0x{addr:X}: memory 0x{got:X}, expected 0x{want:X}")

    async def run_windows(self, count, rng):
        """ERR -> SLVERR, RTY -> RTY_RESP, and the port still works after."""
        for i in range(count):
            for lo, hi, want in ((ERR_WINDOW[0], ERR_WINDOW[1], SLVERR),
                                 (RTY_WINDOW[0], RTY_WINDOW[1], self.rty_resp)):
                addr = rng.randrange(lo, hi + 1 - self.SW, self.SW)
                res = await self.axi_wr.single_write(addr, rng.getrandbits(self.data_width), size=self.axsize)
                if self._resp_of(res) != want:
                    self._fail(f"window write {i} @0x{addr:X}: B resp {self._resp_of(res)}, expected {want}")
                try:
                    await self.axi_rd.single_read(addr, size=self.axsize)
                    self._fail(f"window read {i} @0x{addr:X} answered OKAY, expected resp {want}")
                except RuntimeError as e:
                    name = {2: 'SLVERR', 3: 'DECERR'}[want]
                    if name not in str(e):
                        self._fail(f"window read {i} @0x{addr:X}: {e} (expected {name})")
            probe = rng.randrange(0, DATA_TOP, self.SW)
            good = rng.getrandbits(self.data_width)
            res = await self.axi_wr.single_write(probe, good, size=self.axsize)
            self._shadow_write(probe, good, (1 << self.SW) - 1)
            got = await self.axi_rd.single_read(probe, size=self.axsize)
            if self._resp_of(res) != OKAY or got != good:
                self._fail(f"window {i}: port did not recover (resp {self._resp_of(res)}, read 0x{got:X})")

    async def run_suite(self, level, seed):
        rng = random.Random(seed)
        plan = {'gate': dict(bursts=6, beats=4, strobes=4, windows=1, profiles=('fixed',)),
                'func': dict(bursts=24, beats=8, strobes=16, windows=3, profiles=('fixed', 'stally')),
                'full': dict(bursts=60, beats=16, strobes=40, windows=6, profiles=('fixed', 'stally', 'slow'))}[level]
        self.log.info(f"AXI4->WB4 {level.upper()} plan: {plan}")
        for prof in plan['profiles']:
            self.set_profile(prof)
            await self.run_bursts(plan['bursts'], rng, plan['beats'])
            await self.run_strobes(plan['strobes'], rng)
        self.set_profile('fixed')
        await self.run_windows(plan['windows'], rng)
        if self.wb.stats['accepted'] == 0:
            self._fail("the Wishbone completer saw no transfer at all")
        self.log.info(f"wishbone transfers: {self.wb.stats}  errors={len(self.errors)}")
        return not self.errors
