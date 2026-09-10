# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for axil4_to_wb4 (AXI4-Lite slave in, Wishbone B4 master out).

AXI4-Lite master BFMs drive s_axil_*; the framework's Wishbone slave BFM
answers m_wb_* over a memory model, with ERR and RTY windows decided by
address, and the Wishbone monitor checks the B4 rules on the wire.
The scoreboard keeps a byte-accurate mirror of what the writes should have
left in the slave and checks every read against it, and every response
code against the window the address falls in.
"""
import os
import random
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4MasterWrite, AXIL4MasterRead
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_monitor, create_wb4_slave
from CocoTBFramework.components.wb4.wb4_sequence import WB4Sequence
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR, WB4_STATUS_RTY
from TBClasses.shared.tbbase import TBBase

ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)
MEM_BYTES = 0x1_0000            # covers the ACK, ERR and RTY windows
OKAY, SLVERR, DECERR = 0, 2, 3

SLAVE_PROFILES = {
    'fixed':   {'stall': ([(0, 0)], [1]),            'ack': ([(1, 1)], [1]),            'status': ([(0, 0)], [1])},
    'slow':    {'stall': ([(0, 0)], [1]),            'ack': ([(2, 6)], [1]),            'status': ([(0, 0)], [1])},
    'stally':  {'stall': ([(0, 0), (1, 4)], [1, 1]), 'ack': ([(1, 2)], [1]),            'status': ([(0, 0)], [1])},
    'mixed':   {'stall': ([(0, 0), (1, 3)], [3, 1]), 'ack': ([(1, 1), (2, 5)], [2, 1]), 'status': ([(0, 0)], [1])},
}


def _status_for(adr):
    if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
        return WB4_STATUS_ERR
    if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
        return WB4_STATUS_RTY
    return WB4_STATUS_ACK


class AXIL4ToWB4TB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.classic = os.environ.get('CLASSIC', '0') == '1'
        self.rty_resp = self.convert_to_int(os.environ.get('RTY_RESP', '2'))
        self.mirror = {}                 # byte address -> value, for ACK-window lines
        self.errors = []
        self.stats = {'writes': 0, 'reads': 0, 'slverr': 0, 'rty': 0}

        self.axil_wr = AXIL4MasterWrite(dut=dut, clock=self.clk, prefix='s_axil_', log=self.log,
                                        data_width=self.DW, addr_width=self.AW, multi_sig=True)
        self.axil_rd = AXIL4MasterRead(dut=dut, clock=self.clk, prefix='s_axil_', log=self.log,
                                       data_width=self.DW, addr_width=self.AW, multi_sig=True)
        self.slave = create_wb4_slave(
            dut, 'WB Slave', 'm_wb', self.clk, addr_width=self.AW, data_width=self.DW,
            num_lines=MEM_BYTES // self.SW, max_outstanding=16, status_hook=self._status_hook,
            randomizer=FlexRandomizer(SLAVE_PROFILES['fixed']), classic=self.classic, log=self.log)
        self.mon = create_wb4_monitor(dut, 'WB Mon', 'm_wb', self.clk, addr_width=self.AW,
                                      data_width=self.DW, classic=self.classic, log=self.log)

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- helpers --------------------------------------------------------
    @staticmethod
    def _status_hook(pkt):
        return _status_for(int(pkt.adr))

    def set_slave_profile(self, name):
        self.slave.set_randomizer(FlexRandomizer(SLAVE_PROFILES[name]))

    def _sequence(self, rng, count, *, windows=True, unique=False, name="traffic"):
        """The traffic for one batch, as a WB4Sequence.

        The sequence axis owns WHAT transfers happen -- the 60/40 write mix,
        the word alignment the memory model's lines want, and the ERR and RTY
        windows the Wishbone slave decodes. The AXI4-Lite BFMs still own who
        drives them and when. ``unique`` keeps addresses distinct inside a
        batch, which concurrent traffic needs so a per-address mirror cannot
        race itself.
        """
        seq = WB4Sequence(f"axil4_to_wb4.{name}", addr_width=self.AW,
                          data_width=self.DW, seed=rng.getrandbits(32))
        win = [(ERR_WINDOW[0], ERR_WINDOW[1], 0.08),
               (RTY_WINDOW[0], RTY_WINDOW[1], 0.08)] if windows else []
        seq.add_random_workload(count, addr_lo=0, addr_hi=0xD000, write_frac=0.6,
                                align=True, random_sel=False, unique_addrs=unique,
                                windows=win)
        return seq

    def _expected_word(self, adr):
        return sum(self.mirror.get(adr + i, 0) << (8 * i) for i in range(self.SW))

    async def write(self, adr, data, strb=None):
        """One AXI4-Lite write; checks the response against the address window
        and updates the mirror on OKAY."""
        strb = (1 << self.SW) - 1 if strb is None else strb
        want = {WB4_STATUS_ACK: OKAY, WB4_STATUS_ERR: SLVERR, WB4_STATUS_RTY: self.rty_resp}[_status_for(adr)]
        try:
            got = await self.axil_wr.write_transaction(adr, data, strb=strb)
        except RuntimeError as e:                 # the BFM raises on SLVERR/DECERR
            got = SLVERR if 'SLVERR' in str(e) else DECERR
        self.stats['writes'] += 1
        if got != want:
            self.errors.append(f"write 0x{adr:X}: bresp {got}, want {want}")
        elif want == OKAY:
            for i in range(self.SW):
                if strb >> i & 1:
                    self.mirror[adr + i] = (data >> (8 * i)) & 0xFF
        else:
            self.stats['rty' if _status_for(adr) == WB4_STATUS_RTY else 'slverr'] += 1

    async def read(self, adr):
        """One AXI4-Lite read; checks data (ACK window) or the response code."""
        want = {WB4_STATUS_ACK: OKAY, WB4_STATUS_ERR: SLVERR, WB4_STATUS_RTY: self.rty_resp}[_status_for(adr)]
        try:
            data = await self.axil_rd.read_transaction(adr)
            got = OKAY
        except RuntimeError:
            got = int(self.axil_rd.last_r_packet.resp)
            data = None
        self.stats['reads'] += 1
        if got != want:
            self.errors.append(f"read 0x{adr:X}: rresp {got}, want {want}")
        elif want == OKAY and data != self._expected_word(adr):
            self.errors.append(f"read 0x{adr:X}: data 0x{data:X}, want 0x{self._expected_word(adr):X}")

    async def run_random(self, rng, count, concurrency=1, windows=True):
        """count transactions, up to `concurrency` in flight, 60% writes.
        Concurrent traffic on the same word would race the mirror, so each
        in-flight batch uses distinct addresses."""
        done = 0
        while done < count:
            n = min(concurrency, count - done)
            # One sequence per batch, addresses unique within it when more
            # than one transfer is in flight.
            batch = self._sequence(rng, n, windows=windows, unique=(concurrency > 1),
                                   name="random")
            tasks = []
            for t in batch:
                if t.is_write:
                    strb = rng.randint(1, (1 << self.SW) - 1) if rng.random() < 0.3 else None
                    tasks.append(cocotb.start_soon(self.write(t.adr, t.dat_w, strb)))
                else:
                    tasks.append(cocotb.start_soon(self.read(t.adr)))
            for task in tasks:
                await task
            done += n

    async def run_strobes(self, rng, count):
        """Full write, then a partial (strobed) write to the same word, then a
        read back: the untouched bytes must survive. Random traffic rarely
        lands a strobed write and a read on the same word, so this is directed."""
        # add_strobed_writes builds exactly this triple per address: a full
        # write, a partial one, then the read back.
        seq = WB4Sequence("axil4_to_wb4.strobes", addr_width=self.AW,
                          data_width=self.DW, seed=rng.getrandbits(32))
        base = (rng.randrange(0, 0xC000) // self.SW) * self.SW
        seq.add_strobed_writes(base, count)
        for t in seq:
            if t.is_write:
                strb = None if t.sel == seq.all_sel else t.sel
                await self.write(t.adr, t.dat_w, strb)
            else:
                await self.read(t.adr)

    async def wait_idle(self, limit=2000):
        for _ in range(limit):
            await RisingEdge(self.clk)
            if int(self.dut.busy.value) == 0:
                return True
        self.errors.append("busy never dropped")
        return False

    def check_monitor(self):
        v = self.mon.total_violations()
        if v:
            self.errors.append(f"Wishbone monitor violations: {self.mon.violations}")
        n = self.stats['writes'] + self.stats['reads']
        if self.mon.terminated != n:
            self.errors.append(f"monitor saw {self.mon.terminated} transfers for {n} transactions")

    def report(self):
        self.log.info(f"stats {self.stats} monitor transfers {self.mon.terminated} "
                      f"max_inflight {self.mon.max_inflight}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
