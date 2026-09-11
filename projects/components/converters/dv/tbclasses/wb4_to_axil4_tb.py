# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for wb4_to_axil4 (Wishbone B4 slave in, AXI4-Lite master out).

The framework's Wishbone master BFM drives s_wb_*; the AXI4-Lite slave BFMs
answer m_axil_* over one shared memory model, so a write really lands where
a later read finds it. The Wishbone monitor checks the B4 rules on the wire.

The central check is ORDERING. AXI4-Lite's B and R channels are independent
and this testbench deliberately answers them at different speeds, so a read
issued behind a slow write finishes first on the AXI side. Wishbone
terminates in issue order, so the converter must hold that read back. The
scoreboard pairs terminations with issue order and fails if one overtakes.
"""
import os
from collections import deque

from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveWrite, AXIL4SlaveRead
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_master, create_wb4_monitor
from CocoTBFramework.components.wb4.wb4_sequence import WB4Sequence
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR
from TBClasses.shared.tbbase import TBBase

MEM_BYTES = 0x4000                       # everything above this answers SLVERR
ERR_BASE  = 0x8000                       # comfortably out of the memory model

MASTER_PROFILES = {
    'fixed':  {'stb': ([(0, 0)], [1])},
    'gappy':  {'stb': ([(0, 0), (1, 4)], [1, 1])},
    'sparse': {'stb': ([(2, 8)], [1])},
}


class WB4ToAXIL4TB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.classic = os.environ.get('CLASSIC', '0') == '1'
        self.outstanding = self.convert_to_int(os.environ.get('OUTSTANDING', '1'))
        # Answer writes slowly and reads quickly, so the AXI side finishes out
        # of order and the converter's reordering is actually exercised.
        self.wr_delay = self.convert_to_int(os.environ.get('WR_DELAY', '6'))
        self.rd_delay = self.convert_to_int(os.environ.get('RD_DELAY', '1'))

        self.mem = MemoryModel(num_lines=MEM_BYTES // self.SW, bytes_per_line=self.SW,
                               log=self.log)
        self.mirror = {}                 # byte address -> value, the expected memory
        self.issued = deque()            # (we, adr, dat, sel, want_status, want_data)
        self.errors = []
        self.stats = {'issued': 0, 'completed': 0, 'ack': 0, 'err': 0}

        self.master = create_wb4_master(dut, 'WB Master', 's_wb', self.clk,
                                        addr_width=self.AW, data_width=self.DW,
                                        max_outstanding=max(1, self.outstanding),
                                        classic=self.classic,
                                        randomizer=FlexRandomizer(MASTER_PROFILES['fixed']),
                                        log=self.log)
        self.master.add_callback(self._on_complete)
        self.mon = create_wb4_monitor(dut, 'WB Mon', 's_wb', self.clk, addr_width=self.AW,
                                      data_width=self.DW, classic=self.classic, log=self.log)
        self.axil_wr = AXIL4SlaveWrite(dut=dut, clock=self.clk, prefix='m_axil_', log=self.log,
                                       data_width=self.DW, addr_width=self.AW, multi_sig=True,
                                       memory_model=self.mem, response_delay=self.wr_delay)
        self.axil_rd = AXIL4SlaveRead(dut=dut, clock=self.clk, prefix='m_axil_', log=self.log,
                                      data_width=self.DW, addr_width=self.AW, multi_sig=True,
                                      memory_model=self.mem, response_delay=self.rd_delay)

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

    def set_profile(self, name):
        self.master.set_randomizer(FlexRandomizer(MASTER_PROFILES[name]))

    # ---- model ----------------------------------------------------------
    def _expected_word(self, adr):
        return sum(self.mirror.get(adr + i, 0) << (8 * i) for i in range(self.SW))

    def _plan(self, we, adr, dat, sel):
        """What the AXI4-Lite side will answer, and what the read should
        return. Anything outside the memory model is SLVERR, which B4 has
        exactly one termination for: ERR."""
        if adr >= MEM_BYTES:
            return WB4_STATUS_ERR, None
        if we:
            for i in range(self.SW):
                if sel >> i & 1:
                    self.mirror[adr + i] = (dat >> (8 * i)) & 0xFF
            return WB4_STATUS_ACK, None
        return WB4_STATUS_ACK, self._expected_word(adr)

    def _on_complete(self, pkt):
        """Terminations arrive in issue order or the DUT is broken: that is
        the B4 rule the converter exists to preserve."""
        self.stats['completed'] += 1
        status, dat = int(pkt.status), int(pkt.dat_r)
        if not self.issued:
            self.errors.append("a termination arrived with nothing issued")
            return
        we, adr, _dat, _sel, want_status, want_data = self.issued.popleft()
        self.stats['ack' if status == WB4_STATUS_ACK else 'err'] += 1
        if status != want_status:
            self.errors.append(f"adr=0x{adr:X} we={we}: status {status}, want {want_status}. "
                               f"A wrong pairing here means a response overtook its "
                               f"predecessor, which B4 forbids.")
        elif want_data is not None and dat != want_data:
            self.errors.append(f"read 0x{adr:X}: data 0x{dat:X}, want 0x{want_data:X}")

    def _sequence(self, rng, count, err_frac=0.1):
        seq = WB4Sequence("wb4_to_axil4.traffic", addr_width=self.AW, data_width=self.DW,
                          seed=rng.getrandbits(32))
        seq.add_random_workload(
            count, addr_lo=0, addr_hi=MEM_BYTES, write_frac=0.5,
            align=True, random_sel=True,
            windows=[(ERR_BASE, ERR_BASE + 0xFFF, err_frac)])
        return seq

    async def run_traffic(self, count, rng, err_frac=0.1, timeout_clocks=60000):
        start = self.stats['completed']
        for t in self._sequence(rng, count, err_frac):
            want_status, want_data = self._plan(t.we, t.adr, t.dat_w, t.sel)
            self.issued.append((t.we, t.adr, t.dat_w, t.sel, want_status, want_data))
            self.stats['issued'] += 1
            await self.master.send(self.master.create_packet(
                we=t.we, adr=t.adr, dat_w=t.dat_w, sel=t.sel))
        waited = 0
        while self.stats['completed'] - start < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_clocks:
                self.errors.append(f"timeout: {self.stats['completed'] - start}/{count} terminations")
                return False
        return not self.errors

    async def run_ordering_probe(self, rng, pairs=8):
        """Directed: a write to the SLOW channel immediately followed by a
        read of a different word on the FAST channel. On the AXI side the
        read finishes first every time; Wishbone must still terminate the
        write first. With OUTSTANDING=1 the converter serialises and the
        question cannot arise, so this is the check that matters when it is
        raised."""
        for i in range(pairs):
            wadr = ((rng.randrange(0, MEM_BYTES // 2)) // self.SW) * self.SW
            radr = (wadr + MEM_BYTES // 2) & ~(self.SW - 1)
            for we, adr in ((1, wadr), (0, radr)):
                dat = rng.getrandbits(self.DW)
                want_status, want_data = self._plan(we, adr, dat, (1 << self.SW) - 1)
                self.issued.append((we, adr, dat, (1 << self.SW) - 1, want_status, want_data))
                self.stats['issued'] += 1
                await self.master.send(self.master.create_packet(
                    we=we, adr=adr, dat_w=dat, sel=(1 << self.SW) - 1))
        waited = 0
        while self.issued and waited < 40000:
            await RisingEdge(self.clk)
            waited += 1
        if self.issued:
            self.errors.append(f"ordering probe: {len(self.issued)} transfers never terminated")
        return not self.errors

    async def wait_idle(self, limit=4000):
        for _ in range(limit):
            await RisingEdge(self.clk)
            if int(self.dut.busy.value) == 0:
                return True
        self.errors.append("busy never dropped")
        return False

    def report(self):
        v = self.mon.total_violations()
        if v:
            self.errors.append(f"Wishbone protocol violation(s): {self.mon.violations}")
        if self.mon.terminated != self.stats['completed']:
            self.errors.append(f"monitor saw {self.mon.terminated} terminations, "
                               f"the master BFM {self.stats['completed']}")
        self.log.info(f"stats {self.stats} wr_delay={self.wr_delay} rd_delay={self.rd_delay} "
                      f"outstanding={self.outstanding} mon terminated={self.mon.terminated} "
                      f"max_inflight={self.mon.max_inflight} violations={v}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
