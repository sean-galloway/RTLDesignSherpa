# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: wb4_slave_tb
# Purpose: Testbench for wb4_slave alone: the framework's WB4Master driving
#          the Wishbone side, a WB4Monitor on the wires, GAXI BFMs on the
#          cmd/rsp queues with a responder that models the FUB.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_slave.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-09-09
"""
The TB is the FUB: every command the DUT presents on cmd_* is checked against
the request the master BFM issued (in order), answered from a word memory
with ERR/RTY address windows, and that decision is the expectation for the
termination the master BFM receives. The abort phase drops CYC with requests
outstanding and proves the DUT discards their late responses instead of
pairing them with the next cycle's requests.
"""

import os
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_master, create_wb4_monitor
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR, WB4_STATUS_RTY
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)

MASTER_PROFILES = {
    'fixed':      {'stb': ([(0, 0)], [1])},
    'gappy':      {'stb': ([(0, 0), (1, 4)], [1, 1])},
    'sparse':     {'stb': ([(2, 8)], [1])},
}


class WB4SlaveTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Two clock domains for the CDC variant (WB_CLK / FUB_CLK name the
        # Wishbone-side and queue-side clocks; both default to 'clk').
        self.wb_clk_name = os.environ.get('WB_CLK', 'clk')
        self.fub_clk_name = os.environ.get('FUB_CLK', 'clk')
        self.wb_period = int(os.environ.get('WB_CLK_PERIOD', '10'))
        self.fub_period = int(os.environ.get('FUB_CLK_PERIOD', '10'))
        self.clk = getattr(dut, self.wb_clk_name)          # Wishbone side
        self.fub_clk = getattr(dut, self.fub_clk_name)     # queue side
        self.clk_name = self.wb_clk_name
        self.rst_n = dut.aresetn
        self.wb_rst_n = getattr(dut, 'wb_resetn', None)     # CDC variant only
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.max_outstanding = self.convert_to_int(os.environ.get('MAX_OUTSTANDING', '16'))
        self.classic = os.environ.get('CLASSIC', '0') == '1'   # DUT built CLASSIC=1
        self.mem = {}
        self.issued = deque()        # requests the master BFM was given, in order
        self.expected = deque()      # (status, dat_r) decided by the responder, in order
        self.pending = deque()       # responses waiting for the responder coroutine
        self.done = False
        self.paused = False          # responder hold, for the abort phase
        self.orphans_expected = 0    # commands inside the DUT at abort: answered, never terminated
        self.errors = []
        self.stats = {'issued': 0, 'cmds': 0, 'completed': 0, 'ack': 0, 'err': 0, 'rty': 0}

        self.cmd_fc = FieldConfig()
        self.cmd_fc.add_field(FieldDefinition(name="we", bits=1, default=0, format="bin", display_width=1))
        self.cmd_fc.add_field(FieldDefinition(name="adr", bits=self.AW, default=0, format="hex",
                                              display_width=(self.AW + 3) // 4))
        self.cmd_fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                              display_width=(self.DW + 3) // 4))
        self.cmd_fc.add_field(FieldDefinition(name="sel", bits=self.SW, default=(1 << self.SW) - 1,
                                              format="bin", display_width=self.SW))
        self.rsp_fc = FieldConfig()
        self.rsp_fc.add_field(FieldDefinition(name="status", bits=2, default=0, format="dec", display_width=1))
        self.rsp_fc.add_field(FieldDefinition(name="dat", bits=self.DW, default=0, format="hex",
                                              display_width=(self.DW + 3) // 4))

        self.cmd = create_gaxi_slave(
            dut, 'CMD', '', self.fub_clk, field_config=self.cmd_fc, pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        self.rsp = create_gaxi_master(
            dut, 'RSP', '', self.fub_clk, field_config=self.rsp_fc, pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True)
        self.cmd.add_callback(self._on_cmd)

        # Same mode as the DUT (B4 chapter 5): a pipelined master would drop
        # STB after one clock, which a classic slave never accepts.
        self.master = create_wb4_master(dut, 'WB Master', 's_wb', self.clk, addr_width=self.AW,
                                        data_width=self.DW, max_outstanding=8, classic=self.classic,
                                        randomizer=FlexRandomizer(MASTER_PROFILES['fixed']), log=self.log)
        self.master.add_callback(self._on_complete)
        self.mon = create_wb4_monitor(dut, 'WB Mon', 's_wb', self.clk, addr_width=self.AW,
                                      data_width=self.DW, classic=self.classic, log=self.log)

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.wb_clk_name, self.wb_period, 'ns')
        if self.fub_clk_name != self.wb_clk_name:
            await self.start_clock(self.fub_clk_name, self.fub_period, 'ns')
        self._pre_reset()
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        self._responder = cocotb.start_soon(self._respond())

    def _pre_reset(self):
        """Hook for variants that need configuration pins set before reset."""

    async def assert_reset(self):
        self.rst_n.value = 0
        if self.wb_rst_n is not None:
            self.wb_rst_n.value = 0
        self.dut.cmd_ready.value = 0
        self.dut.rsp_valid.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1
        if self.wb_rst_n is not None:
            self.wb_rst_n.value = 1

    def set_profiles(self, master='fixed', cmd='fixed', rsp='fixed'):
        self.master.set_randomizer(FlexRandomizer(MASTER_PROFILES[master]))
        self.cmd.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[cmd]['slave']))
        self.rsp.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[rsp]['master']))
        self.log.info(f"profiles: master={master} cmd={cmd} rsp={rsp}")

    # ---- the FUB model ----------------------------------------------------
    @staticmethod
    def _status_for(adr):
        if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
            return WB4_STATUS_ERR
        if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
            return WB4_STATUS_RTY
        return WB4_STATUS_ACK

    def _on_cmd(self, pkt):
        we, adr, dat, sel = int(pkt.we), int(pkt.adr), int(pkt.dat), int(pkt.sel)
        self.stats['cmds'] += 1
        if not self.issued:
            self.errors.append(f"DUT presented a command nothing issued: we={we} adr=0x{adr:X}")
            return
        exp = self.issued.popleft()
        if (we, adr, dat, sel) != exp:
            self.errors.append(f"command {(we, adr, hex(dat), sel)} != request issued "
                               f"{(exp[0], exp[1], hex(exp[2]), exp[3])}")
        status, rdat = self._status_for(adr), 0
        if status == WB4_STATUS_ACK:
            if we:
                old = self.mem.get(adr, 0)
                for b in range(self.SW):
                    if (sel >> b) & 1:
                        m = 0xFF << (8 * b)
                        old = (old & ~m) | (dat & m)
                self.mem[adr] = old
            else:
                rdat = self.mem.get(adr, 0)
        if self.orphans_expected > 0:
            # Accepted by the DUT before the abort, delivered to the FUB after
            # it: answered like any command, but the DUT must drop the answer.
            self.orphans_expected -= 1
        else:
            self.expected.append((status, rdat, we))
        self.pending.append((status, rdat))

    async def _respond(self):
        while not self.done:
            if self.pending and not self.paused:
                status, rdat = self.pending.popleft()
                pkt = GAXIPacket(self.rsp_fc)
                pkt.status, pkt.dat = status, rdat
                await self.rsp.send(pkt)
            else:
                await RisingEdge(self.clk)

    def _on_complete(self, pkt):
        self.stats['completed'] += 1
        self.stats[pkt.status_name.lower()] += 1
        if not self.expected:
            self.errors.append(f"termination with nothing expected: {pkt.formatted(compact=True)}")
            return
        status, rdat, we = self.expected.popleft()
        if int(pkt.status) != status or (status == WB4_STATUS_ACK and not we and int(pkt.dat_r) != rdat):
            self.errors.append(f"termination {pkt.formatted(compact=True)} != expected "
                               f"status={status} dat_r=0x{rdat:X}")

    # ---- traffic ------------------------------------------------------------
    def _random_req(self, rng, mix):
        r = rng.random()
        if r < mix / 2:
            adr = rng.randint(*ERR_WINDOW)
        elif r < mix:
            adr = rng.randint(*RTY_WINDOW)
        else:
            adr = rng.randint(0, 0x0FFF) & ~(self.SW - 1)
        return rng.randint(0, 1), adr, rng.getrandbits(self.DW), (rng.getrandbits(self.SW) or ((1 << self.SW) - 1))

    async def run_traffic(self, count, rng, mix=0.2, timeout_clocks=20000):
        start = self.stats['completed']
        for _ in range(count):
            we, adr, dat, sel = self._random_req(rng, mix)
            self.issued.append((we, adr, dat, sel))
            self.stats['issued'] += 1
            await self.master.send(self.master.create_packet(we=we, adr=adr, dat_w=dat, sel=sel))
        waited = 0
        while self.stats['completed'] - start < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_clocks:
                self.errors.append(f"timeout: {self.stats['completed'] - start}/{count} terminations")
                return False
        return not self.errors

    async def run_abort(self, rng, outstanding=4):
        """Issue requests with the FUB responder held, drop CYC while they are
        outstanding, release the responder, and prove the DUT drops those
        responses rather than pairing them with the next cycle.

        Works for any MAX_OUTSTANDING: the DUT may STALL before every request
        is accepted, so the master BFM reports what its abort threw away and
        the TB keeps its request/response bookkeeping consistent with that:
        a request dropped unaccepted is removed from the issued list; commands
        the DUT accepted but had not yet handed to the FUB are answered and
        counted as orphans the DUT must swallow."""
        self.paused = True
        for _ in range(outstanding):
            we, adr, dat, sel = self._random_req(rng, 0.0)
            self.issued.append((we, adr, dat, sel))
            self.stats['issued'] += 1
            await self.master.send(self.master.create_packet(we=we, adr=adr, dat_w=dat, sel=sel))
        # Let the DUT accept what it will (it STALLs at MAX_OUTSTANDING).
        waited = 0
        while len(self.master.outstanding) < min(outstanding, self.max_outstanding) and waited < 200:
            await RisingEdge(self.clk)
            waited += 1
        self.master.abort()
        await self.wait_clocks(self.clk_name, 4)
        info = self.master.last_abort or {}
        accepted, seen = self.master.stats['accepted'], self.stats['cmds']
        # Responses the FUB already computed are no longer expected on the bus.
        dropped = len(self.expected)
        self.expected.clear()
        # Commands accepted on the bus but not yet at the FUB will be answered
        # after the abort; the DUT must drop those answers.
        self.orphans_expected = max(0, accepted - seen)
        # A request the master dropped unaccepted is not coming to the FUB at all.
        if info.get('head_dropped'):
            idx = self.orphans_expected
            issued = list(self.issued)
            if idx < len(issued):
                del issued[idx]
                self.issued = deque(issued)
        aborted_mon = self.mon.aborts
        # Bookkeeping is consistent: let the master start its next cycle and
        # the FUB answer what it holds.
        self.master.resume()
        self.paused = False
        await self.wait_clocks(self.clk_name, 60)
        unexpected = self.master.stats['unexpected_term']
        self.log.info(f"abort: outstanding_at_abort={info.get('outstanding')} head_dropped={info.get('head_dropped')} "
                      f"responses_dropped={dropped} orphans_expected_after={self.orphans_expected} "
                      f"monitor_aborts={aborted_mon} unexpected_terms_after={unexpected}")
        if not info.get('outstanding'):
            self.errors.append("abort phase: nothing was outstanding when CYC dropped")
        if unexpected:
            self.errors.append(f"DUT terminated {unexpected} aborted transfer(s) after CYC dropped")
        return not self.errors

    def report(self):
        v = self.mon.total_violations()
        if v:
            self.errors.append(f"{v} Wishbone protocol violation(s): {self.mon.violations}")
        self.log.info(f"issued={self.stats['issued']} cmds={self.stats['cmds']} "
                      f"completed={self.stats['completed']} ack={self.stats['ack']} err={self.stats['err']} "
                      f"rty={self.stats['rty']} master={self.master.stats} mon: max_inflight={self.mon.max_inflight} "
                      f"aborts={self.mon.aborts} violations={v} errors={len(self.errors)}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
