# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: wb4_master_tb
# Purpose: Testbench for wb4_master alone: GAXI BFMs on the cmd/rsp queues,
#          the framework's WB4Slave answering on the Wishbone side and a
#          WB4Monitor checking the wires.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-09-09
"""
The slave BFM services every request it accepts from a memory model and
decides the termination: ERR inside ERR_WINDOW, RTY inside RTY_WINDOW, ACK
elsewhere. Its completed packets (in order) are the expectation: each
response the DUT returns on rsp_* must carry that packet's status and read
data, and each request the slave saw must be the command the TB queued.
"""

import os
from collections import deque

from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_monitor, create_wb4_slave
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ERR, WB4_STATUS_RTY
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

ERR_WINDOW = (0x0000_E000, 0x0000_EFFF)
RTY_WINDOW = (0x0000_F000, 0x0000_FFFF)
MEM_LINES = 4096      # bytes / bytes-per-line; addresses below ERR_WINDOW

# WB4Slave timing presets: (stall, ack latency, status weights)
SLAVE_PROFILES = {
    'fixed':      {'stall': ([(0, 0)], [1]),            'ack': ([(1, 1)], [1]),         'status': ([(0, 0)], [1])},
    'slow_ack':   {'stall': ([(0, 0)], [1]),            'ack': ([(2, 6)], [1]),         'status': ([(0, 0)], [1])},
    'stally':     {'stall': ([(0, 0), (1, 4)], [1, 1]), 'ack': ([(1, 2)], [1]),         'status': ([(0, 0)], [1])},
    'mixed':      {'stall': ([(0, 0), (1, 3)], [3, 1]), 'ack': ([(1, 1), (2, 5)], [2, 1]), 'status': ([(0, 0)], [1])},
}


class WB4MasterTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.classic = os.environ.get('CLASSIC', '0') == '1'   # DUT built CLASSIC=1
        self.sent = deque()          # commands queued by the TB, in order
        self.got = deque()           # (status, dat) seen on rsp_*
        self.errors = []
        self.stats = {'sent': 0, 'responses': 0}

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

        self.cmd = create_gaxi_master(
            dut, 'CMD', '', self.clk, field_config=self.cmd_fc, pkt_prefix='cmd',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']),
            memory_model=None, log=self.log, multi_sig=True)
        self.rsp = create_gaxi_slave(
            dut, 'RSP', '', self.clk, field_config=self.rsp_fc, pkt_prefix='rsp',
            randomizer=FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']),
            memory_model=None, log=self.log, multi_sig=True)
        self.rsp.add_callback(self._on_rsp)

        # The peer must be the same mode as the DUT (B4 chapter 5): a classic
        # master against a pipelined slave would have its held STB accepted
        # again every clock.
        self.slave = create_wb4_slave(
            dut, 'WB Slave', 'm_wb', self.clk, addr_width=self.AW, data_width=self.DW,
            num_lines=MEM_LINES, max_outstanding=16, status_hook=self._status_hook,
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
        self.dut.cmd_valid.value = 0
        self.dut.rsp_ready.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- profiles ---------------------------------------------------------
    def set_profiles(self, cmd='fixed', rsp='fixed', slave='fixed'):
        self.cmd.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[cmd]['master']))
        self.rsp.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[rsp]['slave']))
        self.slave.set_randomizer(FlexRandomizer(SLAVE_PROFILES[slave]))
        self.log.info(f"profiles: cmd={cmd} rsp={rsp} slave={slave}")

    # ---- model ------------------------------------------------------------
    @staticmethod
    def _status_hook(pkt):
        adr = int(pkt.adr)
        if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
            return WB4_STATUS_ERR
        if RTY_WINDOW[0] <= adr <= RTY_WINDOW[1]:
            return WB4_STATUS_RTY
        return None

    def _on_rsp(self, pkt):
        self.stats['responses'] += 1
        self.got.append((int(pkt.status), int(pkt.dat)))

    def _random_cmd(self, rng, mix):
        r = rng.random()
        if r < mix / 2:
            adr = rng.randint(*ERR_WINDOW)
        elif r < mix:
            adr = rng.randint(*RTY_WINDOW)
        else:
            adr = rng.randint(0, MEM_LINES * self.SW - 1) & ~(self.SW - 1)
        we = rng.randint(0, 1)
        return we, adr, rng.getrandbits(self.DW), (rng.getrandbits(self.SW) or ((1 << self.SW) - 1))

    async def trace_wires(self, cycles):
        """Debug aid (WB4_TRACE=1): one line per clock of the Wishbone wires."""
        d = self.dut
        for i in range(cycles):
            await RisingEdge(self.clk)
            self.log.info(f"[wire {i:3d}] cyc={int(d.m_wb_CYC.value)} stb={int(d.m_wb_STB.value)} "
                          f"stall={int(d.m_wb_STALL.value)} ack={int(d.m_wb_ACK.value)} "
                          f"err={int(d.m_wb_ERR.value)} rty={int(d.m_wb_RTY.value)} "
                          f"cmd_v={int(d.cmd_valid.value)} cmd_r={int(d.cmd_ready.value)} "
                          f"rsp_v={int(d.rsp_valid.value)} rsp_r={int(d.rsp_ready.value)} "
                          f"inflight={int(d.r_inflight.value)} reserved={int(d.r_reserved.value)}")

    async def run_traffic(self, count, rng, mix=0.2, timeout_clocks=20000):
        start = self.stats['responses']
        if os.environ.get('WB4_TRACE', '0') == '1':
            import cocotb
            cocotb.start_soon(self.trace_wires(48))
        # Queue the whole phase, then let the GAXI master drive it at its
        # profile's pace. `send()` per packet waits for the driver pipeline to
        # drain each time (one command per ~3 clocks whatever the profile), so
        # the DUT could never be offered work fast enough to fill its credit.
        pkts = []
        for _ in range(count):
            we, adr, dat, sel = self._random_cmd(rng, mix)
            self.sent.append((we, adr, dat, sel))
            pkt = GAXIPacket(self.cmd_fc)
            pkt.we, pkt.adr, pkt.dat, pkt.sel = we, adr, dat, sel
            self.stats['sent'] += 1
            pkts.append(pkt)
        await self.cmd.send_burst(pkts)
        waited = 0
        while self.stats['responses'] - start < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_clocks:
                self.errors.append(f"timeout: {self.stats['responses'] - start}/{count} responses")
                return False
        return self.check()

    def check(self):
        """Pair what the slave BFM serviced with what the TB sent and what
        the DUT returned, all in order."""
        while self.slave.sentQ and self.got and self.sent:
            spkt = self.slave.sentQ.popleft()
            we, adr, dat, sel = self.sent.popleft()
            status, rdat = self.got.popleft()
            seen = (int(spkt.we), int(spkt.adr), int(spkt.dat_w), int(spkt.sel))
            if seen != (we, adr, dat, sel):
                self.errors.append(f"request on the bus {seen} != command sent {(we, adr, dat, sel)}")
            exp = (int(spkt.status), int(spkt.dat_r) if int(spkt.status) == 0 and not int(spkt.we) else None)
            if status != exp[0] or (exp[1] is not None and rdat != exp[1]):
                self.errors.append(f"response ({status}, 0x{rdat:X}) != slave termination "
                                   f"({exp[0]}, {exp[1] if exp[1] is None else hex(exp[1])}) for adr=0x{adr:X}")
        return not self.errors

    def report(self):
        v = self.mon.total_violations()
        if v:
            self.errors.append(f"{v} Wishbone protocol violation(s): {self.mon.violations}")
        self.log.info(f"sent={self.stats['sent']} responses={self.stats['responses']} "
                      f"slave={self.slave.stats} mon: accepted={self.mon.accepted} "
                      f"terminated={self.mon.terminated} max_inflight={self.mon.max_inflight} "
                      f"violations={v} errors={len(self.errors)}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
