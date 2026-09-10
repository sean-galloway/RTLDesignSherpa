# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Testbench for wb4_master_retry (rtl/amba/wb4/wb4_master_retry.sv):
wb4_retry in front of wb4_master.

GAXI BFMs drive the FUB-side queues (a burst producer on cmd_*, a consumer on
rsp_*); the framework Wishbone slave answers the bus over a memory model with
three address windows decided by a status hook:

  ERR window      every access terminates ERR
  RTY_K window    the first k accesses of an address terminate RTY, then ACK
                  (k drawn 1..3 per address)
  RTY_ALWAYS      every access terminates RTY

so the expected FUB response and the expected number of re-issues follow
from the address and the retry budget: retry_count, the monitor's transfer
count and the slave's RTY count must all agree with the model, and the FUB
responses come back in command order with the right status and data.
"""
import os
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.wb4.wb4_factories import create_wb4_monitor, create_wb4_slave
from CocoTBFramework.components.wb4.wb4_sequence import WB4Sequence
from CocoTBFramework.components.shared.wb4_common import WB4_STATUS_ACK, WB4_STATUS_ERR, WB4_STATUS_RTY
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.amba.wb4_master_tb import SLAVE_PROFILES

ERR_WINDOW    = (0x0000_E000, 0x0000_EFFF)
RTY_K_WINDOW  = (0x0000_F000, 0x0000_F7FF)
RTY_ALWAYS    = (0x0000_F800, 0x0000_FFFF)
MEM_BYTES     = 0x1_0000


class WB4MasterRetryTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.aresetn
        self.AW = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DW = self.convert_to_int(os.environ.get('DATA_WIDTH', '32'))
        self.SW = self.DW // 8
        self.inflight = self.convert_to_int(os.environ.get('INFLIGHT', '1'))
        self.classic = os.environ.get('CLASSIC', '0') == '1'
        self.max_retries = 3
        self.retry_delay = 4
        self.min_retry_gap = None   # smallest RTY-to-re-issue gap seen on the wire (INFLIGHT=1)
        self.rty_initial = {}       # RTY_K window: RTYs an address answers before ACK (drawn by the model)
        self.rty_left = {}          # RTY_K window: the slave hook's live countdown per address
        self.model_left = {}        # RTY_K window: the model's countdown, advanced at plan time
        self.mirror = {}            # byte address -> value (ACK writes)
        self.sent = deque()         # (we, adr, dat, sel, want_status, want_data)
        self.got = deque()          # (status, dat) from rsp_*
        self.expected_retries = 0
        self.expected_rty_to_fub = 0
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
        self.slave = create_wb4_slave(
            dut, 'WB Slave', 'm_wb', self.clk, addr_width=self.AW, data_width=self.DW,
            num_lines=MEM_BYTES // self.SW, max_outstanding=16, status_hook=self._status_hook,
            randomizer=FlexRandomizer(SLAVE_PROFILES['fixed']), classic=self.classic, log=self.log)
        self.mon = create_wb4_monitor(dut, 'WB Mon', 'm_wb', self.clk, addr_width=self.AW,
                                      data_width=self.DW, classic=self.classic, log=self.log)

    # ---- mandatory ------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        self.set_retry(3, 4)
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        if self.inflight == 1:
            cocotb.start_soon(self._watch_retry_delay())

    async def _watch_retry_delay(self):
        """With one command in flight the request after a scheduled retry IS
        the retry, so the gap on the wire between the RTY termination
        (retry_count moving) and the next accepted request must be at least
        cfg_retry_delay + 1 clocks (the timer, then the master's queue)."""
        d = self.dut
        last_rc, pending, t = 0, None, 0
        while True:
            await RisingEdge(self.clk)
            t += 1
            rc = int(d.retry_count.value)
            if rc != last_rc:
                pending, last_rc = (t, self.retry_delay), rc
            if int(d.m_wb_CYC.value) and int(d.m_wb_STB.value) and not int(d.m_wb_STALL.value):
                if pending is not None:
                    gap = t - pending[0]
                    self.min_retry_gap = gap if self.min_retry_gap is None else min(self.min_retry_gap, gap)
                    if gap < pending[1] + 1:
                        self.errors.append(f"re-issue {gap} clocks after the RTY, cfg_retry_delay={pending[1]}")
                    pending = None

    async def assert_reset(self):
        self.rst_n.value = 0
        self.dut.cmd_valid.value = 0
        self.dut.rsp_ready.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- knobs ----------------------------------------------------------
    def set_retry(self, max_retries, delay):
        self.max_retries = max_retries
        self.retry_delay = delay
        self.dut.cfg_max_retries.value = max_retries
        self.dut.cfg_retry_delay.value = delay

    def set_profiles(self, cmd='fixed', rsp='fixed', slave='fixed'):
        self.cmd.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[cmd]['master']))
        self.rsp.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS[rsp]['slave']))
        self.slave.set_randomizer(FlexRandomizer(SLAVE_PROFILES[slave]))

    # ---- model ----------------------------------------------------------
    def _status_hook(self, pkt):
        adr = int(pkt.adr)
        if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
            return WB4_STATUS_ERR
        if RTY_ALWAYS[0] <= adr <= RTY_ALWAYS[1]:
            return WB4_STATUS_RTY
        if RTY_K_WINDOW[0] <= adr <= RTY_K_WINDOW[1]:
            left = self.rty_left.get(adr, self.rty_initial.get(adr, 0))
            self.rty_left[adr] = max(0, left - 1)
            return WB4_STATUS_RTY if left > 0 else WB4_STATUS_ACK
        return WB4_STATUS_ACK

    def _on_rsp(self, pkt):
        self.stats['responses'] += 1
        self.got.append((int(pkt.status), int(pkt.dat)))

    def _plan(self, rng, we, adr, dat, sel):
        """Decide the expected outcome of one command against the windows
        and the retry budget, updating the model as the bus will."""
        if ERR_WINDOW[0] <= adr <= ERR_WINDOW[1]:
            return WB4_STATUS_ERR, None
        if RTY_ALWAYS[0] <= adr <= RTY_ALWAYS[1]:
            self.expected_retries += self.max_retries
            self.expected_rty_to_fub += 1
            return WB4_STATUS_RTY, None
        if RTY_K_WINDOW[0] <= adr <= RTY_K_WINDOW[1]:
            # A fresh address draws its k; a repeated one carries what the
            # earlier commands left (the hook counts down the same way, one
            # RTY per presentation, so the model must be advanced here, at
            # plan time, not read back from the hook later).
            if adr not in self.rty_initial:
                self.rty_initial[adr] = rng.randint(1, 3)
                self.model_left[adr] = self.rty_initial[adr]
            left = self.model_left[adr]
            if left <= self.max_retries:
                self.expected_retries += left
                self.model_left[adr] = 0
            else:
                self.expected_retries += self.max_retries
                self.expected_rty_to_fub += 1
                self.model_left[adr] = left - (self.max_retries + 1)
                return WB4_STATUS_RTY, None
        # ACK: apply to the mirror
        if we:
            for i in range(self.SW):
                if sel >> i & 1:
                    self.mirror[adr + i] = (dat >> (8 * i)) & 0xFF
            return WB4_STATUS_ACK, None
        return WB4_STATUS_ACK, sum(self.mirror.get(adr + i, 0) << (8 * i) for i in range(self.SW))

    def _sequence(self, rng, count, mix):
        """The traffic for one phase, as a WB4Sequence.

        Three windows this DUT's slave decodes: ERR, retry-a-bounded-number
        (RTY_K) and retry-forever. With more than one command in flight the
        addresses are unique within the phase, so a retried write never
        reorders against a read of the same word -- the INFLIGHT > 1 hazard
        wb4_retry documents. Seeded from the TB's generator so the run stays
        reproducible.
        """
        seq = WB4Sequence("retry.traffic", addr_width=self.AW, data_width=self.DW,
                          seed=rng.getrandbits(32))
        seq.add_random_workload(
            count, addr_lo=0, addr_hi=0xD000, write_frac=0.5,
            align=True, random_sel=True, unique_addrs=(self.inflight > 1),
            windows=[(ERR_WINDOW[0], ERR_WINDOW[1], mix / 3),
                     (RTY_K_WINDOW[0], RTY_K_WINDOW[1], mix / 3),
                     (RTY_ALWAYS[0], RTY_ALWAYS[1], mix / 3)])
        return seq

    async def run_traffic(self, count, rng, mix=0.3, timeout_clocks=60000):
        start = self.stats['responses']
        pkts = []
        for t in self._sequence(rng, count, mix):
            we, adr, dat, sel = t.we, t.adr, t.dat_w, t.sel
            want_status, want_data = self._plan(rng, we, adr, dat, sel)
            self.sent.append((we, adr, dat, sel, want_status, want_data))
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
        while self.sent and self.got:
            we, adr, dat, sel, want_status, want_data = self.sent.popleft()
            status, rdat = self.got.popleft()
            if status != want_status or (want_data is not None and rdat != want_data):
                self.errors.append(f"adr=0x{adr:X} we={we}: response ({status}, 0x{rdat:X}) != "
                                   f"({want_status}, {want_data if want_data is None else hex(want_data)})")
                if len(self.errors) > 12:
                    break
        return not self.errors

    def report(self):
        v = self.mon.total_violations()
        if v:
            self.errors.append(f"{v} Wishbone protocol violation(s): {self.mon.violations}")
        rc = int(self.dut.retry_count.value)
        n = self.stats['sent']
        if rc != self.expected_retries:
            self.errors.append(f"retry_count {rc} != {self.expected_retries} expected re-issues")
        if self.mon.terminated != n + self.expected_retries:
            self.errors.append(f"monitor terminated {self.mon.terminated} != {n} commands + {self.expected_retries} retries")
        rty_on_bus = self.slave.stats.get('rty', 0)
        if rty_on_bus != self.expected_retries + self.expected_rty_to_fub:
            self.errors.append(f"slave RTY count {rty_on_bus} != {self.expected_retries} retried + "
                               f"{self.expected_rty_to_fub} passed to the FUB")
        self.log.info(f"sent={n} responses={self.stats['responses']} retry_count={rc} min_retry_gap={self.min_retry_gap} "
                      f"rty_to_fub={self.expected_rty_to_fub} slave={self.slave.stats} "
                      f"mon terminated={self.mon.terminated} max_inflight={self.mon.max_inflight} "
                      f"violations={v} errors={len(self.errors)}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
