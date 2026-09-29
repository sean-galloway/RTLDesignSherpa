# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi_write_engine_beats_tb
# Purpose: Testbench for axi_write_engine_beats (FUB level)
#
# Documentation: projects/components/dma-ip/rapids/docs/rapids_beats_mas/ch02_fub_blocks/04_axi_write_engine.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2026-09-27
"""
Testbench for axi_write_engine_beats.

    sched_wr_*   --->  [ axi_write_engine_beats ]  ---> m_axi_aw*/w*/b*  (memory)
    SRAM drain   <---                              <--- axi_wr_sram_*     (ID-select read)

- **AXI4 write slave (framework BFM)** on `m_axi_*`, backed by a MemoryModel,
  so the test can read back exactly what landed at each address after the B
  responses. Its AW and W callbacks are also the model's bookkeeping source:
  an accepted AW reserves that burst's beats in the SRAM model, an accepted W
  beat pops one. Keying the model off the BFM's handshakes (rather than
  sampling the engine's combinational `axi_wr_drain_req` / `axi_wr_sram_drain`
  from Python) removes the same-timestep ordering race between a monitor and
  a level driver.
- **`_sram_drain_model`** (one coroutine) owns the engine's ID-select read
  port, which is the SRAM controller's own interface and has no valid/ready
  BFM: per channel a queue of beats and a reserved count, driving
  `axi_wr_sram_valid` / `_valid_comb` (queue non-empty),
  `axi_wr_drain_data_avail` (queued minus reserved) and `axi_wr_sram_data`
  (head of the queue the engine selects with `axi_wr_sram_id`). A `trickle`
  fill mode feeds beats in slowly so the data-available gating is exercised.
- **`_scheduler_model`** holds `sched_wr_valid[ch]` while beats remain and
  reacts to the done (AW issued) and commit (B seen) strobes the way
  `scheduler_beats` does.

Checks: memory equals the beats each channel queued, address by address; the
engine never reserves more than the model has queued nor pops an empty queue;
AW attributes (INCR, size = bus width, len <= cfg); done and commit strobes
both sum to the request; debug counters agree; `sched_wr_error` stays 0.
"""
import os
import random
from collections import deque
from typing import Dict, List

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_wr
from CocoTBFramework.components.shared.memory_model import MemoryModel
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_levels import PROFILE


def _pkt_field(pkt, *names):
    for n in names:
        try:
            v = getattr(pkt, n)
            if v is not None:
                return int(v)
        except AttributeError:
            pass
        fields = getattr(pkt, 'fields', None)
        if fields and n in fields:
            return int(fields[n])
    raise KeyError(f"packet has none of {names}")


class AxiWriteEngineBeatsTB(TBBase):
    """FUB testbench for axi_write_engine_beats."""

    CH_STRIDE = 0x4000          # bytes of memory per channel (16 KB: FULL odd sizes reach 159 x 64 B)

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.clk = dut.clk
        self.rst_n = dut.rst_n

        self.NC = int(dut.NUM_CHANNELS.value)
        self.AW = int(dut.ADDR_WIDTH.value)
        self.DW = int(dut.DATA_WIDTH.value)
        self.IW = int(dut.ID_WIDTH.value)
        self.UW = int(dut.USER_WIDTH.value)
        self.SCW = int(dut.SEG_COUNT_WIDTH.value)
        self.PIPELINE = int(dut.PIPELINE.value)
        self.bytes_per_beat = self.DW // 8

        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.seed = int(os.environ.get('SEED', '0'))
        random.seed(self.seed)
        self.log.info(f"axi_write_engine_beats TB: NC={self.NC} DW={self.DW} IW={self.IW} UW={self.UW} "
                      f"SCW={self.SCW} PIPELINE={self.PIPELINE} level={self.test_level} seed={self.seed}")

        self.xfer_cfg = int(os.environ.get('TEST_XFER_CFG', '7'))       # cfg_axi_wr_xfer_beats (AxLEN-style)
        self.fill_mode = os.environ.get('TEST_FILL_MODE', 'prefill')     # prefill | trickle
        self.trickle_gap = int(os.environ.get('TEST_TRICKLE_GAP', '3'))  # cycles between trickled beats
        # sram_controller flops data_avail at its boundary: the engine sees a
        # reservation one cycle after the AW; the model matches that.
        self.report_delay = int(os.environ.get('TEST_REPORT_DELAY', '1'))
        self._view_pipe: deque = deque()

        # SRAM model
        self.queue: List[deque] = [deque() for _ in range(self.NC)]
        self.reserved: List[int] = [0] * self.NC
        self.pending_fill: List[deque] = [deque() for _ in range(self.NC)]
        self.over_reserve = 0
        self.empty_pop = 0
        self.orphan_w = 0
        self.aw_bursts: deque = deque()   # [ch, beats_left] in AW order
        # scheduler model / scoreboard
        self.remaining: List[int] = [0] * self.NC
        self.addr: List[int] = [0] * self.NC
        self.issued: List[int] = [0] * self.NC
        self.committed: List[int] = [0] * self.NC
        self.expected: Dict[int, List[int]] = {}
        self.aw_count = 0
        self.aw_violations = 0
        self.max_outstanding = int(dut.AW_MAX_OUTSTANDING.value) if self.PIPELINE else 1
        self.open_bursts: List[int] = [0] * self.NC      # AWs issued, B not yet seen
        self.next_addr: List[int] = [0] * self.NC
        self.outstanding_violations = 0
        self.addr_violations = 0
        self.w_beats = 0
        self.wuser_bad = 0
        self.cycle = 0
        self._models_running = False

        self.memory_model = None
        self.axi_slave = None

    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)
        await self._create_bfms()

    async def assert_reset(self):
        self.rst_n.value = 0
        self.dut.cfg_axi_wr_xfer_beats.value = self.xfer_cfg
        self.dut.sched_wr_valid.value = 0
        self.dut.sched_wr_addr.value = 0
        self.dut.sched_wr_beats.value = 0
        self.dut.sched_wr_burst_len.value = self._pack([self.xfer_cfg] * self.NC, 8)
        self.dut.axi_wr_drain_data_avail.value = 0
        self.dut.axi_wr_sram_valid.value = 0
        self.dut.axi_wr_sram_valid_comb.value = 0
        self.dut.axi_wr_sram_data.value = 0
        self.dut.m_axi_awready.value = 0
        self.dut.m_axi_wready.value = 0
        self.dut.m_axi_bvalid.value = 0
        self.dut.m_axi_bid.value = 0
        self.dut.m_axi_bresp.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    async def _create_bfms(self):
        total_bytes = self.NC * self.CH_STRIDE
        self.memory_model = MemoryModel(num_lines=total_bytes // self.bytes_per_beat,
                                        bytes_per_line=self.bytes_per_beat, log=self.log)
        self.axi_slave = create_axi4_slave_wr(
            dut=self.dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.DW, id_width=self.IW, addr_width=self.AW, user_width=self.UW,
            multi_sig=True, memory_model=self.memory_model)
        self.axi_slave['AW'].add_callback(self._on_aw)
        self.axi_slave['W'].add_callback(self._on_w)
        for ch in ('AW', 'W', 'B'):
            comp = self.axi_slave.get(ch)
            if comp is not None and hasattr(comp, 'reset_bus'):
                await comp.reset_bus()
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    # ------------------------------------------------------------------
    # callbacks (the BFM saw the handshake; the model books it)
    # ------------------------------------------------------------------
    def _on_aw(self, pkt):
        self.aw_count += 1
        ch = _pkt_field(pkt, 'id', 'awid') & (self.NC - 1) if self.NC > 1 else 0
        awlen = _pkt_field(pkt, 'len', 'awlen')
        awsize = _pkt_field(pkt, 'size', 'awsize')
        awburst = _pkt_field(pkt, 'burst', 'awburst')
        awaddr = _pkt_field(pkt, 'addr', 'awaddr')
        bad = []
        if self.open_bursts[ch] >= self.max_outstanding:
            self.outstanding_violations += 1
            bad.append(f"ch{ch} already has {self.open_bursts[ch]} burst(s) outstanding (limit {self.max_outstanding})")
        if awaddr != self.next_addr[ch]:
            self.addr_violations += 1
            bad.append(f"ch{ch} awaddr 0x{awaddr:x}, expected 0x{self.next_addr[ch]:x}")
        self.next_addr[ch] = awaddr + (awlen + 1) * self.bytes_per_beat
        self.open_bursts[ch] += 1
        if awlen > self.xfer_cfg:
            bad.append(f"len {awlen} > cfg {self.xfer_cfg}")
        if awsize != (self.DW // 8).bit_length() - 1:
            bad.append(f"size {awsize}")
        if awburst != 1:
            bad.append(f"burst {awburst} != INCR")
        if bad:
            if not any(x.startswith('ch') for x in bad):
                self.aw_violations += 1
            self.log.error(f"AW #{self.aw_count} ch{ch}: " + ", ".join(bad))
        size = awlen + 1
        if self.reserved[ch] + size > len(self.queue[ch]):
            self.over_reserve += 1
            self.log.error(f"ch{ch}: AW reserves {size} beats with {len(self.queue[ch]) - self.reserved[ch]} unreserved")
        self.reserved[ch] += size
        self.aw_bursts.append([ch, size])

    def _on_w(self, pkt):
        """A W beat the BFM accepted. W is in order with AW (the engine's W-phase
        FIFO), so the burst at the head of the AW list says which channel's beat
        this is; wuser must agree."""
        self.w_beats += 1
        if not self.aw_bursts:
            self.orphan_w += 1
            self.log.error("W beat accepted with no AW outstanding")
            return
        ch = self.aw_bursts[0][0]
        try:
            user = _pkt_field(pkt, 'user', 'wuser')
            if user != ch:
                self.wuser_bad += 1
                if self.wuser_bad <= 5:
                    self.log.error(f"W beat wuser={user}, burst belongs to ch{ch}")
        except KeyError:
            pass
        self.aw_bursts[0][1] -= 1
        if self.aw_bursts[0][1] == 0:
            self.aw_bursts.popleft()
        if not self.queue[ch]:
            self.empty_pop += 1
            self.log.error(f"ch{ch}: W beat accepted with an empty SRAM queue")
            return
        self.queue[ch].popleft()
        self.reserved[ch] = max(0, self.reserved[ch] - 1)

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Ready-delay profile on the AXI slave's AW and W channels (bus backpressure)."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]['slave']
        for chn in ('AW', 'W'):
            comp = self.axi_slave.get(chn)
            if comp is not None and hasattr(comp, 'randomizer'):
                comp.randomizer = FlexRandomizer(cfg)
        self.log.info(f"GAXI m_axi AW/W ready timing profile: {profile_name}")

    # ------------------------------------------------------------------
    @staticmethod
    def _pack(values, width):
        v = 0
        for i, x in enumerate(values):
            v |= (int(x) & ((1 << width) - 1)) << (i * width)
        return v

    def _unpack(self, value, width):
        return [(int(value) >> (i * width)) & ((1 << width) - 1) for i in range(self.NC)]

    # ------------------------------------------------------------------
    # level-driven models
    # ------------------------------------------------------------------
    async def _sram_drain_model(self):
        """Drive the ID-select read port from the per-channel queues, one
        cycle at a time (after the edge, once registered outputs have settled)."""
        while self._models_running:
            await RisingEdge(self.clk)
            self.cycle += 1
            await Timer(1, 'ns')
            # trickle fill: one beat per channel every trickle_gap cycles
            if self.fill_mode == 'trickle' and self.cycle % self.trickle_gap == 0:
                for ch in range(self.NC):
                    if self.pending_fill[ch]:
                        self.queue[ch].append(self.pending_fill[ch].popleft())
            valid = 0
            avail = []
            for ch in range(self.NC):
                n = len(self.queue[ch])
                if n:
                    valid |= 1 << ch
                avail.append(min(max(0, n - self.reserved[ch]), (1 << self.SCW) - 1))
            sel = int(self.dut.axi_wr_sram_id.value)
            self.dut.axi_wr_sram_valid.value = valid
            self.dut.axi_wr_sram_valid_comb.value = valid
            self._view_pipe.append(self._pack(avail, self.SCW))
            while len(self._view_pipe) > self.report_delay + 1:
                self._view_pipe.popleft()
            self.dut.axi_wr_drain_data_avail.value = self._view_pipe[0]
            self.dut.axi_wr_sram_data.value = self.queue[sel][0] if self.queue[sel] else 0

    async def _scheduler_model(self):
        while self._models_running:
            await RisingEdge(self.clk)
            await Timer(1, 'ns')
            done = int(self.dut.sched_wr_done_strobe.value)
            if done:
                nb = self._unpack(self.dut.sched_wr_beats_done.value, 32)
                for ch in range(self.NC):
                    if (done >> ch) & 1:
                        self.issued[ch] += nb[ch]
                        self.remaining[ch] = max(0, self.remaining[ch] - nb[ch])
                        self.addr[ch] += nb[ch] * self.bytes_per_beat
            commit = int(self.dut.sched_wr_commit_strobe.value)
            if commit:
                nb = self._unpack(self.dut.sched_wr_commit_beats.value, 32)
                for ch in range(self.NC):
                    if (commit >> ch) & 1:
                        self.committed[ch] += nb[ch]
                        self.open_bursts[ch] = max(0, self.open_bursts[ch] - 1)
            self.dut.sched_wr_valid.value = sum((1 << ch) for ch in range(self.NC) if self.remaining[ch] > 0)
            self.dut.sched_wr_addr.value = self._pack(self.addr, self.AW)
            self.dut.sched_wr_beats.value = self._pack(self.remaining, 32)

    # ------------------------------------------------------------------
    def _plan(self, beats_per_channel: Dict[int, int]):
        for ch, n in beats_per_channel.items():
            assert n * self.bytes_per_beat <= self.CH_STRIDE
            self.addr[ch] = ch * self.CH_STRIDE
            self.next_addr[ch] = ch * self.CH_STRIDE
            self.remaining[ch] = n
            self.issued[ch] = self.committed[ch] = 0
            beats = [random.getrandbits(self.DW) for _ in range(n)]
            self.expected[ch] = beats
            target = self.pending_fill[ch] if self.fill_mode == 'trickle' else self.queue[ch]
            target.extend(beats)

    async def run_transfer(self, beats_per_channel: Dict[int, int], timeout_cycles: int = 60000):
        total = sum(beats_per_channel.values())
        self._plan(beats_per_channel)
        if not self._models_running:
            self._models_running = True
            cocotb.start_soon(self._sram_drain_model())
            cocotb.start_soon(self._scheduler_model())
        start = self.cycle
        finished = False
        while self.cycle - start < timeout_cycles:
            await RisingEdge(self.clk)
            if sum(self.committed) >= total and all(r == 0 for r in self.remaining):
                await self.wait_clocks('clk', 20)
                finished = True
                break
        self._report(beats_per_channel, finished)

    def _report(self, beats_per_channel, finished):
        errs = []
        total = sum(beats_per_channel.values())
        if not finished:
            errs.append(f"timeout: committed {sum(self.committed)} of {total} beats, remaining={self.remaining}, "
                        f"queued={[len(q) for q in self.queue]} reserved={self.reserved}")
        for ch, n in beats_per_channel.items():
            if self.issued[ch] != n:
                errs.append(f"ch{ch}: done strobes report {self.issued[ch]} beats, expected {n}")
            if self.committed[ch] != n:
                errs.append(f"ch{ch}: commit strobes report {self.committed[ch]} beats, expected {n}")
            base = ch * self.CH_STRIDE
            bad = 0
            for b, exp in enumerate(self.expected[ch]):
                got = self.memory_model.bytearray_to_integer(
                    self.memory_model.read(base + b * self.bytes_per_beat, self.bytes_per_beat))
                if got != exp:
                    bad += 1
                    if bad <= 5:
                        self.log.error(f"ch{ch} beat {b} @0x{base + b * self.bytes_per_beat:x}: "
                                       f"memory 0x{got:x} expected 0x{exp:x}")
            if bad:
                errs.append(f"ch{ch}: {bad} of {n} beats wrong in memory")
            if self.queue[ch]:
                errs.append(f"ch{ch}: {len(self.queue[ch])} beats left in the SRAM model")
        if self.over_reserve:
            errs.append(f"{self.over_reserve} AW commands reserved beyond the queued data")
        if self.empty_pop:
            errs.append(f"{self.empty_pop} W beats taken from an empty queue")
        if self.orphan_w:
            errs.append(f"{self.orphan_w} W beats with no AW outstanding")
        if self.aw_bursts:
            errs.append(f"{len(self.aw_bursts)} AW bursts never completed their W beats")
        if self.aw_violations:
            errs.append(f"{self.aw_violations} AW commands violated len/size/burst")
        if self.outstanding_violations:
            errs.append(f"{self.outstanding_violations} AW commands exceeded the per-channel outstanding limit")
        if self.addr_violations:
            errs.append(f"{self.addr_violations} AW commands carried an address that did not follow the previous burst")
        if self.wuser_bad:
            errs.append(f"{self.wuser_bad} W beats carried a wuser that is not the selected channel")
        err_bits = int(self.dut.sched_wr_error.value)
        if err_bits:
            errs.append(f"sched_wr_error = 0x{err_bits:x}")
        aw = int(self.dut.dbg_aw_transactions.value)
        wb = int(self.dut.dbg_w_beats.value)
        if aw != self.aw_count or wb != total or self.w_beats != total:
            errs.append(f"debug counters: aw_transactions={aw} (BFM saw {self.aw_count}), "
                        f"w_beats={wb} (BFM saw {self.w_beats}), expected beats {total}")
        complete = int(self.dut.dbg_wr_all_complete.value)
        if complete != (1 << self.NC) - 1:
            errs.append(f"dbg_wr_all_complete = 0x{complete:x}, expected all channels idle")
        self.log.info(f"transfer: {total} beats over {len(beats_per_channel)} channels, "
                      f"{self.aw_count} AW commands, cfg len {self.xfer_cfg}, fill mode {self.fill_mode}")
        assert not errs, "; ".join(errs)

    # ------------------------------------------------------------------
    def _depth(self):
        # rapids_levels.PROFILE is the one depth table for the area (tooling BUG-004).
        return PROFILE.get(self.test_level, PROFILE['gate'])['axi_engine_beats']

    async def test_single_channel(self):
        lo, hi = self._depth()
        await self.run_transfer({0: random.randint(lo, hi)})

    async def test_all_channels(self):
        lo, hi = self._depth()
        await self.run_transfer({ch: random.randint(lo, hi) for ch in range(self.NC)})

    async def test_odd_sizes(self):
        burst = self.xfer_cfg + 1
        sizes = [1, burst - 1, burst + 1, 2 * burst + 3]
        if self.test_level == 'full':
            sizes += [3 * burst + 1, 5 * burst - 1]
        await self.run_transfer({ch: sizes[ch % len(sizes)] for ch in range(self.NC)})

    async def test_trickle(self):
        """Data arrives in the SRAM slower than the bus drains it: the engine must
        wait on data_avail and never issue an AW it cannot feed."""
        self.fill_mode = 'trickle'
        lo, hi = self._depth()
        await self.run_transfer({ch: random.randint(lo, hi) for ch in range(self.NC)})
