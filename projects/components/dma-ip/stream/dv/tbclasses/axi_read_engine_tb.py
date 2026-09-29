# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module (ported from rapids' identical engine, 2026-09-29): axi_read_engine_tb
# Purpose: Testbench for axi_read_engine (FUB level)
#
# Documentation: projects/components/dma-ip/stream/docs/stream_mas/ch02_blocks/06_axi_read_engine.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2026-09-27
"""
Testbench for axi_read_engine.

The engine sits between per-channel scheduler requests and the SRAM controller:

    sched_rd_*  --->  [ axi_read_engine ]  ---> m_axi_ar*/r*  (memory)
    alloc space <---                             ---> axi_rd_sram_* (SRAM fill)

Three things surround it here, and each is the standard collateral for its
interface:

- **AXI4 read slave (framework BFM)** on `m_axi_*`, backed by a MemoryModel
  the test pre-fills with random beats, so every R beat has a known value.
- **GAXI slave (framework BFM)** on `axi_rd_sram_*` (valid/ready/id/data): it
  applies the ready-delay timing profile and hands every accepted beat to the
  scoreboard through a callback.
- **Two level-driven models**, each in one named coroutine, for the engine's
  own non-handshake interfaces: `_scheduler_model` holds `sched_rd_valid`
  while a channel has beats left and advances address/remaining on
  `sched_rd_done_strobe` exactly as `scheduler_beats` does;
  `_sram_space_model` owns `axi_rd_alloc_space_free`, debiting it on every
  `axi_rd_alloc_req` pulse and crediting it as the GAXI slave accepts beats
  (optionally after a drain delay). These are the level/pulse ports a
  valid/ready BFM cannot speak.

Checks: every channel receives exactly its beats, in order, equal to memory;
the engine never allocates more space than the model reports free; AR
attributes (INCR, size = bus width, len <= cfg) on every command; done-strobe
beats sum to the request; the debug counters agree; no channel raises
`sched_rd_error`.
"""
import os
import random
from collections import deque
from typing import Dict, List

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_slave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel
# Per-level depth for this ported suite: the rapids_levels 'axi_engine_beats' values
# (the engines are the same contract; STREAM keeps no levels table of its own).
PROFILE = {lvl: {'axi_engine_beats': d} for lvl, d in {'gate': (16, 32), 'func': (32, 96), 'full': (64, 120)}.items()}


def _pkt_field(pkt, *names):
    """Read the first present field of a framework packet (attribute or dict)."""
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


class AxiReadEngineTB(TBBase):
    """FUB testbench for axi_read_engine."""

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
        self.SCW = int(dut.SEG_COUNT_WIDTH.value)
        self.PIPELINE = int(dut.PIPELINE.value)
        self.bytes_per_beat = self.DW // 8

        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.seed = int(os.environ.get('SEED', '0'))
        random.seed(self.seed)
        self.log.info(f"axi_read_engine TB: NC={self.NC} DW={self.DW} IW={self.IW} "
                      f"SCW={self.SCW} PIPELINE={self.PIPELINE} level={self.test_level} seed={self.seed}")

        # knobs
        self.xfer_cfg = int(os.environ.get('TEST_XFER_CFG', '7'))           # cfg_axi_rd_xfer_beats (AxLEN-style)
        self.sram_depth = int(os.environ.get('TEST_SRAM_DEPTH', '64'))      # modelled free space per channel
        self.release_delay = int(os.environ.get('TEST_RELEASE_DELAY', '0'))  # cycles before a consumed beat frees space
        # The real reporting chain shows a debit 2 cycles after the alloc pulse
        # (stream_alloc_ctrl count, then sram_controller's boundary flop); the
        # model delays its driven view by the same amount so the engine is
        # tested against the staleness it meets in the data path.
        self.report_delay = int(os.environ.get('TEST_REPORT_DELAY', '2'))
        assert self.sram_depth < (1 << self.SCW), "modelled depth must fit SEG_COUNT_WIDTH"
        # stream BUG-018 (rapids BUG-009): a burst can never exceed the buffer SEG_COUNT_WIDTH
        # encodes (2^(SCW-1) beats), nor 255 beats (the 8-bit size ports). The
        # engine clamps the configured AxLEN to this; every AR must honour it.
        self.arlen_cap = min(self.xfer_cfg, (1 << (self.SCW - 1)) - 1, 254)
        self.max_arlen_seen = -1

        # models / scoreboard
        self.space_free: List[int] = [self.sram_depth] * self.NC
        self.release_q: deque = deque()          # (cycle, ch)
        self._view_pipe: deque = deque()         # delayed space_free views
        self.cycle = 0
        self.remaining: List[int] = [0] * self.NC
        self.addr: List[int] = [0] * self.NC
        self.issued: List[int] = [0] * self.NC   # beats reported by done strobes
        self.expected: List[deque] = [deque() for _ in range(self.NC)]
        self.received: List[int] = [0] * self.NC
        self.mismatches = 0
        self.over_alloc = 0
        self.ar_violations = 0
        self.ar_count = 0
        self.max_outstanding = int(dut.AR_MAX_OUTSTANDING.value) if self.PIPELINE else 1
        self.outstanding: List[deque] = [deque() for _ in range(self.NC)]   # beats left per open burst
        self.next_addr: List[int] = [0] * self.NC   # address the channel's next AR must carry
        self.outstanding_violations = 0
        self.addr_violations = 0
        self._models_running = False

        self.memory_model = None
        self.axi_slave = None
        self.sram_slave = None

    # ------------------------------------------------------------------
    # mandatory three
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
        self.dut.cfg_axi_rd_xfer_beats.value = self.xfer_cfg
        self.dut.sched_rd_valid.value = 0
        self.dut.sched_rd_addr.value = 0
        self.dut.sched_rd_beats.value = 0
        self.dut.axi_rd_alloc_space_free.value = self._pack(self.space_free, self.SCW)
        self.dut.m_axi_arready.value = 0
        self.dut.m_axi_rvalid.value = 0
        self.dut.m_axi_rid.value = 0
        self.dut.m_axi_rdata.value = 0
        self.dut.m_axi_rresp.value = 0
        self.dut.m_axi_rlast.value = 0
        self.dut.axi_rd_sram_ready.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ------------------------------------------------------------------
    # BFMs
    # ------------------------------------------------------------------
    async def _create_bfms(self):
        total_bytes = self.NC * self.CH_STRIDE
        self.memory_model = MemoryModel(num_lines=total_bytes // self.bytes_per_beat,
                                        bytes_per_line=self.bytes_per_beat, log=self.log)
        self.axi_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="m_axi_", log=self.log,
            data_width=self.DW, id_width=self.IW, addr_width=self.AW, user_width=1,
            multi_sig=True, memory_model=self.memory_model)
        self.axi_slave['AR'].add_callback(self._on_ar)

        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='id', bits=self.IW, format='dec', description='channel id'))
        fc.add_field(FieldDefinition(name='data', bits=self.DW, format='hex', description='beat'))
        self.sram_slave = create_gaxi_slave(
            dut=self.dut, title='rd_sram', prefix='axi_rd_sram', clock=self.clk,
            field_config=fc, multi_sig=True, log=self.log, mode='skid')
        self.sram_slave.add_callback(self._on_sram_beat)
        await self.sram_slave.reset_bus()
        for ch in ('AR', 'R'):
            comp = self.axi_slave.get(ch)
            if comp is not None and hasattr(comp, 'reset_bus'):
                await comp.reset_bus()
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Ready-delay profile on the SRAM-side GAXI slave (the engine's consumer)."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        self.sram_slave.randomizer = FlexRandomizer(GAXI_RANDOMIZER_CONFIGS[profile_name]['slave'])
        self.log.info(f"GAXI axi_rd_sram timing profile: {profile_name}")

    # ------------------------------------------------------------------
    # callbacks
    # ------------------------------------------------------------------
    def _on_sram_beat(self, pkt):
        ch = _pkt_field(pkt, 'id') & (self.NC - 1) if self.NC > 1 else 0
        data = _pkt_field(pkt, 'data')
        if not self.expected[ch]:
            self.mismatches += 1
            self.log.error(f"ch{ch}: unexpected beat 0x{data:x} (nothing outstanding)")
        else:
            exp = self.expected[ch].popleft()
            if data != exp:
                self.mismatches += 1
                if self.mismatches <= 10:
                    self.log.error(f"ch{ch} beat {self.received[ch]}: got 0x{data:x} expected 0x{exp:x}")
        self.received[ch] += 1
        self.release_q.append((self.cycle + self.release_delay, ch))
        if self.outstanding[ch]:
            self.outstanding[ch][0] -= 1
            if self.outstanding[ch][0] == 0:
                self.outstanding[ch].popleft()

    def _on_ar(self, pkt):
        self.ar_count += 1
        arlen = _pkt_field(pkt, 'len', 'arlen')
        arsize = _pkt_field(pkt, 'size', 'arsize')
        arburst = _pkt_field(pkt, 'burst', 'arburst')
        ch = _pkt_field(pkt, 'id', 'arid') & (self.NC - 1) if self.NC > 1 else 0
        araddr = _pkt_field(pkt, 'addr', 'araddr')
        bad = []
        # outstanding contract: PIPELINE=0 is one burst per channel, PIPELINE=1
        # at most AR_MAX_OUTSTANDING. A stale arbiter grant re-issuing a channel
        # the cycle after its AR shows up here (rapids BUG-004, second form).
        if len(self.outstanding[ch]) >= self.max_outstanding:
            self.outstanding_violations += 1
            bad.append(f"ch{ch} already has {len(self.outstanding[ch])} burst(s) outstanding (limit {self.max_outstanding})")
        # each AR must carry the address the previous one advanced to
        if araddr != self.next_addr[ch]:
            self.addr_violations += 1
            bad.append(f"ch{ch} araddr 0x{araddr:x}, expected 0x{self.next_addr[ch]:x}")
        self.next_addr[ch] = araddr + (arlen + 1) * self.bytes_per_beat
        self.outstanding[ch].append(arlen + 1)
        self.max_arlen_seen = max(self.max_arlen_seen, arlen)
        if arlen > self.arlen_cap:
            bad.append(f"len {arlen} > cap {self.arlen_cap} (cfg {self.xfer_cfg}, SCW {self.SCW})")
        if arsize != (self.DW // 8).bit_length() - 1:
            bad.append(f"size {arsize}")
        if arburst != 1:
            bad.append(f"burst {arburst} != INCR")
        if bad:
            if not any(x.startswith('ch') for x in bad):
                self.ar_violations += 1
            self.log.error(f"AR #{self.ar_count}: " + ", ".join(bad))

    # ------------------------------------------------------------------
    # packed-array helpers ([NC-1:0][W-1:0] ports)
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
    # level-driven models (one coroutine each; these ports have no BFM)
    # ------------------------------------------------------------------
    async def _scheduler_model(self):
        """Hold sched_rd_valid[ch] while beats remain; consume done strobes the way
        scheduler_beats does (remaining -= beats_done, addr += beats_done * bytes)."""
        while self._models_running:
            await RisingEdge(self.clk)
            await Timer(1, 'ns')
            strobes = int(self.dut.sched_rd_done_strobe.value)
            if strobes:
                done = self._unpack(self.dut.sched_rd_beats_done.value, 32)
                for ch in range(self.NC):
                    if (strobes >> ch) & 1:
                        n = done[ch]
                        self.issued[ch] += n
                        self.remaining[ch] = max(0, self.remaining[ch] - n)
                        self.addr[ch] += n * self.bytes_per_beat
            self.dut.sched_rd_valid.value = sum((1 << ch) for ch in range(self.NC) if self.remaining[ch] > 0)
            self.dut.sched_rd_addr.value = self._pack(self.addr, self.AW)
            self.dut.sched_rd_beats.value = self._pack(self.remaining, 32)

    async def _sram_space_model(self):
        """Own axi_rd_alloc_space_free: debit on every alloc pulse, credit when the
        SRAM-side slave has taken a beat (plus TEST_RELEASE_DELAY cycles)."""
        while self._models_running:
            await RisingEdge(self.clk)
            self.cycle += 1
            await Timer(1, 'ns')
            if int(self.dut.axi_rd_alloc_req.value):
                size = int(self.dut.axi_rd_alloc_size.value)
                ch = int(self.dut.axi_rd_alloc_id.value) & (self.NC - 1) if self.NC > 1 else 0
                if size > self.space_free[ch]:
                    self.over_alloc += 1
                    self.log.error(f"ch{ch}: alloc {size} beats with only {self.space_free[ch]} free")
                self.space_free[ch] -= size
            while self.release_q and self.release_q[0][0] <= self.cycle:
                _, ch = self.release_q.popleft()
                self.space_free[ch] += 1
            view = self._pack([max(0, min(s, (1 << self.SCW) - 1)) for s in self.space_free], self.SCW)
            self._view_pipe.append(view)
            while len(self._view_pipe) > self.report_delay + 1:
                self._view_pipe.popleft()
            self.dut.axi_rd_alloc_space_free.value = self._view_pipe[0]

    # ------------------------------------------------------------------
    # stimulus
    # ------------------------------------------------------------------
    def _plan(self, beats_per_channel: Dict[int, int]):
        """Fill memory with random beats for each channel's region and queue the
        expected sequence."""
        for ch, n in beats_per_channel.items():
            base = ch * self.CH_STRIDE
            assert n * self.bytes_per_beat <= self.CH_STRIDE
            self.addr[ch] = base
            self.next_addr[ch] = base
            self.remaining[ch] = n
            self.issued[ch] = 0
            self.received[ch] = 0
            for b in range(n):
                val = random.getrandbits(self.DW)
                self.memory_model.write(base + b * self.bytes_per_beat,
                                        self.memory_model.integer_to_bytearray(val, self.bytes_per_beat))
                self.expected[ch].append(val)

    async def _run_until_done(self, total: int, timeout_cycles: int):
        start = self.cycle
        while self.cycle - start < timeout_cycles:
            await RisingEdge(self.clk)
            if sum(self.received) >= total and all(r == 0 for r in self.remaining):
                # let the engine retire the last outstanding bookkeeping
                await self.wait_clocks('clk', 20)
                return True
        return False

    async def run_transfer(self, beats_per_channel: Dict[int, int], timeout_cycles: int = 60000):
        total = sum(beats_per_channel.values())
        self._plan(beats_per_channel)
        if not self._models_running:
            self._models_running = True
            cocotb.start_soon(self._scheduler_model())
            cocotb.start_soon(self._sram_space_model())
        ok = await self._run_until_done(total, timeout_cycles)
        self._report(beats_per_channel, ok)

    def _report(self, beats_per_channel, finished):
        errs = []
        if not finished:
            errs.append(f"timeout: received {sum(self.received)} of {sum(beats_per_channel.values())} beats, "
                        f"remaining={self.remaining} space={self.space_free}")
        for ch, n in beats_per_channel.items():
            if self.received[ch] != n:
                errs.append(f"ch{ch}: received {self.received[ch]} beats, expected {n}")
            if self.issued[ch] != n:
                errs.append(f"ch{ch}: done strobes report {self.issued[ch]} beats, expected {n}")
            if self.expected[ch]:
                errs.append(f"ch{ch}: {len(self.expected[ch])} expected beats never arrived")
        if self.mismatches:
            errs.append(f"{self.mismatches} data mismatches")
        if self.over_alloc:
            errs.append(f"{self.over_alloc} allocations exceeded the free space the model reported")
        if self.ar_violations:
            errs.append(f"{self.ar_violations} AR commands violated len/size/burst")
        if self.outstanding_violations:
            errs.append(f"{self.outstanding_violations} AR commands exceeded the per-channel outstanding limit")
        if self.addr_violations:
            errs.append(f"{self.addr_violations} AR commands carried an address that did not follow the previous burst")
        err_bits = int(self.dut.sched_rd_error.value)
        if err_bits:
            errs.append(f"sched_rd_error = 0x{err_bits:x}")
        rcvd = int(self.dut.dbg_r_beats_rcvd.value)
        writes = int(self.dut.dbg_sram_writes.value)
        total = sum(beats_per_channel.values())
        if rcvd != total or writes != total:
            errs.append(f"debug counters: r_beats_rcvd={rcvd} sram_writes={writes}, expected {total}")
        complete = int(self.dut.dbg_rd_all_complete.value)
        if complete != (1 << self.NC) - 1:
            errs.append(f"dbg_rd_all_complete = 0x{complete:x}, expected all channels idle")
        self.log.info(f"transfer: {total} beats over {len(beats_per_channel)} channels, "
                      f"{self.ar_count} AR commands, cfg len {self.xfer_cfg}, "
                      f"space model depth {self.sram_depth}, release delay {self.release_delay}, "
                      f"report delay {self.report_delay}")
        assert not errs, "; ".join(errs)

    # ------------------------------------------------------------------
    # tests (depth gated by TEST_LEVEL)
    # ------------------------------------------------------------------
    def _depth(self):
        # PROFILE above mirrors rapids_levels for this ported suite.
        return PROFILE.get(self.test_level, PROFILE['gate'])['axi_engine_beats']

    async def test_single_channel(self):
        lo, hi = self._depth()
        await self.run_transfer({0: random.randint(lo, hi)})

    async def test_all_channels(self):
        lo, hi = self._depth()
        await self.run_transfer({ch: random.randint(lo, hi) for ch in range(self.NC)})

    async def test_odd_sizes(self):
        """Beat counts that are not multiples of the burst length, including 1."""
        burst = self.xfer_cfg + 1
        sizes = [1, burst - 1, burst + 1, 2 * burst + 3]
        if self.test_level == 'full':
            sizes += [3 * burst + 1, 5 * burst - 1]
        plan = {ch: sizes[ch % len(sizes)] for ch in range(self.NC)}
        await self.run_transfer(plan)

    async def test_space_starved(self):
        """Free space smaller than two bursts: the engine must wait for releases
        and never allocate past what the model reports."""
        self.sram_depth = max(self.xfer_cfg + 1, min(self.sram_depth, 2 * (self.xfer_cfg + 1) - 1))
        self.space_free = [self.sram_depth] * self.NC
        self.release_delay = max(self.release_delay, 8)
        lo, hi = self._depth()
        await self.run_transfer({ch: random.randint(lo, hi) for ch in range(self.NC)})

    async def test_burst_cap(self):
        """stream BUG-018 (rapids BUG-009): cfg AxLEN above what the buffer holds, with the space
        model sized to that buffer. Every AR must carry the cap (the final
        burst of a channel may be shorter), no allocation may exceed the free
        space, the transfer must complete, and at least one full-cap AR must
        be seen so the check is not vacuous. Before the fix the 8-bit '+1'
        wrapped a 256-beat request to 0: space_ok passed on any free count and
        the engine over-fetched past the buffer."""
        cap = self.arlen_cap
        assert cap < self.xfer_cfg, f"cfg {self.xfer_cfg} does not exceed the cap {cap}; nothing to test"
        self.sram_depth = 1 << (self.SCW - 1)
        self.space_free = [self.sram_depth] * self.NC
        plan = {ch: (cap + 1) * (2 + ch % 2) + ch for ch in range(self.NC)}   # >= 2 full bursts each
        await self.run_transfer(plan)
        assert self.max_arlen_seen == cap, \
            f"no AR carried the cap length {cap} (longest seen {self.max_arlen_seen})"
