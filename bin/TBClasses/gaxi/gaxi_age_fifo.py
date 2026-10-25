# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GaxiAgeFifoTB
# Purpose: Testbench for gaxi_age_fifo_sync - age-carrying GAXI BFM wrappers
#          on both ports plus a cycle-accurate age model checked every cycle.
#
# Documentation: docs/markdown/rtl-amba/gaxi/gaxi_age_fifo_sync.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-25
"""Testbench for gaxi_age_fifo_sync.

Three orthogonal choices, deliberately ([[rds-dv-axes]]):
- BFM: GaxiAgeMaster drives wr_*, GaxiAgeSlave drains rd_* (the framework
  GAXI BFMs bound to the age-carrying ports, bin/TBClasses/gaxi/gaxi_age_bfm.py).
- Sequence: random data and either random ages or the N-bank pool rule,
  driven live by GaxiAgePoolDriver.
- Timing: FlexConfigGen profiles on both handshakes; age_dec as a Bernoulli
  strobe and/or the FIFO's own retire strobe.

The checker is a reference model advanced at every falling edge from the
inputs the DUT will latch at the next rising edge, with every output compared
against the model first. Ages, youngest, rd_age_thresh, count and wr_ready are
therefore checked on every cycle, not only at handshakes. Verdicts carry counts
([[checker-verdict-needs-a-count]]).

The runner (val/amba/test_gaxi_age_fifo_sync.py) holds only the grid and
run(); run_suite(level) here is the whole test ([[tb-structure]]).
"""
import os
import random
from collections import deque
from dataclasses import dataclass, field

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from TBClasses.gaxi.gaxi_age_bfm import (
    GaxiAgeMaster, GaxiAgeSlave, GaxiAgePoolDriver, CHECK_SAMPLE_NS)
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen


@dataclass
class AgeFifoStats:
    """What the checker saw. All counts; the verdict is read from these."""
    cycles_checked: int = 0
    writes: int = 0
    reads: int = 0
    decrements: int = 0
    saturations: int = 0        # cycles with a valid head at age 0
    full_cycles: int = 0        # cycles with wr_ready low
    same_cycle_rw: int = 0      # write and read in one cycle
    decr_with_write: int = 0    # decrement in a write cycle
    pool_rank_checks: int = 0   # entries checked for age == rank + 1 (pool mode)
    mismatches: int = 0
    first_mismatches: list = field(default_factory=list)


# Per-level depth: profiles swept, entries per phase, hold-phase strobes.
LEVELS = {
    'gate': dict(profiles=['backtoback', 'fast', 'constrained'],
                 entries_per_depth=4, extra_strobes=2),
    'func': dict(profiles=['backtoback', 'fast', 'constrained', 'bursty',
                           'moderate', 'heavy_pause', 'gaxi_realistic'],
                 entries_per_depth=8, extra_strobes=4),
    'full': dict(profiles=None,               # every profile
                 entries_per_depth=12, extra_strobes=4, double_strobes=True),
}


class GaxiAgeFifoTB(TBBase):
    """Testbench for gaxi_age_fifo_sync."""

    def __init__(self, dut, clk, rstn):
        super().__init__(dut)
        self.clk = clk
        self.clk_name = clk._name
        self.rstn = rstn

        self.DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '4'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '8'))
        self.AGEW = self.convert_to_int(os.environ.get('TEST_AGE_WIDTH', '4'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.MAX_DATA = (1 << self.DW) - 1
        self.MAX_AGE = (1 << self.AGEW) - 1
        self.TIMEOUT_CYCLES = 2000
        self.log.info(f"GaxiAgeFifoTB: DEPTH={self.DEPTH} DW={self.DW} "
                      f"AGEW={self.AGEW} SEED={self.SEED}")

        self.write_master = GaxiAgeMaster(dut, self.clk, self.DW, self.AGEW, self.log,
                                          timeout_cycles=self.TIMEOUT_CYCLES)
        self.read_slave = GaxiAgeSlave(dut, self.clk, self.DW, self.AGEW, self.log,
                                       timeout_cycles=self.TIMEOUT_CYCLES)
        self.pool = GaxiAgePoolDriver(dut, self.clk, self.AGEW, self.log)
        self.randomizers = self._build_randomizers()

        self.model = deque()            # entries: [data, age]
        self.stats = AgeFifoStats()
        self.errors = []
        self._checker_task = None

    # ------------------------------------------------------------------
    # Randomization
    # ------------------------------------------------------------------
    def _build_randomizers(self):
        custom = {
            'gaxi_backpressure': ([(0, 0), (30, 50)], [8, 1]),
            'gaxi_realistic': ([(0, 1), (2, 4), (8, 12), (20, 25)], [4, 3, 2, 1]),
            'depth_aware': ([(0, 0), (1, 1), (self.DEPTH, self.DEPTH * 2)], [6, 2, 1]),
            'parked': ([(400, 400)], [1]),   # reader held off for a hold phase
        }
        gen = FlexConfigGen(
            profiles=['backtoback', 'fast', 'constrained', 'bursty', 'slow',
                      'stress', 'moderate', 'balanced', 'heavy_pause',
                      'chaotic', 'gaxi_backpressure', 'gaxi_realistic',
                      'depth_aware', 'parked'],
            fields=['valid_delay', 'ready_delay'],
            custom_profiles=custom)
        gen.backtoback.valid_delay.fixed_value(0)
        gen.backtoback.ready_delay.fixed_value(0)
        gen.heavy_pause.valid_delay.mostly_zero(zero_weight=10, fallback_range=(1, 3), fallback_weight=1)
        gen.heavy_pause.ready_delay.weighted_ranges([((0, 0), 2), ((30, 50), 1)])
        gen.parked.valid_delay.fixed_value(0)
        gen.parked.ready_delay.fixed_value(400)
        return gen.build(return_flexrandomizer=True)

    def traffic_profiles(self):
        return [p for p in self.randomizers if p != 'parked']

    def set_profile(self, write_profile, read_profile=None):
        read_profile = read_profile or write_profile
        self.write_master.set_randomizer(self.randomizers[write_profile])
        self.read_slave.set_randomizer(self.randomizers[read_profile])

    # ------------------------------------------------------------------
    # The three mandatory methods
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rstn.value = 0
        self.dut.age_dec.value = 0
        await self.write_master.reset_bus()
        await self.read_slave.reset_bus()

    async def deassert_reset(self):
        self.rstn.value = 1
        self.log.info(f"Reset complete{self.get_time_ns_str()}")

    # ------------------------------------------------------------------
    # Cycle checker
    # ------------------------------------------------------------------
    def start_background(self):
        self.pool.start()
        if self._checker_task is None:
            self._checker_task = cocotb.start_soon(self._checker())

    def _expected(self):
        n = len(self.model)
        head = self.model[0] if n else None
        return {
            'wr_ready': 1 if n < self.DEPTH else 0,
            'rd_valid': 1 if n else 0,
            'rd_data': head[0] if head else None,
            'rd_data_age': head[1] if head else None,
            'youngest': max((e[1] for e in self.model), default=0),
            'rd_age_thresh': 1 if (head and head[1] == 0) else 0,
        }

    def _record_mismatch(self, name, exp, got):
        self.stats.mismatches += 1
        msg = (f"{self.get_time_ns_str()} {name}: expected {exp} got {got} "
               f"model={list(self.model)}")
        if len(self.stats.first_mismatches) < 10:
            self.stats.first_mismatches.append(msg)
        self.errors.append(msg)
        self.log.error(msg)

    async def _checker(self):
        dut = self.dut
        while True:
            # After the slave (falling edge) and the pool driver (+2 ns):
            # this is what the next rising edge latches.
            await FallingEdge(self.clk)
            await Timer(CHECK_SAMPLE_NS, 'ns')
            if int(self.rstn.value) == 0:
                self.model.clear()
                continue

            # 1. Inputs the DUT latches at the next edge.
            wr = int(dut.wr_valid.value) and int(dut.wr_ready.value)
            rd = int(dut.rd_valid.value) and int(dut.rd_ready.value)
            dec = int(dut.age_dec.value)

            # 2. Outputs reflect every edge so far: compare to the model.
            #    Exception, inherited from gaxi_fifo_sync mux mode: `count`
            #    comes off the NEXT pointers, so it already includes the
            #    handshakes in flight this cycle.
            exp = self._expected()
            exp['count'] = len(self.model) + (1 if wr else 0) - (1 if rd else 0)
            got = {
                'count': int(dut.count.value),
                'wr_ready': int(dut.wr_ready.value),
                'rd_valid': int(dut.rd_valid.value),
                'youngest': int(dut.youngest.value),
                'rd_age_thresh': int(dut.rd_age_thresh.value),
            }
            if exp['rd_valid']:
                got['rd_data'] = int(dut.rd_data.value)
                got['rd_data_age'] = int(dut.rd_data_age.value)
            for key, g in got.items():
                if exp[key] != g:
                    self._record_mismatch(key, exp[key], g)
            self.stats.cycles_checked += 1
            if exp['rd_age_thresh']:
                self.stats.saturations += 1
            if not exp['wr_ready']:
                self.stats.full_cycles += 1

            # Pool invariant. Under the one-queue wrapper (age = youngest + 1
            # at the latching edge, youngest with age_dec, decrement on every
            # retire) an entry's age must equal its rank + 1: rank 0 is the
            # head. Anything else is drift, and drift wraps. Exact only when
            # every rank fits in the age width.
            if self.pool.live_age and self.DEPTH + 1 <= self.MAX_AGE:
                for rank, e in enumerate(self.model):
                    self.stats.pool_rank_checks += 1
                    if e[1] != rank + 1:
                        self._record_mismatch(f"pool rank {rank}", rank + 1, e[1])

            # 3. Advance the model in the RTL's order: the decrement steps
            #    the entries that were valid before the edge, the head
            #    retires, the new entry is admitted with its age as given.
            if dec:
                self.stats.decrements += 1
                for e in self.model:
                    if e[1] > 0:
                        e[1] -= 1
            if rd:
                self.stats.reads += 1
                self.model.popleft()
            if wr:
                self.stats.writes += 1
                self.model.append([int(dut.wr_data.value), int(dut.wr_data_age.value)])
                if dec:
                    self.stats.decr_with_write += 1
            if wr and rd:
                self.stats.same_cycle_rw += 1

    # ------------------------------------------------------------------
    # Stimulus phases
    # ------------------------------------------------------------------
    def _age_for(self, age_mode):
        if age_mode == 'pool':
            return 0            # placeholder; the pool driver supplies it live
        if age_mode == 'zero':
            return 0
        if age_mode == 'max':
            return self.MAX_AGE
        return random.randint(0, self.MAX_AGE)

    async def run_phase(self, name, count, profile, decr_prob=0.0,
                        decr_on_read=False, age_mode='random',
                        read_profile=None):
        """Send `count` entries under one timing profile and drain them."""
        self.log.info(f"--- phase {name}: {count} entries, profile={profile}"
                      f"/{read_profile or profile}, decr_prob={decr_prob}, "
                      f"decr_on_read={decr_on_read}, age={age_mode}")
        self.set_profile(profile, read_profile)
        self.pool.configure(decr_prob=decr_prob, decr_on_read=decr_on_read,
                            live_age=(age_mode == 'pool'))
        self.read_slave.clear_queue()

        pairs = [(random.randint(0, self.MAX_DATA), self._age_for(age_mode))
                 for _ in range(count)]
        # A burst keeps valid up across beats, so writes can coincide with
        # reads (send() restarts the pipeline per beat and never can).
        await self.write_master.send_burst_aged(pairs)
        await self._drain(len(pairs))
        self.pool.idle()

        got = [d for d, _ in self.read_slave.observed_aged()]
        sent = [d for d, _ in pairs]
        if got != sent:
            self._record_mismatch(f"{name} data order", sent[:8], got[:8])
        self.log.info(f"--- phase {name} done: {len(got)} read back, "
                      f"mismatches so far {self.stats.mismatches}")

    async def _drain(self, expected):
        for _ in range(self.TIMEOUT_CYCLES * 4):
            if len(self.read_slave.get_observed_packets()) >= expected and not self.model:
                return
            await RisingEdge(self.clk)
        self._record_mismatch("drain timeout", expected,
                              len(self.read_slave.get_observed_packets()))

    async def hold_and_decrement(self, name, fill, strobes, age_mode='random'):
        """Fill `fill` entries with the reader parked, strobe age_dec
        `strobes` times, and let the checker watch every age walk to zero.
        """
        self.log.info(f"--- hold phase {name}: fill {fill}, {strobes} strobes")
        self.read_slave.clear_queue()
        self.pool.idle()
        # Park the reader: its next ready comes 400 cycles out, long after
        # the fill and the strobes. The drain below rides that delay out.
        self.set_profile('backtoback', 'parked')
        pairs = [(random.randint(0, self.MAX_DATA), self._age_for(age_mode))
                 for _ in range(fill)]
        await self.write_master.send_burst_aged(pairs)
        self.pool.configure(decr_prob=1.0)
        await self.wait_clocks(self.clk_name, strobes)
        self.pool.idle()
        await self.wait_clocks(self.clk_name, 3)
        self.set_profile('backtoback')
        await self._drain(len(pairs))
        got = [d for d, _ in self.read_slave.observed_aged()]
        sent = [d for d, _ in pairs]
        if got != sent:
            self._record_mismatch(f"{name} data order", sent[:8], got[:8])
        self.log.info(f"--- hold phase {name} done, mismatches so far {self.stats.mismatches}")

    # ------------------------------------------------------------------
    # The suite, by level
    # ------------------------------------------------------------------
    async def run_suite(self, level: str) -> bool:
        cfg = LEVELS[level]
        depth = self.DEPTH
        profiles = cfg['profiles'] or self.traffic_profiles()
        per_phase = cfg['entries_per_depth'] * depth
        hold_strobes = (2 if cfg.get('double_strobes') else 1) * self.MAX_AGE + cfg['extra_strobes']
        self.log.info(f"run_suite level={level}: {len(profiles)} profiles, "
                      f"{per_phase} entries/phase, {hold_strobes} hold strobes")
        self.start_background()
        await self.wait_clocks(self.clk_name, 2)

        # 1. Random ages, random decrement strobes, every timing profile.
        for prof in profiles:
            await self.run_phase(f"random-{prof}", per_phase, prof,
                                 decr_prob=random.choice([0.0, 0.2, 0.5, 1.0]))

        # 2. The N-bank discipline, live: age = youngest + 1 (youngest with
        #    age_dec), decrement on every read; rank invariant checked.
        for prof in profiles[:3]:
            await self.run_phase(f"pool-{prof}", per_phase, prof,
                                 decr_on_read=True, age_mode='pool')

        # 3. Fill with the reader parked, strobe past the largest age: every
        #    entry must saturate at zero and the head must flag it.
        await self.hold_and_decrement("saturate-random", depth, hold_strobes)
        await self.hold_and_decrement("saturate-max", depth, hold_strobes, age_mode='max')
        await self.hold_and_decrement("saturate-zero", depth, 3, age_mode='zero')

        # 4. Writer and reader at opposite paces, so same-cycle write+read
        #    and full both occur with decrements running.
        await self.run_phase("fast-in-slow-out", per_phase, 'backtoback',
                             decr_prob=0.5, read_profile='heavy_pause')
        await self.run_phase("slow-in-fast-out", per_phase, 'heavy_pause',
                             decr_prob=0.5, read_profile='backtoback')

        return self.verdict()

    def verdict(self) -> bool:
        """Zero mismatches AND every event class seen. Counts, not booleans."""
        s = self.stats
        self.log.info(
            f"checker: {s.cycles_checked} cycles, {s.writes} writes, {s.reads} reads, "
            f"{s.decrements} decrements, {s.saturations} saturated-head cycles, "
            f"{s.full_cycles} full cycles, {s.same_cycle_rw} same-cycle r/w, "
            f"{s.decr_with_write} decrement-in-write cycles, "
            f"{s.pool_rank_checks} pool-rank checks, {s.mismatches} mismatches")
        required = {
            'cycles_checked > 100': s.cycles_checked > 100,
            'writes > 0': s.writes > 0,
            'reads == writes': s.reads == s.writes,
            'decrements > 0': s.decrements > 0,
            'saturations > 0': s.saturations > 0,
            'full_cycles > 0': s.full_cycles > 0,
            'same_cycle_rw > 0': s.same_cycle_rw > 0,
            'decr_with_write > 0': s.decr_with_write > 0,
        }
        if self.DEPTH + 1 <= self.MAX_AGE:
            required['pool_rank_checks > 0'] = s.pool_rank_checks > 0
        for name, ok in required.items():
            if not ok:
                self.errors.append(f"coverage: {name} not met")
                self.log.error(f"coverage: {name} not met")
        return s.mismatches == 0 and all(required.values())
