# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterFreqInvariantTB
# Purpose: Testbench for counter_freq_invariant
# Subsystem: framework
#
# Extracted from val/common/test_counter_freq_invariant.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.triggers import RisingEdge
from TBClasses.shared.tbbase import TBBase


def linear_freq(idx: int, n: int, lo: int, hi: int) -> int:
    """Matches RTL linear_freq: uniform spacing from lo to hi."""
    if n <= 1:
        return lo
    return lo + ((hi - lo) * idx) // (n - 1)

def pow2_freq(idx: int, n: int, lo: int, hi: int) -> int:
    """Matches RTL pow2_freq: doubling per step, capped at hi."""
    v = lo
    for _ in range(idx):
        if v >= hi:
            return hi
        v *= 2
    return min(v, hi)

def build_factor_map(
    min_mhz: int, max_mhz: int, num_entries: int, strategy: int = 0
) -> dict:
    """Build {freq_sel_index: division_factor} matching the RTL LUT."""
    table = {}
    for i in range(num_entries):
        if strategy == 1:
            table[i] = pow2_freq(i, num_entries, min_mhz, max_mhz)
        else:
            table[i] = linear_freq(i, num_entries, min_mhz, max_mhz)
    return table

class CounterFreqInvariantTB(TBBase):
    """
    Testbench for counter_freq_invariant with parametric LUT.

    Reads MIN_FREQ_MHZ, MAX_FREQ_MHZ, NUM_FREQ_ENTRIES from environment
    variables (set by the pytest wrapper) and builds the expected factor
    map at init time.
    """

    def __init__(self, dut):
        super().__init__(dut)

        self.COUNTER_WIDTH = self.convert_to_int(
            os.environ.get('TEST_COUNTER_WIDTH', '16'))
        self.SEED = self.convert_to_int(
            os.environ.get('SEED', '12345'))
        self.MIN_FREQ_MHZ = self.convert_to_int(
            os.environ.get('TEST_MIN_FREQ_MHZ', '5'))
        self.MAX_FREQ_MHZ = self.convert_to_int(
            os.environ.get('TEST_MAX_FREQ_MHZ', '220'))
        self.NUM_FREQ_ENTRIES = self.convert_to_int(
            os.environ.get('TEST_NUM_FREQ_ENTRIES', '16'))
        self.FREQ_STRATEGY = self.convert_to_int(
            os.environ.get('TEST_FREQ_STRATEGY', '0'))

        random.seed(self.SEED)

        # Build the expected factor map (must match RTL)
        self.factor_map = build_factor_map(
            self.MIN_FREQ_MHZ, self.MAX_FREQ_MHZ,
            self.NUM_FREQ_ENTRIES, self.FREQ_STRATEGY)

        # Clock and reset
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n
        self.sync_reset_n = self.dut.sync_reset_n

        self.counter_max = (2 ** self.COUNTER_WIDTH) - 1
        self.counter_changes = []
        self.tick_events = []
        self.current_freq_sel = 0
        self.current_division_factor = self.factor_map[0]
        self.done = False

        self.log.info(
            f"TB init: COUNTER_WIDTH={self.COUNTER_WIDTH} "
            f"range={self.MIN_FREQ_MHZ}-{self.MAX_FREQ_MHZ} MHz "
            f"entries={self.NUM_FREQ_ENTRIES} strategy={self.FREQ_STRATEGY}")
        self.log.info(f"LUT: {self.factor_map}")

    # ------------------------------------------------------------------
    # Reset helpers
    # ------------------------------------------------------------------

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

    async def reset_dut(self):
        """Full asynchronous reset; leaves sync_reset_n=0."""
        self.reset_n.value = 0
        self.sync_reset_n.value = 0
        self.dut.freq_sel.value = 0
        await self.wait_clocks('clk', 10)
        self.reset_n.value = 1
        await self.wait_clocks('clk', 5)
        self.counter_changes.clear()
        self.tick_events.clear()

    async def sync_reset_dut(self):
        """Apply and release synchronous reset (async reset stays inactive)."""
        self.reset_n.value = 1
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 5)
        self.sync_reset_n.value = 1
        await self.wait_clocks('clk', 10)
        self.counter_changes.clear()
        self.tick_events.clear()

    # ------------------------------------------------------------------
    # Frequency control
    # ------------------------------------------------------------------

    def set_frequency_selection(self, freq_sel: int):
        """Programme freq_sel and hold sync_reset_n=0 (programming model)."""
        max_sel = self.NUM_FREQ_ENTRIES - 1
        if freq_sel < 0 or freq_sel > max_sel:
            self.log.error(
                f"freq_sel {freq_sel} out of range 0..{max_sel}; clamping")
            freq_sel = min(max(freq_sel, 0), max_sel)

        self.sync_reset_n.value = 0
        self.dut.freq_sel.value = freq_sel
        self.current_freq_sel = freq_sel
        self.current_division_factor = self.factor_map[freq_sel]
        self.log.info(
            f"Set freq_sel={freq_sel} → "
            f"{self.current_division_factor} MHz ({self.current_division_factor} cycles/us)")

    async def activate_frequency(self):
        """Release sync_reset_n to start the counter."""
        self.sync_reset_n.value = 1
        await self.wait_clocks('clk', 10)

    # ------------------------------------------------------------------
    # Monitoring
    # ------------------------------------------------------------------

    async def monitor_counter(self, num_cycles: int):
        """Record counter changes and tick pulses for *num_cycles* clocks."""
        self.counter_changes.clear()
        self.tick_events.clear()

        prev = int(self.dut.o_counter.value)
        self.counter_changes.append((0, prev))

        for cyc in range(1, num_cycles + 1):
            await RisingEdge(self.clock)
            cur = int(self.dut.o_counter.value)
            if cur != prev:
                self.counter_changes.append((cyc, cur))
                prev = cur
            if int(self.dut.tick.value) == 1:
                self.tick_events.append(cyc)

            # Enough data? Stop early for fast frequencies
            if len(self.counter_changes) > 20 and self.current_division_factor >= 500:
                break

        return self.counter_changes, self.tick_events

    # ------------------------------------------------------------------
    # Verification helpers
    # ------------------------------------------------------------------

    def verify_counter_changes(self, counter_changes, expected_div):
        """Check that average interval between counter increments is ~expected_div."""
        if len(counter_changes) < 3:
            self.log.warning("Too few counter changes to verify")
            return False

        intervals = [
            counter_changes[i][0] - counter_changes[i - 1][0]
            for i in range(2, len(counter_changes))
        ]
        avg = sum(intervals) / len(intervals)

        # Tolerance: wider for very large division factors
        tol = 0.05 if expected_div <= 200 else (0.08 if expected_div <= 500 else 0.12)
        lo = expected_div * (1 - tol)
        hi = expected_div * (1 + tol)

        self.log.info(
            f"Avg interval={avg:.2f}, expected={expected_div} "
            f"(acceptable {lo:.1f}-{hi:.1f})")
        ok = lo <= avg <= hi
        if not ok:
            self.log.error("Counter interval verification FAILED")
        return ok

    def verify_counter_sequence(self, counter_changes):
        """Check that counter values increment by 1 (or wrap)."""
        if len(counter_changes) < 2:
            return False
        errors = 0
        for i in range(1, len(counter_changes)):
            _, cur = counter_changes[i]
            _, prev = counter_changes[i - 1]
            expected = (prev + 1) & self.counter_max
            if cur != expected and not (prev == self.counter_max and cur == 0):
                errors += 1
                self.log.error(
                    f"Sequence error at idx {i}: {prev} -> {cur}, expected {expected}")
        ok = errors == 0
        if ok:
            self.log.info("Counter sequence OK")
        return ok

    def verify_tick_signal(self, tick_events, expected_div):
        """Check that tick interval matches expected_div."""
        if len(tick_events) < 2:
            # Used to `return True  # not enough data - pass silently`, which
            # is the exact shape of an unfailable check: a prescaler that never
            # ticks produces zero events and was reported as verified. The
            # monitor window is div*10 cycles (capped at 15000) and div maxes
            # out around MAX_FREQ_MHZ, so a healthy entry yields roughly ten
            # ticks. Fewer than two means the tick did not run.
            self.log.error(
                f"Tick verification impossible: {len(tick_events)} tick event(s) "
                f"observed for expected_div={expected_div}; a working prescaler "
                f"should produce about 10 in this window")
            return False
        intervals = [tick_events[i] - tick_events[i - 1]
                      for i in range(1, len(tick_events))]
        avg = sum(intervals) / len(intervals)
        tol = 0.15
        lo = expected_div * (1 - tol)
        hi = expected_div * (1 + tol)
        self.log.info(
            f"Avg tick interval={avg:.2f}, expected={expected_div} "
            f"(acceptable {lo:.1f}-{hi:.1f})")
        ok = lo <= avg <= hi
        if not ok:
            self.log.error("Tick timing verification FAILED")
        return ok

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------

    async def run_programming_model_test(self):
        """Verify: sync_reset_n=0 holds counter at 0, freq change restarts."""
        self.log.info("=== Programming model test ===")
        await self.reset_dut()

        mid = self.NUM_FREQ_ENTRIES // 2
        self.set_frequency_selection(mid)

        # Counter must stay at 0 while sync_reset_n = 0
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 100)
        ctr = int(self.dut.o_counter.value)
        tick = int(self.dut.tick.value)
        holds_zero = ctr == 0 and tick == 0

        # Activate and verify operation
        await self.activate_frequency()
        await self.wait_clocks('clk', self.current_division_factor * 5)
        cc, te = await self.monitor_counter(self.current_division_factor * 8)
        runs_ok = len(cc) > 1 and len(te) > 0

        # Change frequency while running
        new_sel = max(0, mid - 2)
        self.set_frequency_selection(new_sel)
        await self.activate_frequency()
        cc2, te2 = await self.monitor_counter(self.current_division_factor * 8)
        change_ok = len(cc2) > 1

        ok = holds_zero and runs_ok and change_ok
        self.log.info(f"Programming model: {'PASS' if ok else 'FAIL'}")
        return ok

    async def run_sync_reset_test(self):
        """Verify synchronous reset clears counter and tick."""
        self.log.info("=== Sync reset test ===")
        await self.reset_dut()

        mid = self.NUM_FREQ_ENTRIES // 2
        self.set_frequency_selection(mid)
        await self.activate_frequency()
        await self.wait_clocks('clk', self.current_division_factor * 5)

        # Assert sync reset
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 5)
        ctr = int(self.dut.o_counter.value)
        tick = int(self.dut.tick.value)
        held = ctr == 0 and tick == 0

        # Release and check recovery
        self.sync_reset_n.value = 1
        await self.wait_clocks('clk', self.current_division_factor * 3)
        cc, te = await self.monitor_counter(self.current_division_factor * 8)
        recovers = len(cc) > 1
        seq_ok = self.verify_counter_sequence(cc)
        timing_ok = self.verify_counter_changes(cc, self.current_division_factor) \
            if len(cc) >= 3 else True

        ok = held and recovers and seq_ok and timing_ok
        self.log.info(f"Sync reset: {'PASS' if ok else 'FAIL'}")
        return ok

    async def run_frequency_sweep_test(self):
        """Sweep all (or a subset of) LUT entries and verify tick rate."""
        self.log.info("=== Frequency sweep test ===")

        test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        n = self.NUM_FREQ_ENTRIES

        if test_level == 'full':
            indices = list(range(n))
        elif test_level == 'func':
            step = max(1, n // 8)
            indices = list(range(0, n, step))
            if (n - 1) not in indices:
                indices.append(n - 1)
        else:
            # GATE: first, mid, last
            indices = sorted(set([0, n // 2, n - 1]))

        self.log.info(f"Sweep {len(indices)} entries: {indices}")
        all_ok = True

        for sel in indices:
            self.log.info(f"--- freq_sel={sel} ---")
            await self.reset_dut()
            self.set_frequency_selection(sel)
            await self.activate_frequency()

            div = self.current_division_factor
            monitor_cycles = min(div * 10, 15000)

            cc, te = await self.monitor_counter(monitor_cycles)

            if len(cc) >= 3:
                t_ok = self.verify_counter_changes(cc, div)
                s_ok = self.verify_counter_sequence(cc)
                k_ok = self.verify_tick_signal(te, div)
                if not (t_ok and s_ok and k_ok):
                    all_ok = False
                    self.log.error(f"freq_sel={sel} FAILED")
                else:
                    self.log.info(f"freq_sel={sel} PASSED")
            else:
                # Insufficient data is a FAILED entry, not a skipped one. The
                # module docstring promises this sweep "verifies that prescaler
                # tick intervals match the expected division factor for every
                # LUT entry"; leaving all_ok alone here meant a dead entry --
                # counter never increments -- was counted as PASS.
                all_ok = False
                self.log.error(
                    f"freq_sel={sel} FAILED: insufficient data ({len(cc)} counter "
                    f"changes in {monitor_cycles} cycles, div={div}); the counter "
                    f"is not running for this LUT entry")

        self.log.info(f"Frequency sweep: {'PASS' if all_ok else 'FAIL'}")
        return all_ok
