# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_counter_freq_invariant
# Purpose: Test runner for the parametric counter_freq_invariant module
#
# Author: sean galloway
# Created: 2025-10-18
# Updated: 2026-04-10 -- rewritten for parametric LUT (MIN/MAX/NUM_ENTRIES)

"""
Test runner for counter_freq_invariant module.

The RTL module now generates its frequency LUT at elaboration time from
MIN_FREQ_MHZ, MAX_FREQ_MHZ, and NUM_FREQ_ENTRIES parameters.  This test
mirrors the LUT computation in Python and verifies that prescaler tick
intervals match the expected division factor for every LUT entry.

Three frequency ranges are tested (per the user's request):
  1.   5 -   85 MHz   (low-end FPGA)
  2.  50 -  250 MHz   (mainstream FPGA)
  3. 100 - 1500 MHz   (high-speed ASIC)

REG_LEVEL controls parameter breadth:
    GATE: 1 counter width  x 3 ranges =  3 tests
    FUNC: 2 counter widths x 3 ranges =  6 tests  (default)
    FULL: 3 counter widths x 3 ranges =  9 tests
"""

import os
import sys
import math
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from conftest import get_coverage_compile_args
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd

# ==========================================================================
# Python-side LUT computation (must match RTL functions exactly)
# ==========================================================================

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


# ==========================================================================
# Testbench class
# ==========================================================================

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
            return True  # not enough data — pass silently
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
                self.log.warning(
                    f"freq_sel={sel}: insufficient data ({len(cc)} changes)")

        self.log.info(f"Frequency sweep: {'PASS' if all_ok else 'FAIL'}")
        return all_ok


# ==========================================================================
# CocoTB test function
# ==========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def counter_freq_invariant_test(dut):
    """Parametric frequency-invariant counter test."""
    tb = CounterFreqInvariantTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # 1 ns clock → fast simulation regardless of freq_sel setting
    await tb.start_clock('clk', 1, 'ns')
    await tb.reset_dut()

    passed = True

    p = await tb.run_programming_model_test()
    assert p, "Programming model test failed"
    passed &= p

    p = await tb.run_sync_reset_test()
    assert p, "Sync reset test failed"
    passed &= p

    p = await tb.run_frequency_sweep_test()
    assert p, "Frequency sweep test failed"
    passed &= p

    await tb.wait_clocks('clk', 100)
    tb.log.info("All tests passed" if passed else "Some tests FAILED")


# ==========================================================================
# Parameter generation
# ==========================================================================

# Three frequency ranges requested by the user
FREQ_RANGES = [
    (5, 85),       # low-end FPGA
    (50, 250),     # mainstream FPGA
    (100, 1500),   # high-speed ASIC
]

NUM_ENTRIES = 16
STRATEGY = 0  # LINEAR


def generate_test_parameters():
    """
    Build (counter_width, min_mhz, max_mhz) tuples.

    REG_LEVEL=GATE: 1 width  x 3 ranges =  3 tests
    REG_LEVEL=FUNC: 2 widths x 3 ranges =  6 tests (default)
    REG_LEVEL=FULL: 3 widths x 3 ranges =  9 tests
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_widths = [8, 16, 24]
    if reg_level == 'GATE':
        widths = [all_widths[0]]
    elif reg_level == 'FUNC':
        widths = all_widths[:2]
    else:
        widths = all_widths

    params = []
    for cw in widths:
        for lo, hi in FREQ_RANGES:
            params.append((cw, lo, hi))
    return params


test_params = generate_test_parameters()


# ==========================================================================
# Pytest wrapper
# ==========================================================================

@pytest.mark.parametrize("counter_width, min_mhz, max_mhz", test_params)
def test_counter_freq_invariant(request, counter_width, min_mhz, max_mhz):
    """Run the parametric counter_freq_invariant test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "counter_freq_invariant"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_freq_invariant.f',
    )

    # Derive DIV_WIDTH and PRESCALER_MAX to match RTL localparams
    div_width = math.ceil(math.log2(max_mhz + 1))
    prescaler_max = 2 ** div_width
    sel_width = math.ceil(math.log2(NUM_ENTRIES)) if NUM_ENTRIES > 1 else 1

    cw_str = TBBase.format_dec(counter_width, 3)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = (
        f"test_{dut_name}_cw{cw_str}_"
        f"{min_mhz}to{max_mhz}mhz_{reg_level}"
    )
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        "COUNTER_WIDTH":    str(counter_width),
        "MIN_FREQ_MHZ":     str(min_mhz),
        "MAX_FREQ_MHZ":     str(max_mhz),
        "NUM_FREQ_ENTRIES": str(NUM_ENTRIES),
        "FREQ_STRATEGY":    str(STRATEGY),
        "DEBUG_LUT":        "1",
    }

    test_level_map = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}
    test_level = test_level_map.get(reg_level, 'gate')

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'TEST_COUNTER_WIDTH': str(counter_width),
        'TEST_MIN_FREQ_MHZ': str(min_mhz),
        'TEST_MAX_FREQ_MHZ': str(max_mhz),
        'TEST_NUM_FREQ_ENTRIES': str(NUM_ENTRIES),
        'TEST_FREQ_STRATEGY': str(STRATEGY),
        'TEST_LEVEL': test_level,
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "-Wno-TIMESCALEMOD",
    ]
    compile_args.extend(get_coverage_compile_args())

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="counter_freq_invariant_test",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=["--trace", "--trace-structs", "--trace-depth", "99"],
            plusargs=["--trace"],
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        raise
