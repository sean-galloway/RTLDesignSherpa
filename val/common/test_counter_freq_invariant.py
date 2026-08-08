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
from TBClasses.common.counter_freq_invariant_tb import CounterFreqInvariantTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args

# ==========================================================================
# Python-side LUT computation (must match RTL functions exactly)
# ==========================================================================




# ==========================================================================
# Testbench class
# ==========================================================================


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
# FREQ_STRATEGY is a GRID DIMENSION, not a constant. It was pinned at 0
# (LINEAR) here, so pow2_freq() and the case arm that selects it were never
# elaborated -- 9 uncovered statements and the module stuck at 71.1% line
# coverage, identical at gate and full because no amount of depth reaches an
# unbuilt configuration.
STRATEGY_LINEAR = 0
STRATEGY_POW2 = 1

def generate_test_parameters():
    """
    Build (counter_width, min_mhz, max_mhz) tuples.

    REG_LEVEL=GATE: 1 width  x 3 ranges x 1 strategy =  3 tests
    REG_LEVEL=FUNC: 2 widths x 3 ranges x 2 strategies = 12 tests (default)
    REG_LEVEL=FULL: 3 widths x 3 ranges x 2 strategies = 18 tests

    GATE stays LINEAR-only to keep the smoke level fast; POW2 comes in from
    FUNC up, which is where coverage is measured.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_widths = [8, 16, 24]
    if reg_level == 'GATE':
        widths = [all_widths[0]]
        strategies = [STRATEGY_LINEAR]
    elif reg_level == 'FUNC':
        widths = all_widths[:2]
        strategies = [STRATEGY_LINEAR, STRATEGY_POW2]
    else:
        widths = all_widths
        strategies = [STRATEGY_LINEAR, STRATEGY_POW2]

    params = []
    for cw in widths:
        for lo, hi in FREQ_RANGES:
            for st in strategies:
                params.append((cw, lo, hi, st, NUM_ENTRIES))

    if reg_level == 'FULL':
        # A single-entry LUT, once per strategy. SEL_WIDTH is explicitly
        # written as (NUM_FREQ_ENTRIES > 1) ? $clog2(N) : 1, so this is a
        # SUPPORTED degenerate configuration, and it is the only thing that
        # reaches linear_freq's `if (n <= 1) return lo` guard. Two tests
        # rather than a whole extra dimension -- the guard does not need
        # sweeping, only reaching.
        lo, hi = FREQ_RANGES[0]
        for st in (STRATEGY_LINEAR, STRATEGY_POW2):
            params.append((widths[0], lo, hi, st, 1))

    return params

test_params = generate_test_parameters()

# ==========================================================================
# Pytest wrapper
# ==========================================================================

@pytest.mark.parametrize("counter_width, min_mhz, max_mhz, strategy, num_entries", test_params)
def test_counter_freq_invariant(request, counter_width, min_mhz, max_mhz, strategy, num_entries):
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
    # The strategy MUST be in the name: without it the LINEAR and POW2 builds
    # of the same width/range share one sim_build directory and one log, so the
    # second silently reuses the first's compiled DUT.
    test_name_plus_params = (
        f"test_{dut_name}_cw{cw_str}_"
        f"{min_mhz}to{max_mhz}mhz_"
        f"{'pow2' if strategy == STRATEGY_POW2 else 'linear'}_n{num_entries}_{reg_level}"
    )
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        "COUNTER_WIDTH":    str(counter_width),
        "MIN_FREQ_MHZ":     str(min_mhz),
        "MAX_FREQ_MHZ":     str(max_mhz),
        "NUM_FREQ_ENTRIES": str(num_entries),
        "FREQ_STRATEGY":    str(strategy),
        "DEBUG_LUT":        "1",
    }

    test_level_map = {'GATE': 'gate', 'FUNC': 'func', 'FULL': 'full'}
    test_level = test_level_map.get(reg_level, 'gate')

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'TEST_COUNTER_WIDTH': str(counter_width),
        'TEST_MIN_FREQ_MHZ': str(min_mhz),
        'TEST_MAX_FREQ_MHZ': str(max_mhz),
        'TEST_NUM_FREQ_ENTRIES': str(num_entries),
        'TEST_FREQ_STRATEGY': str(strategy),
        'TEST_LEVEL': test_level,
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
        '-Wno-WIDTHTRUNC',
    ]


    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this

    # the run produces no coverage.dat at all and `make coverage-report`

    # silently reports 0.0% from 0 merged files.

    extra_args.extend(get_coverage_compile_args())

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    sim_args = ['--trace'] if enable_waves else []

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
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        raise
