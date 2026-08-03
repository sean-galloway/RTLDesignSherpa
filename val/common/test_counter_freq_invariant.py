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
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
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
        'TRACE_FILE': f"{sim_build}/dump.fst",
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
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
        '-Wno-WIDTHTRUNC',
    ]

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
