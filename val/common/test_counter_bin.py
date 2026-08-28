# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterBinTB
# Purpose: Binary Counter Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary Counter Test with Parameterized Test Levels and Configuration

This test uses WIDTH and MAX as parameters for maximum flexibility:

TEST LEVELS (per-test depth):
    gate (30s-2min):  Quick verification during development
    func (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 2 tests (~5 min) - smoke test (small + large counter)
    FUNC: 9 tests (~20 min) - functional coverage - DEFAULT
    FULL: 27 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 2 configs (small + large) × 1 level = 2 tests
    FUNC: 3 widths × 3 max_vals × 1 level = 9 tests (gate level only)
    FULL: 3 widths × 3 max_vals × 3 levels = 27 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: gate|func|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility

COUNTER_BIN BEHAVIOR:
    Binary counter with special wrap behavior:
    - Counts 0→1→2→...→(MAX-1), then wraps to {~MSB, 0...0}
    - For WIDTH=5, MAX=10: counts 0→1→...→9, then wraps to 16 (10000b)
    - Next cycle: 17, 18, ..., 25, then wraps to 0 (00000b)
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.counter_bin_tb import CounterBinTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_bin_test(dut):
    """Test for Binary Counter module"""
    tb = CounterBinTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER_BIN test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter bin test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed

def generate_params():
    """
    Generate counter_bin parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke test - small + large)
    REG_LEVEL=FUNC: 9 tests (functional coverage) - default
    REG_LEVEL=FULL: 27 tests (comprehensive validation)

    Parameters: (width, max_val, test_level)

    Counter constraint: MAX must fit in WIDTH-1 bits (MSB is special)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove basic functionality
        # 2 tests: small counter + large counter, gate level only
        params = [
            (5, 10, 'gate'),   # Small counter (5 bits, max 10)
            (8, 128, 'gate'),  # Larger counter (8 bits, max 128)
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - test variety of widths/maxs with gate level
        # 3 widths × 3 maxs × 1 level = 9 tests
        widths = [4, 5, 8]
        maxs = [8, 10, 16]
        test_levels = ['gate']  # Keep tests fast for functional check

        params = []
        for width, max_val in product(widths, maxs):
            # Ensure MAX fits in WIDTH-1 bits (since MSB is special)
            if max_val < (1 << (width - 1)):
                for level in test_levels:
                    params.append((width, max_val, level))

    else:  # FULL
        # Comprehensive testing - multiple widths, maxs, and all test levels
        # 3 widths × 3 maxs × 3 levels = 27 tests
        widths = [4, 5, 8]
        maxs = [8, 10, 16]
        test_levels = ['gate', 'func', 'full']

        params = []
        for width, max_val, level in product(widths, maxs, test_levels):
            # Ensure MAX fits in WIDTH-1 bits
            if max_val < (1 << (width - 1)):
                params.append((width, max_val, level))

    return params

params = generate_params()

@pytest.mark.parametrize("width, max_val, test_level", params)
def test_counter_bin(request, width, max_val, test_level):
    """
    Parameterized Binary Counter test with configurable width, max value and test level.

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)

    Counter behavior: Binary counter with special wrap (toggle MSB, clear others)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_bin"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_bin.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_counter_bin_w{width}_max{max_val}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width),
        'MAX': str(max_val)
    }

    # Adjust timeout based on test level and max value
    timeout_multipliers = {'gate': 1, 'func': 3, 'full': 6}
    max_factor = max(1.0, max_val / 100.0)  # Larger max values take more time
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_WIDTH': str(width),
        'TEST_MAX': str(max_val),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this
    # the run produces no coverage.dat at all and `make coverage-report`
    # silently reports 0.0% from 0 merged files.
    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}, max={max_val}")
    print(f"Expected sequence length: {max_val * 2}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ {test_level.upper()} test PASSED: width={width}, max={max_val}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
