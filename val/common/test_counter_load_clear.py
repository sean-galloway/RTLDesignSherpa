# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterLoadClearTB
# Purpose: Counter Load Clear Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Counter Load Clear Test with Parameterized Test Levels and Configuration

This test uses max_value and test_level as parameters for maximum flexibility:

CONFIGURATION:
    max_value:   Maximum count value (32, 255, 1023)

TEST LEVELS (per-test depth):
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (max=32, gate)
    FUNC: 3 tests (~6 min) - functional coverage - DEFAULT
    FULL: 9 tests (~1 hour) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 max_value × 1 level = 1 test
    FUNC: 3 max_values × 1 level = 3 tests (all max_values, gate only)
    FULL: 3 max_values × 3 levels = 9 tests

Environment Variables:
    REG_LEVEL: Control parameter combinations (GATE/FUNC/FULL)
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_MAX_VALUE: Maximum count value for counter
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
from TBClasses.common.counter_load_clear_tb import CounterLoadClearTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def counter_load_clear_test(dut):
    """Test for Counter Load Clear module"""
    tb = CounterLoadClearTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER_LOAD_CLEAR test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter Load Clear test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (max=32, gate level)
    REG_LEVEL=FUNC: 3 tests (all max_values, gate level) - default
    REG_LEVEL=FULL: 9 tests (all max_values, all test levels)

    Returns:
        List of tuples: (max_value, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    max_values = [32, 255, 1023]  # Different maximum count values
    test_levels = ['gate', 'func', 'full']  # Test levels

    if reg_level == 'GATE':
        # Quick smoke test: max=32, gate only
        params = [(32, 'gate')]

    elif reg_level == 'FUNC':
        # Functional coverage: all max_values, gate level only
        params = [(max_val, 'gate') for max_val in max_values]

    else:  # FULL
        # Comprehensive: all combinations
        params = []
        for max_value, test_level in product(max_values, test_levels):
            params.append((max_value, test_level))

    return params

params = generate_params()

@pytest.mark.parametrize("max_value, test_level", params)
def test_counter_load_clear(request, max_value, test_level):
    """
    Parameterized Counter Load Clear test with configurable max value and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_load_clear"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_load_clear.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    max_str = TBBase.format_dec(max_value, 4)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_counter_load_clear_max{max_str}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'MAX': str(max_value)
    }

    # Adjust timeout based on test level and max value
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    max_factor = max(1.0, max_value / 1000.0)
    base_timeout = 3000  # 3 seconds base
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
        'TEST_MAX_VALUE': str(max_value),
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
    print(f"Running {test_level.upper()} test: max_value={max_value}")
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
        print(f"✓ {test_level.upper()} test PASSED: max_value={max_value}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
