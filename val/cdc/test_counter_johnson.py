# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterJohnsonTB
# Purpose: Johnson Counter Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Johnson Counter Test with Parameterized Test Levels and Configuration

This test uses WIDTH as parameter for maximum flexibility:

CONFIGURATION:
    WIDTH: Counter width in bits (4, 5, 8, 12)

TEST LEVELS (per-test depth):
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (4-bit, gate)
    FUNC: 4 tests (~8 min) - functional coverage - DEFAULT
    FULL: 12 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width × 1 level = 1 test
    FUNC: 4 widths × 1 level = 4 tests (all widths, gate only)
    FULL: 4 widths × 3 levels = 12 tests

Environment Variables:
    REG_LEVEL: Control parameter combinations (GATE/FUNC/FULL)
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Counter width in bits

COUNTER_JOHNSON BEHAVIOR:
    Johnson counter (twisted ring counter):
    - Shifts left and feeds inverted MSB to LSB
    - Sequence length: 2 * WIDTH
    - For WIDTH=4: 0000 → 0001 → 0011 → 0111 → 1111 → 1110 → 1100 → 1000 → 0000
    - Creates a "walking ones" then "walking zeros" pattern
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
from TBClasses.cdc.counter_johnson_tb import CounterJohnsonTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path


@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_johnson_test(dut):
    """Test for Johnson Counter module"""
    tb = CounterJohnsonTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"JOHNSON COUNTER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Johnson counter test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (4-bit, gate level)
    REG_LEVEL=FUNC: 4 tests (all widths, gate level) - default
    REG_LEVEL=FULL: 12 tests (all widths, all test levels)

    Returns:
        List of tuples: (width, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [4, 5, 8, 12]  # Different counter widths
    test_levels = ['gate', 'func', 'full']  # Test levels

    if reg_level == 'GATE':
        # Quick smoke test: 4-bit, gate only
        params = [(4, 'gate')]

    elif reg_level == 'FUNC':
        # Functional coverage: all widths, gate level only
        params = [(width, 'gate') for width in widths]

    else:  # FULL
        # Comprehensive: all combinations
        params = []
        for width, test_level in product(widths, test_levels):
            params.append((width, test_level))

    return params

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_counter_johnson(request, width, test_level):
    """
    Parameterized Johnson Counter test with configurable width and test level.

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)

    Counter behavior: Johnson counter (twisted ring) with sequence length 2*WIDTH
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_johnson"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/cdc/filelists/counter_johnson.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_counter_johnson_w{width}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width)
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'gate': 1, 'func': 3, 'full': 6}
    width_factor = max(1.0, width / 8.0)  # Larger widths take more time
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

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
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}")
    print(f"Sequence length: {2 * width}")
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
