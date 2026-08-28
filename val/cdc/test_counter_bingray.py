# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterBinGrayTB
# Purpose: Binary-Gray Counter Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary-Gray Counter Test with Parameterized Test Levels and Configuration

This test uses WIDTH as parameter for maximum flexibility:

TEST LEVELS (per-test depth):
    gate (30s-2min):  Quick verification during development
    func (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 2 tests (~5 min) - smoke test (small + large counter)
    FUNC: 4 tests (~15 min) - functional coverage - DEFAULT
    FULL: 12 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 2 widths × 1 level = 2 tests
    FUNC: 4 widths × 1 level = 4 tests (gate level only)
    FULL: 4 widths × 3 levels = 12 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: gate|func|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility

COUNTER_BINGRAY BEHAVIOR:
    Binary counter with Gray code output:
    - counter_bin increments normally: 0→1→2→...→(2^WIDTH-1)→0
    - counter_gray is Gray code version: binary XOR (binary >> 1)
    - Both outputs wrap around at 2^WIDTH
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
from TBClasses.cdc.counter_bingray_tb import CounterBinGrayTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path


@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_bingray_test(dut):
    """Test for Binary-Gray Counter module"""
    tb = CounterBinGrayTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER_BINGRAY test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter bingray test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed

def generate_params():
    """
    Generate counter_bingray parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke test - small + large)
    REG_LEVEL=FUNC: 4 tests (functional coverage) - default
    REG_LEVEL=FULL: 12 tests (comprehensive validation)

    Parameters: (width, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove basic functionality
        # 2 tests: small + large counter, gate level only
        params = [
            (4, 'gate'),    # Small counter (4 bits)
            (8, 'gate'),    # Larger counter (8 bits)
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - test variety of widths with gate level
        # 4 widths × 1 level = 4 tests
        widths = [4, 5, 8, 12]
        test_levels = ['gate']  # Keep tests fast for functional check

        params = []
        for width in widths:
            for level in test_levels:
                params.append((width, level))

    else:  # FULL
        # Comprehensive testing - multiple widths and all test levels
        # 4 widths × 3 levels = 12 tests
        widths = [4, 5, 8, 12]
        test_levels = ['gate', 'func', 'full']

        params = []
        for width, level in product(widths, test_levels):
            params.append((width, level))

    return params

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_counter_bingray(request, width, test_level):
    """
    Parameterized Binary-Gray Counter test with configurable width and test level.

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    
    Counter behavior: Binary counter with Gray code output
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_bingray"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/cdc/filelists/counter_bingray.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_counter_bingray_w{width}_{test_level}_{reg_level}"
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
    width_factor = max(1.0, (1 << width) / 256.0)  # Larger widths take more time
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
    print(f"Max value: {(1 << width) - 1}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
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
