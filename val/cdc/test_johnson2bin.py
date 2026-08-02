# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GrayJ2BinTB
# Purpose: Gray Johnson Counter to Binary Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Gray Johnson Counter to Binary Converter Test

This test verifies the Gray Johnson counter to binary conversion functionality:

CONFIGURATION:
    JCW: Johnson Counter Width (10, 12, 16, 20)
    WIDTH: Binary output width (4, 5, 6, 8)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - (JCW=10, WIDTH=4): Johnson counter 10 bits -> 4-bit binary
    - (JCW=12, WIDTH=5): Johnson counter 12 bits -> 5-bit binary
    - (JCW=16, WIDTH=6): Johnson counter 16 bits -> 6-bit binary
    - (JCW=20, WIDTH=8): Johnson counter 20 bits -> 8-bit binary

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_JCW: Johnson Counter Width
    TEST_WIDTH: Binary output width

GRAY JOHNSON BEHAVIOR:
    Johnson counter produces specific Gray code patterns
    Module requires leading_one_trailing_one submodule
    Conversion depends on MSB and position of leading/trailing ones
    Sequential clocked operation with reset
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.cdc.johnson2bin_tb import GrayJ2BinTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=60000, timeout_unit="us")
async def johnson2bin_test(dut):
    """Test for Gray Johnson Counter to Binary Converter module"""
    tb = GrayJ2BinTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"GRAYJ2BIN test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"GrayJ2Bin test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters"""
    # Valid parameter combinations
    param_combinations = [
        (10, 5),  # 10-bit Johnson counter -> 4-bit binary
        (12, 5),  # 12-bit Johnson counter -> 5-bit binary
        (16, 5),  # 16-bit Johnson counter -> 6-bit binary
        (20, 6),  # 20-bit Johnson counter -> 8-bit binary
    ]

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        param_combinations, test_levels = param_combinations[:1], ['gate']
    elif reg_level == 'FULL':
        test_levels = ['gate', 'func', 'full']
    else:
        param_combinations, test_levels = param_combinations[:2], ['func']

    valid_params = []
    for (jcw, width), test_level in product(param_combinations, test_levels):
        valid_params.append((jcw, width, test_level))

    # For debugging, uncomment one of these:
    # return [(10, 5, 'full')]  # Single test
    # return [(10, 4, 'func'), (12, 5, 'func')]  # Specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("jcw, width, test_level", params)
def test_johnson2bin(request, jcw, width, test_level):
    """
    Parameterized Gray Johnson Counter to Binary Converter test

    Note: This test requires the leading_one_trailing_one module to be available
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "johnson2bin"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/cdc/filelists/johnson2bin.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    jcw_str = TBBase.format_dec(jcw, 2)
    width_str = TBBase.format_dec(width, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_johnson2bin_j{jcw_str}_w{width_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'JCW': str(jcw),
        'WIDTH': str(width),
    }

    # Adjust timeout based on test level and complexity
    timeout_multipliers = {'gate': 1, 'func': 3, 'full': 6}
    complexity_factor = max(1.0, jcw / 10.0)
    base_timeout = 8000  # 8 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * complexity_factor)

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
        'TEST_JCW': str(jcw),
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '0',
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
    print(f"Running {test_level.upper()} test: jcw={jcw}, width={width}")
    print(f"Johnson counter sequence length: {2 * jcw}")
    print(f"Binary output range: 0 to {(1 << width) - 1}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ {test_level.upper()} test PASSED: jcw={jcw}, width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        print(f"Note: This test requires the leading_one_trailing_one module")
        raise
