# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HexTo7SegTB
# Purpose: Hexadecimal to 7-Segment Display Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Hexadecimal to 7-Segment Display Converter Test

This test verifies the hex to 7-segment display conversion functionality:

CONFIGURATION:
    Fixed 4-bit hex input, 7-bit segment output

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility

7-SEGMENT DISPLAY BEHAVIOR:
    Converts 4-bit hex values (0x0-0xF) to 7-segment display patterns
    Segments are typically arranged as:
         a
       f   b
         g
       e   c
         d
    
    Output format: {g,f,e,d,c,b,a} where 0=on, 1=off (common anode)
"""

import os
import sys
import random
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.hex_to_7seg_tb import HexTo7SegTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=30, timeout_unit="us")
async def hex_to_7seg_test(dut):
    """Test for Hexadecimal to 7-Segment Display Converter module"""
    tb = HexTo7SegTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"HEX_TO_7SEG test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"HexTo7Seg test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters"""
    # Fixed 4-bit input, so the grid varies only in depth.
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        test_levels = ['gate']
    elif reg_level == 'FULL':
        test_levels = ['gate', 'func', 'full']
    else:
        test_levels = ['func']

    valid_params = []
    for test_level in test_levels:
        valid_params.append((test_level,))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("test_level", params)
def test_hex_to_7seg(request, test_level):
    """
    Parameterized Hexadecimal to 7-Segment Display Converter test
    """
    # Extract test_level from tuple
    if isinstance(test_level, tuple):
        test_level = test_level[0]
    
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "hex_to_7seg"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/hex_to_7seg.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    test_name_plus_params = f"test_hex_to_7seg_{test_level}_{reg_level}"

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

    # No RTL parameters needed for this module
    parameters = {}

    # Adjust timeout based on test level
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 3}
    base_timeout = 3000  # 3 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1))

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
        'TEST_DEBUG': '1' if test_level == 'full' else '0',
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
    print(f"Running {test_level.upper()} test: hex_to_7seg")
    print(f"Testing all 16 hex values (0x0-0xF)")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # from the filelist; was [] and dropped +incdir
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ {test_level.upper()} test PASSED: hex_to_7seg")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
