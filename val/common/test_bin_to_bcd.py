# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BinToBcdTB
# Purpose: Binary to BCD Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary to BCD Converter Test

This test verifies the binary to BCD (Binary Coded Decimal) conversion functionality:

CONFIGURATION:
    WIDTH: Bit width of binary input (8, 12, 16)
    DIGITS: Number of BCD digits output (3, 4, 5)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (5-10 min): Integration testing for CI/branches
    full (15-30 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - (WIDTH=8, DIGITS=3): 0-255 -> 000-255
    - (WIDTH=12, DIGITS=4): 0-4095 -> 0000-4095
    - (WIDTH=16, DIGITS=5): 0-65535 -> 00000-65535

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Binary input width
    TEST_DIGITS: BCD output digits

BCD CONVERSION BEHAVIOR:
    Uses double dabble algorithm with FSM
    Each BCD digit is 4 bits (0-9)
    Sequential operation: start -> shifting -> adding -> done
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
from TBClasses.common.bin_to_bcd_tb import BinToBcdTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=120000, timeout_unit="us")
async def bin_to_bcd_test(dut):
    """Test for Binary to BCD Converter module"""
    tb = BinToBcdTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"BIN_TO_BCD test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"BinToBcd test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Valid parameter combinations based on typical usage
    param_combinations = [
        (8, 3),   # 8-bit binary (0-255) -> 3 BCD digits (000-255)
        (12, 4),  # 12-bit binary (0-4095) -> 4 BCD digits (0000-4095)
        (16, 5),  # 16-bit binary (0-65535) -> 5 BCD digits (00000-65535)
    ]

    if reg_level == 'GATE':
        # GATE: Minimal - just 8-bit
        param_combinations = [(8, 3)]
        test_levels = ['gate']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        param_combinations = [(8, 3), (12, 4)]
        test_levels = ['func']
    else:  # FULL
        # FULL: All widths
        test_levels = ['full']

    valid_params = []
    for (width, digits), test_level in product(param_combinations, test_levels):
        valid_params.append((width, digits, test_level))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, digits, test_level", params)
def test_bin_to_bcd(request, width, digits, test_level):
    """
    Parameterized Binary to BCD Converter test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "bin_to_bcd"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/bin_to_bcd.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)
    digits_str = TBBase.format_dec(digits, 1)
    test_name_plus_params = f"test_bin_to_bcd_w{width_str}_d{digits_str}_{test_level}_{reg_level}"

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
        'WIDTH': str(width),
        'DIGITS': str(digits)
    }

    # Adjust timeout based on test level and complexity
    timeout_multipliers = {'gate': 1, 'func': 5, 'full': 10}
    # BCD conversion is sequential and can take many cycles
    complexity_factor = (2 ** width) / 1000.0 if width <= 12 else width / 2.0
    base_timeout = 10000  # 10 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

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
        'TEST_DIGITS': str(digits),
        'TEST_DEBUG': '0',
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

    max_binary = (1 << width) - 1
    max_bcd = int('9' * digits)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}, digits={digits}")
    print(f"Binary range: 0 to {max_binary}")
    print(f"BCD range: 0 to {max_bcd}")
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}, digits={digits}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise