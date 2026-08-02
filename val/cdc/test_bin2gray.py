# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Bin2GrayTB
# Purpose: Binary to Gray Code Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary to Gray Code Converter Test

This test verifies the binary to gray code conversion functionality:

CONFIGURATION:
    WIDTH: Bit width of the converter (4, 8, 16, 32)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - WIDTH: [4, 8, 16, 32]
    - test_level: [gate, func, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Bit width for converter

CONVERSION BEHAVIOR:
    Gray code conversion: gray[i] = binary[i] ^ binary[i+1] (except MSB)
    MSB: gray[WIDTH-1] = binary[WIDTH-1]
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.cdc.bin2gray_tb import Bin2GrayTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=60000, timeout_unit="us")
async def bin2gray_test(dut):
    """Test for Binary to Gray Code Converter module"""
    tb = Bin2GrayTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"BIN2GRAY test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Bin2Gray test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke: smallest + largest width, gate depth)
    REG_LEVEL=FUNC: 4 tests (width coverage at gate depth) -- default
    REG_LEVEL=FULL: 12 tests (all widths x all depths)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(4, 'gate'), (32, 'gate')]
    if reg_level == 'FULL':
        return [(w, l) for w in [4, 8, 16, 32] for l in ['gate', 'func', 'full']]
    return [(w, 'gate') for w in [4, 8, 16, 32]]

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_bin2gray(request, width, test_level):
    """
    Parameterized Binary to Gray Code Converter test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "bin2gray"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/cdc/filelists/bin2gray.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)
    test_name_plus_params = f"test_bin2gray_w{width_str}_{test_level}_{reg_level}"

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
        'WIDTH': str(width)
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'gate': 1, 'func': 3, 'full': 6}
    width_factor = max(1.0, (1 << width) / 1000.0) if width <= 16 else max(1.0, width / 8.0)
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
    print(f"Running {test_level.upper()} test: width={width}")
    print(f"Max values to test: {min(2**width, 10000)}")
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
