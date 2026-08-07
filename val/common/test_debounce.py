# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DebounceTB
# Purpose: Debounce Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Debounce Test with Parameterized Test Levels and Configuration

This test uses num_buttons, debounce_delay, pressed_state and test_level as parameters:

CONFIGURATION:
    num_buttons:     Number of button inputs (1, 2, 4, 8)
    debounce_delay:  Debounce delay in tick cycles (2, 4, 8)
    pressed_state:   State when button is pressed (0=NC, 1=NO)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_NUM_BUTTONS: Number of button inputs
    TEST_DEBOUNCE_DELAY: Debounce delay in cycles
    TEST_PRESSED_STATE: Pressed state (0 or 1)
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
from TBClasses.common.debounce_tb import DebounceTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def debounce_test(dut):
    """Test for Debounce module"""
    tb = DebounceTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"DEBOUNCE test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Debounce test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        num_buttons_list, debounce_delays, pressed_states, test_levels = \
            [4], [4], [1], ['gate']
    elif reg_level == 'FULL':
        num_buttons_list, debounce_delays, pressed_states, test_levels = \
            [1, 2, 4], [2, 4, 8], [0, 1], ['full']
    else:
        num_buttons_list, debounce_delays, pressed_states, test_levels = \
            [2, 4], [4], [0, 1], ['func']

    valid_params = []
    for num_buttons, debounce_delay, pressed_state, test_level in product(
        num_buttons_list, debounce_delays, pressed_states, test_levels):
        valid_params.append((num_buttons, debounce_delay, pressed_state, test_level))

    # For debugging, uncomment one of these:
    # return [(4, 4, 1, 'gate')]  # Single test
    # return [(2, 4, 1, 'func')]  # Just specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("num_buttons, debounce_delay, pressed_state, test_level", params)
def test_debounce(request, num_buttons, debounce_delay, pressed_state, test_level):
    """
    Parameterized Debounce test with configurable parameters and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "debounce"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/debounce.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(num_buttons, 1)
    d_str = TBBase.format_dec(debounce_delay, 1)
    p_str = "no" if pressed_state else "nc"
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_debounce_n{n_str}_d{d_str}_{p_str}_{test_level}_{reg_level}"

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
        'N': str(num_buttons),
        'DEBOUNCE_DELAY': str(debounce_delay),
        'PRESSED_STATE': str(pressed_state)
    }

    # Adjust timeout based on test level
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    base_timeout = 2000  # 2 seconds base
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
        'TEST_NUM_BUTTONS': str(num_buttons),
        'TEST_DEBOUNCE_DELAY': str(debounce_delay),
        'TEST_PRESSED_STATE': str(pressed_state),
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
    print(f"Running {test_level.upper()} test: {num_buttons} buttons, delay={debounce_delay}, {p_str}")
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
        print(f"✓ {test_level.upper()} test PASSED: {num_buttons} buttons, {p_str}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
