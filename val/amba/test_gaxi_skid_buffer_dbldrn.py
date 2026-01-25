# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_skid_buffer_dbldrn
# Purpose: GAXI Skid Buffer Double-Drain Test with Parameterized Test Levels
#
# Documentation: PRD.md, docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer_dbldrn.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-25

"""
GAXI Skid Buffer Double-Drain Test with Parameterized Test Levels

Tests gaxi_skid_buffer_dbldrn.sv - skid buffer with double-drain capability.
When rd_ready2 is asserted (only legal when rd_count >= 2), two items are
drained simultaneously via rd_data and rd_data2.

TEST LEVELS (per-test depth):
    basic (2-3 min):   Quick verification during development
    medium (5-8 min):  Integration testing for CI/branches
    full (15-25 min):  Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~3 min) - smoke test
    FUNC: 4 tests (~15 min) - functional coverage - DEFAULT
    FULL: 36 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width x 1 depth x 1 test_level = 1 test
    FUNC: 2 widths x 1 depth x 2 test_levels = 4 tests
    FULL: 4 widths x 3 depths x 3 test_levels = 36 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: basic|medium|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_dbldrn import GaxiBufferDblDrnTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def gaxi_skid_buffer_dbldrn_test(dut):
    '''Test the GAXI Skid Buffer Double-Drain comprehensively'''
    tb = GaxiBufferDblDrnTB(dut, dut.axi_aclk, dut.axi_aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    # Get test level from environment (default: basic)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    tb.log.info(f"Running test level: {test_level.upper()}")

    # Initialize
    await tb.setup_clocks_and_reset()
    tb.log.info(f"Starting {test_level.upper()} GAXI Skid Buffer Double-Drain test...")

    # Run all tests for the specified level
    all_passed = await tb.run_all_tests(test_level)

    assert all_passed, f"Test failures detected! Total errors: {tb.total_errors}"
    tb.log.info(f"ALL {test_level.upper()} GAXI SKID BUFFER DOUBLE-DRAIN TESTS PASSED!")


def generate_test_params():
    """
    Generate test parameters for gaxi_skid_buffer_dbldrn based on REG_LEVEL.

    REG_LEVEL values:
        GATE: 1 test - minimal smoke test (~3 min)
        FUNC: 4 tests - functional coverage (~15 min) - DEFAULT
        FULL: 36 tests - comprehensive validation (~2 hours)

    For debugging, override REG_LEVEL:
        REG_LEVEL=GATE pytest test_gaxi_skid_buffer_dbldrn.py -v
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal smoke test - just prove it works
        return [
            (8, 4, 10, 'basic'),  # One basic configuration
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - key combinations
        widths = [8, 32]
        depths = [4]
        clk_periods = [10]
        test_levels = ['basic', 'medium']

        return list(product(widths, depths, clk_periods, test_levels))
        # Result: 2 widths x 1 depth x 2 levels = 4 tests

    else:  # FULL
        # Comprehensive testing - all meaningful combinations
        widths = [8, 16, 32, 64]
        depths = [4, 6, 8]  # Minimum 4 for double-drain to be useful
        clk_periods = [10]
        test_levels = ['basic', 'medium', 'full']

        return list(product(widths, depths, clk_periods, test_levels))
        # Result: 4 widths x 3 depths x 3 levels = 36 tests


params = generate_test_params()


@pytest.mark.parametrize("data_width, depth, clk_period, test_level", params)
def test_gaxi_skid_buffer_dbldrn(request, data_width, depth, clk_period, test_level):
    """
    Parameterized GAXI skid buffer double-drain test with configurable test levels.

    Tests gaxi_skid_buffer_dbldrn.sv - skid buffer with double-drain capability.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min)
    - medium: Integration testing (5-8 min)
    - full: Comprehensive validation (15-25 min)
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get all directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "gaxi_skid_buffer_dbldrn"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], f"{dut_name}.sv"),
    ]

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cl_str = TBBase.format_dec(clk_period, 3)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_gaxi_skid_buffer_dbldrn_w{w_str}_d{d_str}_cl{cl_str}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]

    # RTL parameters
    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'INSTANCE_NAME': f'"dbldrn_{test_level}"'
    }

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 5000  # 5 seconds base (more complex than standard skid)
    timeout_ms = base_timeout * timeout_multipliers.get(test_level, 1)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(clk_period),
        'TEST_CLK_RD': str(clk_period),
        'TEST_MODE': 'skid',
        'TEST_KIND': 'sync'
    }

    # VCD waveform generation support via WAVES environment variable
    compile_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} test: gaxi_skid_buffer_dbldrn")
    print(f"Config: depth={depth}, width={data_width}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            testcase="gaxi_skid_buffer_dbldrn_test",
        )
        print(f"PASS {test_level.upper()} test PASSED: gaxi_skid_buffer_dbldrn")
    except Exception as e:
        print(f"FAIL {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic test by default
    test_gaxi_skid_buffer_dbldrn(None, 8, 4, 10, 'basic')
