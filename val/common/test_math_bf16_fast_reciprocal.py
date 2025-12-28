# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_fast_reciprocal
# Purpose: Test for the BF16 fast reciprocal module (LUT-based).
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-26

"""
Test for the BF16 fast reciprocal module.

Tests the LUT-based fast reciprocal (1/x) including:
- Normal reciprocal operations
- Zero/infinity handling
- NaN handling
- Powers of two (exact reciprocals)
- Accuracy across mantissa range
- Random value testing with ULP tolerance based on LUT depth
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the BF16 fast reciprocal testbench class
from CocoTBFramework.tbclasses.common.bf16_testing import BF16FastReciprocalTB


def get_bf16_fast_reciprocal_params():
    """Generate BF16 fast reciprocal test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'test_level': 'simple', 'lut_depth': 32},  # GATE: Minimal test
        ]
    elif reg_level == 'FUNC':
        return [
            {'test_level': 'basic', 'lut_depth': 32},  # FUNC: Basic coverage
        ]
    else:  # FULL
        return [
            {'test_level': 'simple', 'lut_depth': 32},
            {'test_level': 'basic', 'lut_depth': 32},
            {'test_level': 'medium', 'lut_depth': 32},
            {'test_level': 'basic', 'lut_depth': 64},
            {'test_level': 'basic', 'lut_depth': 128},
            {'test_level': 'full', 'lut_depth': 32},
        ]


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def bf16_fast_reciprocal_test(dut):
    """Test the BF16 fast reciprocal"""
    tb = BF16FastReciprocalTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    # Print testbench settings
    tb.print_settings()

    # Clear and initialize interface
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')

    # Run the comprehensive test suite
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_bf16_fast_reciprocal_params())
def test_math_bf16_fast_reciprocal(request, params):
    """PyTest function to run the cocotb test for BF16 fast reciprocal."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_fast_reciprocal"
    toplevel = dut_name
    t_name = params['test_level']
    lut_depth = params['lut_depth']

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Create a human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_{t_name}_lut{lut_depth}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # BF16 fast reciprocal is standalone (no dependencies)
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_fast_reciprocal.sv"),
    ]

    # RTL parameters
    rtl_parameters = {
        'LUT_DEPTH': lut_depth,
    }

    # Define simulation build and log paths
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Define log path
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Set up environment variables
    seed = random.randint(0, 100000)

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'LUT_DEPTH': str(lut_depth),
    }

    # VCD waveform generation support
    compile_args = [
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
