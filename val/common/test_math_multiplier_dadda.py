# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_multiplier_dadda
# Purpose: Test for the Dadda tree multiplier module.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test for the Dadda tree multiplier module.
"""
import os
import sys
import random
import subprocess
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the base MultiplierTB class
from CocoTBFramework.tbclasses.common.multiplier_testing import MultiplierTB

def get_multiplier_params():
    """Generate multiplier test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},  # GATE: Minimal - just 8-bit basic
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},  # FUNC: Small and medium widths
            {'WIDTH': 16, 'test_level': 'basic'},
        ]
    else:  # FULL
        return [
            # Basic tests with different widths
            {'WIDTH': 8, 'test_level': 'simple'},
            {'WIDTH': 8, 'test_level': 'basic'},
            # Different bit widths with basic testing
            {'WIDTH': 16, 'test_level': 'basic'},
            {'WIDTH': 32, 'test_level': 'basic'},
            # More comprehensive testing
            {'WIDTH': 8, 'test_level': 'medium'},
            {'WIDTH': 16, 'test_level': 'medium'},
            # Full test suite
            {'WIDTH': 16, 'test_level': 'full'},
        ]

@cocotb.test(timeout_time=1, timeout_unit="ms")
async def multiplier_test(dut):
    """Test the Dadda tree multiplier"""
    tb = MultiplierTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Print testbench settings
    tb.print_settings()

    # Clear and initialize interface
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    # Run the comprehensive test suite
    await tb.run_comprehensive_tests()

@pytest.mark.parametrize("params", get_multiplier_params())
def test_math_multiplier_dadda_tree(request, params):
    """PyTest function to run the cocotb test."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    # The module name is specific to the bit width for Dadda tree
    n = params['WIDTH']
    t_name = params['test_level']
    dut_name = f"math_multiplier_dadda_tree_{n:03d}"
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create a human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_carry_save.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

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
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'PARAM_N': str(params['WIDTH'])
    }

    # Create command file for viewing waveforms

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Launch the simulation

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters={'N': params['WIDTH']},
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure