# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_adder
# Purpose: Test for the BF16 floating-point adder module.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-26

"""
Test for the BF16 floating-point adder module.

Tests the complete BF16 adder including:
- Normal addition and subtraction with RNE rounding
- Special value handling (zero, infinity, NaN, subnormal)
- Overflow and underflow detection
- Invalid operation detection (inf - inf)
- Pipeline operation with valid handshaking
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the BF16 testbench class
from CocoTBFramework.tbclasses.common.bf16_testing import BF16AdderTB


def get_bf16_adder_params():
    """Generate BF16 adder test parameters based on REG_LEVEL.

    Test levels:
    - simple: Special values only (~22 tests)
    - basic: Special + corner + walking patterns + random50 (~150 tests)
    - medium: All basic + exponent sweep + alternating + random200 (~500 tests)
    - full: All patterns + cancellation + boundary + random1000 (~1500 tests)

    Pipeline stages: [PIPE_STAGE_1, PIPE_STAGE_2, PIPE_STAGE_3, PIPE_STAGE_4]
    - [0,0,0,0] = combinational (1 cycle latency)
    - [1,0,0,0] = 1-stage pipeline (2 cycle latency)
    - [1,1,1,1] = 4-stage pipeline (5 cycle latency)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'test_level': 'simple', 'pipe_stages': [0, 0, 0, 0]},  # GATE: Minimal test, combinational
        ]
    elif reg_level == 'FUNC':
        return [
            # Combinational variant with basic coverage
            {'test_level': 'basic', 'pipe_stages': [0, 0, 0, 0]},
            # Pipelined variant - tests pipeline handshaking
            {'test_level': 'basic', 'pipe_stages': [1, 1, 1, 1]},
        ]
    else:  # FULL
        return [
            # Combinational variants at all test levels
            {'test_level': 'simple', 'pipe_stages': [0, 0, 0, 0]},
            {'test_level': 'basic', 'pipe_stages': [0, 0, 0, 0]},
            {'test_level': 'medium', 'pipe_stages': [0, 0, 0, 0]},
            {'test_level': 'full', 'pipe_stages': [0, 0, 0, 0]},
            # Pipelined variants
            {'test_level': 'basic', 'pipe_stages': [1, 0, 0, 0]},  # 1-stage at input
            {'test_level': 'basic', 'pipe_stages': [0, 0, 0, 1]},  # 1-stage at output
            {'test_level': 'basic', 'pipe_stages': [1, 1, 1, 1]},  # 4-stage pipeline
            {'test_level': 'medium', 'pipe_stages': [1, 1, 1, 1]}, # 4-stage with more coverage
        ]


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def bf16_adder_test(dut):
    """Test the BF16 adder"""
    tb = BF16AdderTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    # Print testbench settings
    tb.print_settings()

    # Set up clocks and reset (adder has clock/reset unlike multiplier)
    await tb.setup_clocks_and_reset()

    # Clear and initialize interface
    await tb.clear_interface()

    # Run the comprehensive test suite
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_bf16_adder_params())
def test_math_bf16_adder(request, params):
    """PyTest function to run the cocotb test for BF16 adder."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_adder"
    toplevel = dut_name
    t_name = params['test_level']
    pipe_stages = params['pipe_stages']
    pipe_str = ''.join(str(p) for p in pipe_stages)

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Create a human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_{t_name}_pipe{pipe_str}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # BF16 adder dependencies (in dependency order):
    verilog_sources = [
        # Basic building blocks
        os.path.join(rtl_dict['rtl_cmn'], "shifter_barrel.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "count_leading_zeros.sv"),
        # BF16 adder
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_adder.sv"),
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

    # RTL parameters for pipeline stages
    rtl_parameters = {
        'PIPE_STAGE_1': pipe_stages[0],
        'PIPE_STAGE_2': pipe_stages[1],
        'PIPE_STAGE_3': pipe_stages[2],
        'PIPE_STAGE_4': pipe_stages[3],
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        # Pass pipeline stages to testbench
        'PIPE_STAGE_1': str(pipe_stages[0]),
        'PIPE_STAGE_2': str(pipe_stages[1]),
        'PIPE_STAGE_3': str(pipe_stages[2]),
        'PIPE_STAGE_4': str(pipe_stages[3]),
    }

    # VCD waveform generation support
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
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
            simulator='verilator',
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
