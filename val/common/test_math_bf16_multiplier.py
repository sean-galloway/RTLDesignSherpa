# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_multiplier
# Purpose: Test for the BF16 floating-point multiplier module.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the BF16 floating-point multiplier module.

Tests the complete BF16 multiplier including:
- Normal multiplication with RNE rounding
- Special value handling (zero, infinity, NaN, subnormal)
- Overflow and underflow detection
- Invalid operation detection (0 * inf)
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the BF16 testbench class
from CocoTBFramework.tbclasses.common.bf16_testing import BF16MultiplierTB


def get_bf16_mult_params():
    """Generate BF16 multiplier test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'test_level': 'simple'},  # GATE: Minimal test
        ]
    elif reg_level == 'FUNC':
        return [
            {'test_level': 'basic'},  # FUNC: Basic coverage
        ]
    else:  # FULL
        return [
            {'test_level': 'simple'},
            {'test_level': 'basic'},
            {'test_level': 'medium'},
            {'test_level': 'full'},
        ]


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def bf16_multiplier_test(dut):
    """Test the BF16 multiplier"""
    tb = BF16MultiplierTB(dut)

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


@pytest.mark.parametrize("params", get_bf16_mult_params())
def test_math_bf16_multiplier(request, params):
    """PyTest function to run the cocotb test for BF16 multiplier."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_bf16_multiplier"
    toplevel = dut_name
    t_name = params['test_level']

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Create a human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # BF16 multiplier depends on these modules (in dependency order):
    verilog_sources = [
        # Basic building blocks
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_compressor_4to2.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_prefix_cell_gray.sv"),
        # Generated BF16 modules
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_han_carlson_016.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_multiplier_dadda_4to2_008.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_mantissa_mult.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_exponent_adder.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_bf16_multiplier.sv"),
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
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
    }

    # VCD waveform generation support
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

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
            parameters={},
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
