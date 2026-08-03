# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_multiplier_dadda_4to2
# Purpose: Test for the Dadda 4:2 multiplier module (8-bit).
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Test for the Dadda 4:2 multiplier module.

This multiplier is used in the BF16 mantissa multiplication (8x8).
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.math.math_multiplier_dadda_4to2_tb import DaddaMultiplierTB
from TBClasses.shared.tbbase import TBBase


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def dadda_multiplier_test(dut):
    """Test the Dadda 4:2 multiplier"""
    tb = DaddaMultiplierTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')

    tb.print_settings()
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    await tb.run_comprehensive_tests()

def get_multiplier_params():
    """Generate multiplier parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'width': 8, 'test_level': 'gate'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'width': 8, 'test_level': 'func'},
        ]
    else:  # FULL - exhaustive testing for 100% coverage
        return [
            {'width': 8, 'test_level': 'full'},
        ]

@pytest.mark.parametrize("params", get_multiplier_params())
def test_math_multiplier_dadda_4to2(request, params):
    """PyTest function to run the cocotb test for Dadda multiplier."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'
    })

    width = params['width']
    dut_name = f"math_multiplier_dadda_4to2_{width:03d}"
    toplevel = dut_name
    t_level = params['test_level']

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_level}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Dadda multiplier dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_math'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_math'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_math'], "math_compressor_4to2.sv"),
        os.path.join(rtl_dict['rtl_math'], "math_prefix_cell.sv"),
        os.path.join(rtl_dict['rtl_math'], "math_prefix_cell_gray.sv"),
        os.path.join(rtl_dict['rtl_math'], "math_adder_han_carlson_016.sv"),
        os.path.join(rtl_dict['rtl_math'], f"{dut_name}.sv"),
    ]

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'PARAM_N': str(width),
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    sim_args = ['--trace'] if enable_waves else []

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters={'N': width},
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
