# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_dataint_crc
# Purpose: Test the CRC calculation for a basic input Across 250 Configurations
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random

import pytest
import cocotb
from cocotb_test.simulator import run


# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.common.crc_testing import CRCTB, crc_parameters
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def crc_basic_test(dut):
    """ Test the CRC calculation for a basic input Across 250 Configurations"""
    tb = CRCTB(dut, 100)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    tb.print_settings()
    tb.generate_test_data()

    await tb.start_clock('clk', 10, 'ns')
    tb.assert_reset()
    await tb.wait_clocks('clk', 10)
    tb.deassert_reset()
    await tb.wait_clocks('clk', 10)
    await tb.main_loop()



# @pytest.mark.parametrize("params", [
#     # Only use the first entry from crc_parameters list
#     {
#         'algo_name': crc_parameters[0][0],
#         'data_width': crc_parameters[0][1],
#         'crc_width': crc_parameters[0][2],
#         'poly': crc_parameters[0][3],
#         'poly_init': crc_parameters[0][4],
#         'refin': crc_parameters[0][5],
#         'refout': crc_parameters[0][6],
#         'xorout': crc_parameters[0][7],
#         'test_level': 'basic'
#     }
# ])
def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 CRC algorithms
    REG_LEVEL=FUNC: 10 CRC algorithms - default
    REG_LEVEL=FULL: all CRC algorithms (~20)

    Returns:
        List of dicts with CRC parameters
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Quick smoke test: CRC-8 and CRC-16
        selected = crc_parameters[0:2]
    elif reg_level == 'FUNC':
        # Functional coverage: first 10 algorithms
        selected = crc_parameters[0:10]
    else:  # FULL
        # Comprehensive: all algorithms
        selected = crc_parameters

    return [
        {
            'algo_name': entry[0],
            'data_width': entry[1],
            'crc_width': entry[2],
            'poly': entry[3],
            'poly_init': entry[4],
            'refin': entry[5],
            'refout': entry[6],
            'xorout': entry[7],
            'test_level': 'basic'
        } for entry in selected
    ]


@pytest.mark.parametrize("params", generate_test_params())
def test_dataint_crc(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'}
    )

    dut_name = "dataint_crc"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/dataint_crc.f'
    )

    # Create a human-readable test identifier
    algorithm = params['algo_name']
    data_w = params['data_width']
    crc_w = params['crc_width']
    refin = params['refin']
    refout = params['refout']
    t_name = params['test_level']

    test_name_plus_params = f"test_{dut_name}_{algorithm}_DW{data_w}_CW{crc_w}_RI{refin}_RO{refout}_{t_name}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    parameters = {
        # 'ALGO_NAME': params['algo_name'],
        'DATA_WIDTH': params['data_width'],
        'CRC_WIDTH': params['crc_width'],
        'REFIN': params['refin'],
        'REFOUT': params['refout'],
    }

    # Prepare environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),
        'TEST_LEVEL': params['test_level'],
        'PARAM_POLY': params['poly'],
        'PARAM_POLY_INIT': params['poly_init'],
        'PARAM_XOROUT': params['xorout'],
    }

    # Pass all parameters as environment variables for consistency
    # sourcery skip: no-loop-in-tests
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    # Calculate timeout based on test complexity
    timeout_factor = 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


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

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
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
