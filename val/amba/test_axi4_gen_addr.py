# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiGenAddrConfig
# Purpose: Configuration class for AXI Address Generator tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import contextlib
import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.axi4_gen_addr_tb import AxiGenAddrTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


class AxiGenAddrConfig:
    """Configuration class for AXI Address Generator tests"""
    def __init__(self, name, test_vectors, aw=32, dw=32, odw=32, len_width=8):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            test_vectors: List of test vectors (dict with addr, size, burst, len, expected_next, expected_align)
            aw: Address width
            dw: Data width
            odw: Output data width
            len_width: Length parameter width
        """
        self.name = name
        self.test_vectors = test_vectors
        self.aw = aw
        self.dw = dw
        self.odw = odw
        self.len_width = len_width




@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = AxiGenAddrTB(dut)

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


@pytest.mark.parametrize("params", [
    # Test with standard configurations
    # {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'gate'},
    # {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'func'},
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'full'},

    # Test with different data widths
    {'AW': 32, 'DW': 64, 'ODW': 32, 'LEN': 8, 'test_level': 'full'},  # DW > ODW
    {'AW': 32, 'DW': 32, 'ODW': 64, 'LEN': 8, 'test_level': 'full'},  # DW < ODW

    # Test with different address widths
    {'AW': 24, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'gate'},
    {'AW': 64, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'gate'},

    # Test with different length parameter
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 4, 'test_level': 'gate'},
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 16, 'test_level': 'gate'},
])
def test_axi_gen_addr(request, params):
    """Run the test with pytest and configurable parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba_shared':'rtl/amba/shared',
        })

    dut_name = "axi_gen_addr"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_gen_addr.f")

    # Create a human-readable test identifier
    t_aw = params['AW']
    t_dw = params['DW']
    t_odw = params['ODW']
    t_len = params['LEN']
    t_name = params['test_level']
    # Format parameters with lowercase and zero-padding for consistent sorting
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{t_aw:03d}_dw{t_dw:03d}_odw{t_odw:03d}_len{t_len:02d}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=includes

    # RTL parameters
    parameters = {}
    # sourcery skip: no-conditionals-in-tests
    if 'AW' in params:
        parameters['AW'] = params['AW']
    if 'DW' in params:
        parameters['DW'] = params['DW']
    if 'ODW' in params:
        parameters['ODW'] = params['ODW']
    if 'LEN' in params:
        parameters['LEN'] = params['LEN']

    # Convert parameters to format expected by simulator
    rtl_parameters = {k.upper(): str(v) for k, v in parameters.items()}

    # Prepare environment variables
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),  # str(seed),
        'TEST_LEVEL': params['test_level'],
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
        'TEST_ODW': str(params['ODW']),
        'TEST_LEN': str(params['LEN'])
    }

    # Calculate timeout based on test complexity
    complexity_factor = 1.0
    if params['test_level'] == 'func':
        complexity_factor = 2.0
    elif params['test_level'] == 'full':
        complexity_factor = 5.0
    timeout_factor = complexity_factor * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
            "--trace",
            
            "--trace-depth", "99",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = [
            "--trace",  # Tell Verilator to use VCD
            
            "--trace-depth", "99",
    ]

    plus_args = [
            "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
