# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RealisticAxiSplitTB
# Purpose: Realistic AXI Split Combinational Logic Test Suite - NO WRAPAROUND
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Realistic AXI Split Combinational Logic Test Suite - NO WRAPAROUND

REALISTIC ASSUMPTIONS:
- No address wraparound ever occurs (transactions never wrap 0xFFFFFFFF -> 0x00000000)
- Focus on comprehensive testing of real-world boundary crossing scenarios
- Robust testing across different data widths and boundary sizes
- Enhanced coverage of legitimate edge cases

COMPREHENSIVE TEST COVERAGE:
1. Boundary crossing with various data widths (32-bit to 512-bit)
2. Multiple boundary sizes (256B to 4KB)
3. Complex multi-boundary crossing scenarios
4. Edge cases near boundaries (but not wraparound)
5. FSM sequence validation for realistic splitting
"""

import os
import random
from itertools import product

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.axi_split_combi_tb import RealisticAxiSplitTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=120000, timeout_unit="us")
async def realistic_axi_split_test(dut):
    """Run the realistic test suite"""
    tb = RealisticAxiSplitTB(dut)
    passed = await tb.run_realistic_test_suite()
    assert passed, f"Realistic test failed with {len(tb.errors)} errors"


def generate_realistic_test_params():
    """Generate test parameters for realistic testing"""
    aw = [32]  # Focus on 32-bit for realistic scenarios
    dw = [32, 64, 128, 512]  # Full data width range
    test_levels = ['gate', 'full']
    test_modes = ['basic', 'sequence']

    return [
        {
            'AW': combo[0],
            'DW': combo[1],
            'test_level': combo[2],
            'test_mode': combo[3]
        }
        for combo in product(aw, dw, test_levels, test_modes)
    ]


@pytest.mark.parametrize("params", generate_realistic_test_params())
def test_axi_split_realistic(request, params):
    """Run realistic test with pytest"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared'
    })

    dut_name = "axi_split_combi"
    toplevel = dut_name
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_split_combi.f")

    # Create test identifier following pattern: test_<module>_<params>
    t_aw = params['AW']
    t_dw = params['DW']
    t_level = params['test_level']
    t_mode = params['test_mode']
    # Format: test_axi_split_combi_aw032_dw064_basic_realistic
    aw_str = f"{t_aw:03d}"
    dw_str = f"{t_dw:03d}"
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_{t_level}_{t_mode}"

    # Setup paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'AW': str(params['AW']),
        'DW': str(params['DW'])
    }

    # Environment
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': params['test_level'],
        'TEST_MODE': params['test_mode'],
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
    }

    # Realistic timeout
    timeout_multiplier = 8.0 if params['test_level'] == 'full' else 4.0
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_multiplier)

    # Compilation arguments
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace", "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-WIDTHEXPAND"
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = ["--trace", "--trace-depth", "99"]
    plus_args = ["--trace"]

    # Create view command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
    except Exception as e:
        print(f"Realistic test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Run realistic test with pytest"""

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared'
    })

    dut_name = "axi_split_combi"
    toplevel = dut_name
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_split_combi.f")

    # Create test identifier following pattern: test_<module>_<params>
    t_aw = params['AW']
    t_dw = params['DW']
    t_level = params['test_level']
    t_mode = params['test_mode']
    # Format: test_axi_split_combi_aw032_dw064_basic_realistic
    aw_str = f"{t_aw:03d}"
    dw_str = f"{t_dw:03d}"
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_{t_level}_{t_mode}"

    # Setup paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'AW': str(params['AW']),
        'DW': str(params['DW'])
    }

    # Environment
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': params['test_level'],
        'TEST_MODE': params['test_mode'],
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
    }

    # Realistic timeout
    timeout_multiplier = 8.0 if params['test_level'] == 'full' else 4.0
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_multiplier)

    # Compilation arguments
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace", "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-WIDTHEXPAND"
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = ["--trace", "--trace-depth", "99"]
    plus_args = ["--trace"]

    # Create view command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
    except Exception as e:
        print(f"Realistic test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise
