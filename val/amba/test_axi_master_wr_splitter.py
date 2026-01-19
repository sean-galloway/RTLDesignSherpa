# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_master_wr_splitter
# Purpose: AXI Master Write Splitter Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Master Write Splitter Test Runner

Comprehensive test runner for the AXI master write splitter module following
the patterns established in the test_axi_master_rd_splitter.py test runner.

Features:
- Parametrized testing with pytest
- Multiple test levels (basic, medium, full)
- Comprehensive parameter combinations
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Write-specific verification and testing
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi_splitter.axi_write_splitter_tb import AxiWriteSplitterTB


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi_write_splitter_test(dut):
    """Main test function for AXI write splitter"""
    tb = AxiWriteSplitterTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI Write Splitter test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    tb.log.info(f"Starting {test_level.upper()} AXI write splitter test...")
    tb.log.info(f"Parameters: IW={tb.IW}, AW={tb.AW}, DW={tb.DW}, UW={tb.UW}")
    tb.log.info(f"FIFO Depth={tb.SPLIT_FIFO_DEPTH}, Alignment=0x{tb.ALIGNMENT_MASK:03X}")

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"AXI write splitter test failed at level {test_level}"

    tb.log.info(f"✓ ALL {test_level.upper()} AXI WRITE SPLITTER TESTS PASSED!")


def generate_test_params():
    """Generate comprehensive test parameter combinations"""
    iw = [8]
    # aw = [32, 40, 64]
    aw = [32]
    dw = [32, 64, 128, 512]
    # dw = [512]
    uw = [8]
    fifo_depths = [4]
    alignment_masks = [0x0FF, 0x1FF, 0x3FF, 0x7FF, 0xFFF]
    # alignment_masks = [0x0FF]
    test_levels = ['full']
    return [(8, 32, 512, 8, 4, 0xFFF, 'full')]
    return list(product(iw, aw, dw, uw, fifo_depths, alignment_masks, test_levels))

@pytest.mark.parametrize("iw, aw, dw, uw, fifo_depth, alignment_mask, test_level", generate_test_params())
def test_axi_write_splitter(request, iw, aw, dw, uw, fifo_depth, alignment_mask, test_level):
    """Test AXI write splitter with parametrized configurations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':         'rtl/common',
        'rtl_gaxi':        'rtl/amba/gaxi',
        'rtl_axi4':        'rtl/amba/axi4/',
        'rtl_amba_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Set up test names and directories
    dut_name = "axi_master_wr_splitter"

    # Create human-readable test identifier
    iw_str = TBBase.format_dec(iw, 2)
    aw_str = TBBase.format_dec(aw, 2)
    dw_str = TBBase.format_dec(dw, 3)
    uw_str = TBBase.format_dec(uw, 2)
    fd_str = TBBase.format_dec(fifo_depth, 2)
    am_str = f"{alignment_mask:04X}"

    test_name_plus_params = (f"test_axi_wr_splitter_"
                            f"iw{iw_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_"
                            f"fd{fd_str}_am{am_str}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources
    verilog_sources = [
        # Dependencies
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], f"axi_split_combi.sv"),
        # Main DUT
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH': str(iw),
        'AXI_ADDR_WIDTH': str(aw),
        'AXI_DATA_WIDTH': str(dw),
        'AXI_USER_WIDTH': str(uw),
        'SPLIT_FIFO_DEPTH': str(fifo_depth),
        # Short names for convenience
        'IW': str(iw),
        'AW': str(aw),
        'DW': str(dw),
        'UW': str(uw),
    }

    # Calculate timeout based on test complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = timeout_multipliers.get(test_level, 1)

    # Additional complexity factors
    data_complexity = max(1.0, dw / 64.0)  # Wider data = more complex
    fifo_complexity = max(1.0, fifo_depth / 8.0)  # Deeper FIFO = more complex
    id_complexity = max(1.0, iw / 8.0)  # More IDs = more complex
    
    # Write splitter has additional complexity due to three-channel flow (AW + W + B)
    write_complexity = 1.5  # Write is more complex than read due to data generation

    total_complexity = complexity_factor * data_complexity * fifo_complexity * id_complexity * write_complexity
    timeout_s = int(10 * total_complexity)  # Base 10s timeout

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_s * 1000),  # Convert to ms

        # DUT-specific parameters
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UW': str(uw),
        'TEST_SPLIT_FIFO_DEPTH': str(fifo_depth),
        'TEST_ALIGNMENT_MASK': str(alignment_mask),
        'TEST_CLOCK_PERIOD': '10',  # 10ns = 100MHz
        'TEST_TIMEOUT_CYCLES': '1000',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected ports for testbench
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",
        
        "--trace-depth", "99"
    ]
    plusargs = ["--trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI Write Splitter test")
    print(f"Parameters: IW={iw}, AW={aw}, DW={dw}, UW={uw}")
    print(f"FIFO Depth={fifo_depth}, Alignment=0x{alignment_mask:X}")
    print(f"Expected duration: {timeout_s}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} AXI Write Splitter test PASSED")

    except Exception as e:
        print(f"✗ {test_level.upper()} AXI Write Splitter test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Test AXI write splitter with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':         'rtl/common',
        'rtl_gaxi':        'rtl/amba/gaxi',
        'rtl_axi4':        'rtl/amba/axi4/',
        'rtl_amba_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Set up test names and directories
    dut_name = "axi_master_wr_splitter"

    # Create human-readable test identifier
    iw_str = TBBase.format_dec(iw, 2)
    aw_str = TBBase.format_dec(aw, 2)
    dw_str = TBBase.format_dec(dw, 3)
    uw_str = TBBase.format_dec(uw, 2)
    fd_str = TBBase.format_dec(fifo_depth, 2)
    am_str = f"{alignment_mask:04X}"

    test_name_plus_params = (f"test_axi_wr_splitter_"
                            f"iw{iw_str}_aw{aw_str}_dw{dw_str}_uw{uw_str}_"
                            f"fd{fd_str}_am{am_str}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources
    verilog_sources = [
        # Dependencies
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], f"axi_split_combi.sv"),
        # Main DUT
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH': str(iw),
        'AXI_ADDR_WIDTH': str(aw),
        'AXI_DATA_WIDTH': str(dw),
        'AXI_USER_WIDTH': str(uw),
        'SPLIT_FIFO_DEPTH': str(fifo_depth),
        # Short names for convenience
        'IW': str(iw),
        'AW': str(aw),
        'DW': str(dw),
        'UW': str(uw),
    }

    # Calculate timeout based on test complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = timeout_multipliers.get(test_level, 1)

    # Additional complexity factors
    data_complexity = max(1.0, dw / 64.0)  # Wider data = more complex
    fifo_complexity = max(1.0, fifo_depth / 8.0)  # Deeper FIFO = more complex
    id_complexity = max(1.0, iw / 8.0)  # More IDs = more complex
    
    # Write splitter has additional complexity due to three-channel flow (AW + W + B)
    write_complexity = 1.5  # Write is more complex than read due to data generation

    total_complexity = complexity_factor * data_complexity * fifo_complexity * id_complexity * write_complexity
    timeout_s = int(10 * total_complexity)  # Base 10s timeout

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_s * 1000),  # Convert to ms

        # DUT-specific parameters
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_DW': str(dw),
        'TEST_UW': str(uw),
        'TEST_SPLIT_FIFO_DEPTH': str(fifo_depth),
        'TEST_ALIGNMENT_MASK': str(alignment_mask),
        'TEST_CLOCK_PERIOD': '10',  # 10ns = 100MHz
        'TEST_TIMEOUT_CYCLES': '1000',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected ports for testbench
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",
        
        "--trace-depth", "99"
    ]
    plusargs = ["--trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI Write Splitter test")
    print(f"Parameters: IW={iw}, AW={aw}, DW={dw}, UW={uw}")
    print(f"FIFO Depth={fifo_depth}, Alignment=0x{alignment_mask:X}")
    print(f"Expected duration: {timeout_s}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} AXI Write Splitter test PASSED")

    except Exception as e:
        print(f"✗ {test_level.upper()} AXI Write Splitter test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise