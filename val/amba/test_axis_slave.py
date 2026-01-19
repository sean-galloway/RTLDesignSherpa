# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axis_slave
# Purpose: AXIS Slave Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Slave Test Runner

Test runner for the axis_slave.sv module using the CocoTB framework.
Tests various AXIS configurations and validates stream transactions.

The axis_slave converts standard AXIS slave interface to FUB-side AXIS signals
through a skid buffer mechanism.

Based on the AXI4 test runner pattern but adapted for AXIS stream protocol.
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

# Import the testbench
from CocoTBFramework.tbclasses.axis4.axis_slave_tb import AXISSlaveTB


@cocotb.test(timeout_time=15, timeout_unit="ms")
async def axis_slave_test(dut):
    """AXIS slave test using the AXIS framework components"""

    # Create testbench instance
    tb = AXISSlaveTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIS slave test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Start clock and reset sequence
    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    # Setup test components
    tb.setup_components()
    await tb.wait_clocks('aclk', 20)

    try:
        # Phase 1: Basic functionality tests
        tb.log.info("=== Phase 1: Basic Transfer Test ===")
        if test_level in ['basic', 'medium', 'full']:
            await tb.run_basic_transfer_test(num_packets=10)

        # Phase 2: Frame transfer tests
        tb.log.info("=== Phase 2: Frame Transfer Test ===")
        if test_level in ['medium', 'full']:
            await tb.run_frame_transfer_test(num_frames=5, frame_size=4)

        # Phase 3: Backpressure tests
        tb.log.info("=== Phase 3: Backpressure Test ===")
        if test_level in ['medium', 'full']:
            await tb.run_backpressure_test(num_packets=20)

        # Phase 4: Ready signal tests
        tb.log.info("=== Phase 4: Ready Signal Test ===")
        if test_level == 'full':
            await tb.run_ready_deassert_test()

        # Phase 5: Skid buffer stress tests
        tb.log.info("=== Phase 5: Skid Buffer Stress Test ===")
        if test_level == 'full':
            await tb.run_skid_buffer_stress_test()

        # Phase 6: Busy signal tests
        tb.log.info("=== Phase 6: Busy Signal Test ===")
        if test_level == 'full':
            await tb.run_busy_signal_test()

        # Phase 7: Data integrity tests
        tb.log.info("=== Phase 7: Data Integrity Test ===")
        if test_level == 'full':
            await tb.run_data_integrity_test(num_packets=30)

        # Wait for completion
        await tb.wait_clocks('aclk', 50)

        # Generate final report
        report_success = tb.generate_final_report()

        if not report_success:
            raise AssertionError("Final report validation failed")

        tb.log.info("=== ALL AXIS SLAVE TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"AXIS slave test failed: {str(e)}")
        raise

    except Exception as e:
        tb.log.error(f"AXIS slave test error: {str(e)}")
        raise


@pytest.mark.parametrize("skid_depth, data_width, id_width, dest_width, user_width", [
    # Basic configurations
    (4, 32, 8, 4, 1),    # Standard configuration
    (2, 32, 8, 4, 1),    # Minimal skid depth
    (8, 32, 8, 4, 1),    # Larger skid depth

    # Different data widths
    (4, 64, 8, 4, 1),    # 64-bit data
    (4, 128, 8, 4, 1),   # 128-bit data
    (4, 256, 8, 4, 1),   # 256-bit data

    # Minimal sideband signals
    (4, 32, 0, 0, 0),    # No ID, DEST, USER
    (4, 32, 4, 0, 0),    # Only ID
    (4, 32, 0, 4, 0),    # Only DEST
    (4, 32, 0, 0, 1),    # Only USER

    # Various ID widths
    (4, 32, 4, 4, 1),    # 4-bit ID
    (4, 32, 12, 4, 1),   # 12-bit ID

    # Various DEST widths
    (4, 32, 8, 8, 1),    # 8-bit DEST

    # Various USER widths
    (4, 32, 8, 4, 8),    # 8-bit USER
])
def test_axis_slave(request, skid_depth, data_width, id_width, dest_width, user_width):
    """Run the AXIS slave test with different configurations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axis_slave"
    toplevel = dut_name

    # Verilog sources for AXIS slave
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi", "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axis4", f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    sd_str = TBBase.format_dec(skid_depth, 1)
    dw_str = TBBase.format_dec(data_width, 3)
    iw_str = TBBase.format_dec(id_width, 2)
    destw_str = TBBase.format_dec(dest_width, 1)
    uw_str = TBBase.format_dec(user_width, 1)

    test_name_plus_params = f"test_{worker_id}_{dut_name}_sd{sd_str}_dw{dw_str}_iw{iw_str}_destw{destw_str}_uw{uw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    # RTL parameters for AXIS slave
    parameters = {
        'SKID_DEPTH': skid_depth,
        'AXIS_DATA_WIDTH': data_width,
        'AXIS_ID_WIDTH': id_width,
        'AXIS_DEST_WIDTH': dest_width,
        'AXIS_USER_WIDTH': user_width
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic')
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
        "--trace",  # Tell Verilator to use VCD
        
        "--trace-depth", "99",
    ]

    plusargs = [
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
        print(f"AXIS slave test failed: {str(e)}")
        print(f"Test configuration: SKID_DEPTH={skid_depth}, DATA_WIDTH={data_width}")
        print(f"ID_WIDTH={id_width}, DEST_WIDTH={dest_width}, USER_WIDTH={user_width}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")

        print("\nTroubleshooting hints for AXIS slave:")
        print("- Check that gaxi_skid_buffer.sv is present")
        print("- Verify AXIS signal connectivity")
        print("- Look for signal interface compatibility issues")
        print("- Check ready signal propagation")
        print("- Check busy signal behavior")
        print("- Verify skid buffer depth configuration")

        raise  # Re-raise exception to indicate failure
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Run the AXIS slave test with different configurations"""

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axis_slave"
    toplevel = dut_name

    # Verilog sources for AXIS slave
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "gaxi", "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axis4", f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    sd_str = TBBase.format_dec(skid_depth, 1)
    dw_str = TBBase.format_dec(data_width, 3)
    iw_str = TBBase.format_dec(id_width, 2)
    destw_str = TBBase.format_dec(dest_width, 1)
    uw_str = TBBase.format_dec(user_width, 1)

    test_name_plus_params = f"test_{worker_id}_{dut_name}_sd{sd_str}_dw{dw_str}_iw{iw_str}_destw{destw_str}_uw{uw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    # RTL parameters for AXIS slave
    parameters = {
        'SKID_DEPTH': skid_depth,
        'AXIS_DATA_WIDTH': data_width,
        'AXIS_ID_WIDTH': id_width,
        'AXIS_DEST_WIDTH': dest_width,
        'AXIS_USER_WIDTH': user_width
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic')
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
        "--trace",  # Tell Verilator to use VCD
        
        "--trace-depth", "99",
    ]

    plusargs = [
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
        print(f"AXIS slave test failed: {str(e)}")
        print(f"Test configuration: SKID_DEPTH={skid_depth}, DATA_WIDTH={data_width}")
        print(f"ID_WIDTH={id_width}, DEST_WIDTH={dest_width}, USER_WIDTH={user_width}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")

        print("\nTroubleshooting hints for AXIS slave:")
        print("- Check that gaxi_skid_buffer.sv is present")
        print("- Verify AXIS signal connectivity")
        print("- Look for signal interface compatibility issues")
        print("- Check ready signal propagation")
        print("- Check busy signal behavior")
        print("- Verify skid buffer depth configuration")

        raise  # Re-raise exception to indicate failure