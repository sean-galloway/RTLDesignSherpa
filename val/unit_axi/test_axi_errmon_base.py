"""
Test runner for AXI Error Monitor Base module

This module provides a pytest-based test runner for validating the axi_errmon_base
module with different parameter configurations.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb.triggers import Timer

from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi_errmon.axi_errmon_base_tb import AXIErrorMonitorTB


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def axi_errmon_base_test(dut):
    """Main entry point for AXI Error Monitor Base tests"""
    # Get test parameters from environment
    test_type = os.environ.get('TEST_TYPE', 'basic')  # basic, medium, full
    is_read = os.environ.get('IS_READ', '1') == '1'
    is_axi = os.environ.get('IS_AXI', '1') == '1'

    # Create the testbench
    tb = AXIErrorMonitorTB(
        dut=dut,
        addr_width=dut.ADDR_WIDTH.value,
        id_width=dut.ID_WIDTH.value,
        is_read=dut.IS_READ.value == 1,
        is_axi=dut.IS_AXI.value == 1,
        timer_width=dut.TIMER_WIDTH.value,  # Added timer width parameter
        timeout_addr=dut.TIMEOUT_ADDR.value,
        timeout_data=dut.TIMEOUT_DATA.value,
        timeout_resp=dut.TIMEOUT_RESP.value,
        error_fifo_depth=dut.ERROR_FIFO_DEPTH.value,
        addr_fifo_depth=dut.ADDR_FIFO_DEPTH.value,
        channels=dut.CHANNELS.value
    )

    # Start the clock
    await tb.start_clock('aclk', 10, 'ns')

    # Run the tests
    result = await tb.run_all_tests(test_level=test_type)

    # Check result
    if result:
        tb.log.info("TEST PASSED")
    else:
        tb.log.error("TEST FAILED")
        assert False, "Test failed"


def generate_params():
    """Generate test parameters"""
    channels_list = [1, 4, 16, 32]
    id_widths = [8]
    addr_widths = [32]
    timer_widths = [16, 20]  # Added timer width options
    error_fifo_depths = [4]
    addr_fifo_depths = [4]
    timeout_values = [100]
    is_read_options = [True, False]
    is_axi_options = [True]
    test_levels = ['basic', 'medium', 'full']

    is_read_options = [True, False]
    timer_widths = [16]  # Added timer width options
    # channels_list = [4]
    test_levels = ['full']

    # For faster running tests, limit parameters
    if os.environ.get('QUICK_TEST', '0') == '1':
        channels_list = [1, 4]
        timer_widths = [16]
        test_levels = ['basic']

    # For debug-focused testing
    if os.environ.get('DEBUG_TEST', '0') == '1':
        channels_list = [4]
        timer_widths = [20]
        test_levels = ['full']

    return [
        (
            channels,
            id_width,
            addr_width,
            timer_width,  # Added to parameter list
            error_fifo_depth,
            addr_fifo_depth,
            timeout,
            is_read,
            is_axi,
            test_level,
        )
        for channels, id_width, addr_width, timer_width, error_fifo_depth, addr_fifo_depth, timeout, is_read, is_axi, test_level in product(
            channels_list,
            id_widths,
            addr_widths,
            timer_widths,
            error_fifo_depths,
            addr_fifo_depths,
            timeout_values,
            is_read_options,
            is_axi_options,
            test_levels,
        )
        if channels <= 16 or test_level != 'full'
    ]

params = generate_params()

@pytest.mark.parametrize(
    "channels, id_width, addr_width, timer_width, error_fifo_depth, addr_fifo_depth, timeout, is_read, is_axi, test_level",
    params
)
def test_axi_errmon_base(request, channels, id_width, addr_width, timer_width, error_fifo_depth,
                            addr_fifo_depth, timeout, is_read, is_axi, test_level):
    """Main test function for AXI Error Monitor Base module"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_axi': 'rtl/axi',
        }
    )

    # Set up all of the test names
    dut_name = "axi_errmon_base"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human-readable test identifier
    timeout = timeout * (channels//4) if channels  > 4 else timeout
    ch_str = format(channels, '02d')
    id_str = format(id_width, '02d')
    addr_str = format(addr_width, '02d')
    tw_str = format(timer_width, '02d')  # Added timer width to identifier
    efd_str = format(error_fifo_depth, '02d')
    afd_str = format(addr_fifo_depth, '02d')
    to_str = format(timeout, '04d')
    rd_str = "R" if is_read else "W"
    axi_str = "AXI" if is_axi else "AXIL"
    test_type_str = f"{test_level}"

    test_name_plus_params = f"test_{dut_name}_ch{ch_str}_id{id_str}_a{addr_str}_tw{tw_str}_efd{efd_str}_afd{afd_str}_to{to_str}_{rd_str}_{axi_str}_{test_type_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {
        'CHANNELS': str(channels),
        'ID_WIDTH': str(id_width),
        'ADDR_WIDTH': str(addr_width),
        'TIMER_WIDTH': str(timer_width),  # Added timer width parameter
        'ERROR_FIFO_DEPTH': str(error_fifo_depth),
        'ADDR_FIFO_DEPTH': str(addr_fifo_depth),
        'TIMEOUT_ADDR': str(timeout),
        'TIMEOUT_DATA': str(timeout),
        'TIMEOUT_RESP': str(timeout),
        'IS_READ': '1' if is_read else '0',
        'IS_AXI': '1' if is_axi else '0',
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_TYPE': test_level,
        'IS_READ': '1' if is_read else '0',
        'IS_AXI': '1' if is_axi else '0',
        'TIMER_WIDTH': str(timer_width),  # Added environment variable
    }

    compile_args = [
            "--trace-fst",
            "--trace-structs",
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace-fst",  # Tell Verilator to use FST
            "--trace-structs",
            "--trace-depth", "99",
    ]

    plusargs = [
            "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        from cocotb_test.simulator import run
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
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
