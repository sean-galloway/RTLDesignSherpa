"""
Test runner for AXI Error Monitor module

This module provides a pytest-based test runner for validating the axi_errmon_base
module with different parameter configurations.
"""

import os
import random
from itertools import product
import pytest
import cocotb

from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi_errmon.axi_errmon_base_tb import AXIErrorMonitorTB


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def axi_errmon_test(dut):
    """Main entry point for AXI Error Monitor tests"""
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
        unit_id=dut.UNIT_ID.value,
        agent_id=dut.AGENT_ID.value
    )

    # Start the clock
    await tb.start_clock('aclk', 10, 'ns')

    # Run the tests
    result = await tb.run_all_tests(test_type)

    # Check result
    if result:
        tb.log.info("TEST PASSED")
    else:
        tb.log.error("TEST FAILED")
        assert False, "Test failed"


def generate_params():
    """Generate test parameters"""
    # Initial parameter lists
    id_widths = [8]
    addr_widths = [32]
    unit_ids = [9]  # Default unit ID in RTL
    agent_ids = [99]  # Default agent ID in RTL
    is_read_options = [True, False]  # Both read and write modes
    is_axi_options = [True, False]  # Both AXI and AXI-Lite

    is_read_options = [True]
    is_axi_options = [True]
    test_levels = ['basic']  # Start with basic tests

    # For faster running tests, limit parameters
    if os.environ.get('QUICK_TEST', '1') == '1':
        # Focus on just a few configurations for quick testing
        is_axi_options = [True]
        is_read_options = [True]

    # For more extensive testing
    if os.environ.get('FULL_TEST', '0') == '1':
        test_levels = ['basic', 'medium', 'full']

    # Generate parameter combinations
    result = []
    result.extend(
        (id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level)
        for id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level in product(
            id_widths,
            addr_widths,
            unit_ids,
            agent_ids,
            is_read_options,
            is_axi_options,
            test_levels,
        )
    )
    return result


params = generate_params()

@pytest.mark.parametrize(
    "id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level",
    params
)
def test_axi_errmon(request, id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level):
    """Main test function for AXI Error Monitor module"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba': 'rtl/amba',
        }
    )

    # Set up all of the test names
    dut_name = "axi_errmon_base"
    toplevel = dut_name

    # Verilog sources needed for the test
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "includes/axi_errmon_types.sv"),  # Updated include path
        os.path.join(rtl_dict['rtl_cmn'],  "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_timer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_timeout.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi_errmon_reporter.sv"),
        os.path.join(rtl_dict['rtl_amba'], f"{dut_name}.sv")
    ]

    # Create a human-readable test identifier
    id_str = format(id_width, '02d')
    addr_str = format(addr_width, '02d')
    uid_str = format(unit_id, '02d')
    aid_str = format(agent_id, '02d')
    rd_str = "R" if is_read else "W"
    axi_str = "AXI" if is_axi else "AXIL"
    test_type_str = f"{test_level}"

    test_name_plus_params = f"test_{dut_name}_id{id_str}_a{addr_str}_uid{uid_str}_aid{aid_str}_{rd_str}_{axi_str}_{test_type_str}"
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
        'ID_WIDTH': str(id_width),
        'ADDR_WIDTH': str(addr_width),
        'UNIT_ID': str(unit_id),
        'AGENT_ID': str(agent_id),
        'IS_READ': '1' if is_read else '0',
        'IS_AXI': '1' if is_axi else '0',
        'MAX_TRANSACTIONS': '16'  # Default value
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
