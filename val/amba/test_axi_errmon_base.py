"""
Test runner for AXI Error Monitor module

This module provides a pytest-based test runner for validating the axi_errmon_base
module with different parameter configurations.

Updated to support comprehensive parameter testing and configuration control.
"""

import os
import random
from itertools import product
import pytest
import cocotb

from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.axi_errmon.axi_errmon_base_tb import AXIErrorMonitorTB


# Define test parameter sets for systematic testing
TIMER_CONFIG_SETS = {
    'basic': {
        'freq_sel': 4,
        'addr_cnt': 1,
        'data_cnt': 5,
        'resp_cnt': 6,
        'description': 'Basic timing - fast timeouts for quick testing'
    },
    'moderate': {
        'freq_sel': 3,
        'addr_cnt': 3,
        'data_cnt': 8,
        'resp_cnt': 10,
        'description': 'Moderate timing - balanced timeouts'
    },
    'slow': {
        'freq_sel': 2,
        'addr_cnt': 5,
        'data_cnt': 12,
        'resp_cnt': 15,
        'description': 'Slow timing - longer timeouts'
    },
    'aggressive': {
        'freq_sel': 5,
        'addr_cnt': 1,
        'data_cnt': 2,
        'resp_cnt': 3,
        'description': 'Aggressive timing - very fast timeouts'
    }
}

PACKET_ENABLE_SETS = {
    'error_only': {
        'error_enable': True,
        'compl_enable': False,
        'threshold_enable': False,
        'timeout_enable': False,
        'perf_enable': False,
        'debug_enable': False,
        'description': 'Only error packets enabled - basic error testing'
    },
    'error_timeout': {
        'error_enable': True,
        'compl_enable': False,
        'threshold_enable': False,
        'timeout_enable': True,
        'perf_enable': False,
        'debug_enable': False,
        'description': 'Error and timeout packets - enhanced error testing'
    },
    'basic_events': {
        'error_enable': True,
        'compl_enable': True,
        'threshold_enable': False,
        'timeout_enable': True,
        'perf_enable': False,
        'debug_enable': False,
        'description': 'Basic event set - errors, timeouts, completions'
    },
    'all_events': {
        'error_enable': True,
        'compl_enable': True,
        'threshold_enable': True,
        'timeout_enable': True,
        'perf_enable': True,
        'debug_enable': True,
        'description': 'All event types enabled - comprehensive testing'
    }
}

@cocotb.test(timeout_time=5, timeout_unit="ms")  # Increased timeout for parameter testing
async def axi_errmon_test(dut):
    """Main entry point for AXI Error Monitor tests"""
    # Get test parameters from environment
    test_type = os.environ.get('TEST_TYPE', 'basic')
    is_read = os.environ.get('IS_READ', '1') == '1'
    is_axi = os.environ.get('IS_AXI', '1') == '1'

    # NEW: Get timer and packet configuration sets
    timer_config_name = os.environ.get('TIMER_CONFIG', 'basic')
    packet_enable_name = os.environ.get('PACKET_ENABLE', 'error_only')

    # Get configuration sets
    timer_config = TIMER_CONFIG_SETS.get(timer_config_name, TIMER_CONFIG_SETS['basic'])
    packet_enable = PACKET_ENABLE_SETS.get(packet_enable_name, PACKET_ENABLE_SETS['error_only'])

    # Create the testbench with enhanced configuration
    tb = AXIErrorMonitorTB(
        dut=dut,
        addr_width=dut.ADDR_WIDTH.value,
        id_width=dut.ID_WIDTH.value,
        is_read=dut.IS_READ.value == 1,
        is_axi=dut.IS_AXI.value == 1,
        unit_id=dut.UNIT_ID.value,
        agent_id=dut.AGENT_ID.value,
        # NEW: Pass timer configuration
        timer_config=timer_config,
        packet_enable_config=packet_enable
    )

    # Start the clock
    await tb.start_clock('aclk', 10, 'ns')

    # NEW: Configure RTL with the specified parameters
    await tb.configure_rtl_parameters()

    # Run the tests
    result = await tb.run_all_tests(test_type)

    # Check result
    if result:
        tb.log.info("TEST PASSED")
    else:
        tb.log.error("TEST FAILED")
        assert False, "Test failed"


def generate_params():
    """Generate test parameters with enhanced configuration control"""
    # Basic RTL parameters
    id_widths = [8]
    addr_widths = [32]
    unit_ids = [5]
    agent_ids = [0xC3]
    is_read_options = [True, False]
    is_axi_options = [True, False]

    # Test levels
    test_levels = ['basic']

    # NEW: Timer and packet configuration sets
    timer_configs = ['basic']  # Start with basic, expand later
    packet_enables = ['error_only']  # Start with error-only, expand later

    # For faster initial testing, limit parameters
    if os.environ.get('QUICK_TEST', '1') == '1':
        is_axi_options = [True]
        is_read_options = [True]
        timer_configs = ['basic']
        packet_enables = ['error_only']

    # For more extensive testing
    if os.environ.get('FULL_TEST', '0') == '1':
        test_levels = ['basic', 'medium', 'full']
        timer_configs = ['basic', 'moderate', 'slow', 'aggressive']
        packet_enables = ['error_only', 'error_timeout', 'basic_events']

    # For comprehensive testing
    if os.environ.get('COMPREHENSIVE_TEST', '0') == '1':
        test_levels = ['basic', 'medium', 'full']
        timer_configs = list(TIMER_CONFIG_SETS.keys())
        packet_enables = list(PACKET_ENABLE_SETS.keys())

    # Generate parameter combinations
    result = []
    result.extend(
        (id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level, timer_config, packet_enable)
        for id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level, timer_config, packet_enable in product(
            id_widths,
            addr_widths,
            unit_ids,
            agent_ids,
            is_read_options,
            is_axi_options,
            test_levels,
            timer_configs,
            packet_enables
        )
    )
    return result


params = generate_params()

@pytest.mark.parametrize(
    "id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level, timer_config, packet_enable",
    params
)
def test_axi_errmon(request, id_width, addr_width, unit_id, agent_id, is_read, is_axi, test_level, timer_config, packet_enable):
    """Main test function for AXI Error Monitor module with enhanced parameter control"""
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
        os.path.join(rtl_dict['rtl_amba'], "includes/axi_errmon_types.sv"),
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

    # Create a human-readable test identifier with enhanced naming
    id_str = format(id_width, '02d')
    addr_str = format(addr_width, '02d')
    uid_str = format(unit_id, '02d')
    aid_str = format(agent_id, '02d')
    rd_str = "R" if is_read else "W"
    axi_str = "AXI" if is_axi else "AXIL"
    test_type_str = f"{test_level}"
    timer_str = timer_config
    packet_str = packet_enable

    test_name_plus_params = f"test_{dut_name}_id{id_str}_a{addr_str}_uid{uid_str}_aid{aid_str}_{rd_str}_{axi_str}_{test_type_str}_{timer_str}_{packet_str}"
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

    # Environment variables with enhanced configuration
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_TYPE': test_level,
        'IS_READ': '1' if is_read else '0',
        'IS_AXI': '1' if is_axi else '0',
        # NEW: Enhanced configuration environment variables
        'TIMER_CONFIG': timer_config,
        'PACKET_ENABLE': packet_enable,
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",
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
            python_search=[tests_dir],
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
        print(f"Timer config: {timer_config} - {TIMER_CONFIG_SETS[timer_config]['description']}")
        print(f"Packet enable: {packet_enable} - {PACKET_ENABLE_SETS[packet_enable]['description']}")
        raise
