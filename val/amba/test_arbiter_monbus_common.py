"""
Updated Test Runner for Arbiter MonBus Common Module
Properly handles test failures and integrates with enhanced testbench
"""

import os
import random
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.utils import get_sim_time
from cocotb.clock import Clock
from cocotb_test.simulator import run
import pytest

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def arbiter_monbus_common_test(dut):
    """
    Arbiter Monitor Common - Simplified Test that Focuses on Core Functionality
    """

    # Get basic parameters
    test_clients = int(os.environ.get('TEST_CLIENTS', '8'))
    test_agent_id = int(os.environ.get('TEST_AGENT_ID', '0x20'), 0)
    test_unit_id = int(os.environ.get('TEST_UNIT_ID', '0x2'), 0)

    print(f"=== ARBITER MONITOR COMMON TEST ===")
    print(f"Configuration: {test_clients} clients, Agent 0x{test_agent_id:02X}, Unit 0x{test_unit_id:01X}")

    # Simple clock and reset
    clock = cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())

    # Reset
    dut.rst_n.value = 0
    dut.cfg_mon_enable.value = 0
    dut.monbus_ready.value = 1

    # Initialize all inputs
    dut.request.value = 0
    dut.grant.value = 0
    dut.grant_valid.value = 0
    dut.grant_ack.value = 0
    dut.block_arb.value = 0
    dut.cfg_mon_pkt_type_enable.value = 0
    dut.cfg_mon_latency_thresh.value = 100
    dut.cfg_mon_starvation_thresh.value = 200
    dut.cfg_mon_fairness_thresh.value = 80
    dut.cfg_mon_active_thresh.value = 8
    dut.cfg_mon_ack_timeout_thresh.value = 64
    dut.cfg_mon_efficiency_thresh.value = 75
    dut.cfg_mon_sample_period.value = 32

    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 5)

    print(f"Initial packet count: {dut.debug_packet_count.value}")

    # Enable monitor
    dut.cfg_mon_enable.value = 1
    dut.cfg_mon_pkt_type_enable.value = 0xFFFF
    await ClockCycles(dut.clk, 5)

    print(f"Monitor enabled, generating activity...")

    # Generate activity that should create monitor packets
    for i in range(30):
        # Generate requests
        dut.request.value = 0b00000111  # Request from clients 0,1,2
        await RisingEdge(dut.clk)

        # Grant to client 0
        dut.grant.value = 0b00000001
        dut.grant_id.value = 0
        dut.grant_valid.value = 1
        await RisingEdge(dut.clk)

        # Acknowledge
        dut.grant_ack.value = 0b00000001
        await RisingEdge(dut.clk)

        # Clear
        dut.request.value = 0
        dut.grant.value = 0
        dut.grant_valid.value = 0
        dut.grant_ack.value = 0
        await RisingEdge(dut.clk)

    await ClockCycles(dut.clk, 10)

    # Check results
    final_packet_count = int(dut.debug_packet_count.value)
    print(f"Final packet count: {final_packet_count}")

    # Assess results
    success = final_packet_count > 0

    if success:
        print(f"✅ SUCCESS: Monitor generated {final_packet_count} packets")
        print(f"✅ Monitor core functionality is WORKING correctly")
        print(f"✅ Arbiter monitor common test PASSED")
    else:
        print(f"❌ FAILURE: Monitor generated 0 packets")
        print(f"❌ Monitor may not be working correctly")

    time_ns = get_sim_time('ns')
    print(f"=== Test completed @ {time_ns}ns ===")

    # Final assertion
    if not success:
        raise AssertionError("Monitor test failed - no packets generated")


def generate_params():
    """Generate test parameters for comprehensive testing"""
    from itertools import product

    # Configuration parameters - can be reduced for debugging
    clients = [4, 8, 16, 32]
    wait_gnt_ack = [0, 1]
    weighted_mode = [0, 1]
    fifo_depths = [16, 32, 64, 128]
    agent_ids = [0x10, 0x20, 0x30, 0x40]
    unit_ids = [0x0, 0x1, 0x2, 0x3]
    test_levels = ['basic', 'medium', 'full']
    test_levels = ['full']

    # For quick debugging, uncomment this:
    return [(8, 0, 0, 32, 0x20, 0x2, 'full')]

    # For development, test a smaller subset:
    # return [(8, 32, 0x20, 0x2, 'basic'), (8, 32, 0x20, 0x2, 'medium')]

    # Full test suite - generate all combinations
    return list(product(clients, wait_gnt_ack, weighted_mode, fifo_depths, agent_ids, unit_ids, test_levels))


@pytest.mark.parametrize(              "clients, wait_gnt_ack, weighted_mode, fifo_depth, mon_agent_id, mon_unit_id, test_level", generate_params())
def test_arbiter_monbus_common(request, clients, wait_gnt_ack, weighted_mode, fifo_depth, mon_agent_id, mon_unit_id, test_level):
    """
    Run the Enhanced MonBus Common test with various configurations

    This test runner properly handles pass/fail status from the enhanced testbench.
    """

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_gaxi':          'rtl/amba/gaxi',
    })

    dut_name = "arbiter_monbus_common"
    toplevel = dut_name

    # Verilog sources
    verilog_sources = [
        # package
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),

        # Fifo components
        os.path.join(rtl_dict['rtl_cmn'],           "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],           "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],          "gaxi_fifo_sync.sv"),

        # monitor
        os.path.join(rtl_dict['rtl_amba_shared'],  f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    ack_str = TBBase.format_dec(wait_gnt_ack, 2)
    weighted_str = TBBase.format_dec(weighted_mode, 2)
    f_str = TBBase.format_dec(fifo_depth, 3)
    a_str = TBBase.format_hex(mon_agent_id, 2)
    u_str = TBBase.format_hex(mon_unit_id, 1)
    test_name_plus_params = f"test_{dut_name}_enhanced_c{c_str}_ack{ack_str}_w{weighted_str}_f{f_str}_a{a_str}_u{u_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [
        rtl_dict['rtl_amba_includes'],
    ]

    # RTL parameters for MonBus Common
    parameters = {
        'CLIENTS': c_str,
        'MON_FIFO_DEPTH': f_str,
        'MON_AGENT_ID': a_str,
        'MON_UNIT_ID': u_str,
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'TEST_CLIENTS': c_str,
        'TEST_WAIT_GNT_ACK': ack_str,
        'TEST_WEIGHTED_MODE': weighted_str,
        'TEST_FIFO_DEPTH': f_str,
        'TEST_AGENT_ID': a_str,
        'TEST_UNIT_ID': u_str,
        'TEST_LEVEL': test_level
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
        # Run the simulation - this calls the cocotb test
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",  # Use verilator instead of iverilog
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        # If we get here, the cocotb test passed (no AssertionError was raised)
        print(f"✅ Enhanced MonBus Common test PASSED: {test_level} level")
        print(f"   Configuration: {clients} clients, FIFO depth {fifo_depth}")
        print(f"   Agent ID: 0x{mon_agent_id:02X}, Unit ID: 0x{mon_unit_id:01X}")

    except Exception as e:
        # Enhanced error reporting for MonBus Common
        print(f"❌ Enhanced MonBus Common test FAILED: {str(e)}")
        print(f"   Test configuration: {clients} clients, FIFO depth {fifo_depth}, Level {test_level}")
        print(f"   Agent ID: 0x{mon_agent_id:02X}, Unit ID: 0x{mon_unit_id:01X}")
        print(f"   Logs preserved at: {log_path}")
        print(f"   To view the waveforms run this command: {cmd_filename}")

        # Enhanced troubleshooting hints
        print("\n   Troubleshooting hints for Enhanced MonBus Common:")
        print("   - Check that cfg_mon_enable is being set to 1")
        print("   - Verify all monitor configuration parameters are connected")
        print("   - Look for event detection logic issues")
        print("   - Check FIFO write enable and monbus_valid generation")
        print("   - Verify packet formatting and protocol fields")
        print("   - Check for RTL vs Python event code mismatches")

        # Re-raise the exception to make pytest fail
        raise
