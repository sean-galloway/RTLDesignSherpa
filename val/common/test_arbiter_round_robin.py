"""
Test Runner for Round Robin Arbiter with New Clean ArbiterMaster
Clean implementation following existing test runner pattern with flex randomizer integration
"""

import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

# Import the adapted testbench and utilities
from CocoTBFramework.tbclasses.common.arbiter_round_robin_tb import ArbiterRoundRobinTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

@cocotb.test(timeout_time=20, timeout_unit="ms")
async def arbiter_round_robin_test(dut):
    """Comprehensive test for round-robin arbiter with new clean ArbiterMaster"""
    tb = ArbiterRoundRobinTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Round robin comprehensive test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT (this starts both master and monitor)
    await tb.reset_dut()

    try:
        # Phase 1: Basic functionality tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting grant signal test @ {time_ns}ns ===")
        await tb.test_grant_signals()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 2: Basic arbitration test with flex randomizer patterns
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting basic arbitration test @ {time_ns}ns ===")
        await tb.run_basic_arbitration_test(800)
        await tb.handle_test_transition_ack_cleanup()

        # Phase 3: Advanced pattern tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting advanced pattern tests @ {time_ns}ns ===")
        await tb.test_walking_requests()
        await tb.test_block_arb()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 4: Traffic pattern tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting traffic pattern tests @ {time_ns}ns ===")
        await tb.test_bursty_traffic_pattern()
        await tb.test_single_client_saturation()
        await tb.test_rapid_request_changes()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 5: Comprehensive fairness test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting fairness test @ {time_ns}ns ===")
        await tb.test_fairness()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 6: Final validation and reporting
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Final validation @ {time_ns}ns ===")

        # Check for any monitor errors
        tb.check_monitor_errors()

        # Generate comprehensive report
        report_success = tb.generate_final_report()

        if not report_success:
            raise AssertionError("Final report validation failed")

        tb.log.info("=== ALL COMPREHENSIVE TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"Comprehensive test failed: {str(e)}")

        # debug info on failure
        try:
            # Monitor statistics
            final_stats = tb.monitor.get_comprehensive_stats()
            tb.log.error(f"Final monitor stats: Total grants={final_stats.get('total_grants', 0)}, "
                        f"Fairness={final_stats.get('fairness_index', 0):.3f}")

            # Master statistics
            master_stats = tb.master.get_stats()
            tb.log.error(f"Master stats: {master_stats}")

            if tb.monitor_errors:
                tb.log.error(f"Monitor errors: {tb.monitor_errors}")

        except Exception as debug_e:
            tb.log.error(f"Error generating debug info: {debug_e}")

        raise

    finally:
        # Gracefully stop master and monitor
        try:
            if tb.master.active:
                await tb.master.shutdown()
                tb.log.info("Master stopped gracefully")
        except Exception as e:
            tb.log.warning(f"Error stopping master: {e}")

        # Wait for any pending operations
        await tb.wait_clocks('clk', 10)

@pytest.mark.parametrize("clients, wait_ack", [
    ( 4, 0),   #  4 clients, no ACK mode
    ( 5, 0),   #  5 clients, no ACK mode
    ( 6, 0),   #  6 clients, no ACK mode
    ( 8, 0),   #  8 clients, no ACK mode
    (16, 0),   # 16 clients, no ACK mode
    (32, 0),   # 32 clients, no ACK mode
    ( 4, 1),   #  4 clients, ACK mode
    ( 5, 1),   #  5 clients, ACK mode
    ( 6, 1),   #  6 clients, ACK mode
    ( 8, 1),   #  8 clients, ACK mode
    (16, 1),   # 16 clients, ACK mode
    (32, 1),   # 32 clients, ACK mode
])
def test_arbiter_round_robin(request, clients, wait_ack):
    """Run the round robin test with new clean ArbiterMaster"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "arbiter_round_robin"
    toplevel = dut_name

    # Verilog sources for ROUND ROBIN arbiter
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_priority_encoder.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    test_name_plus_params = f"test_{dut_name}_c{c_str}_w{w_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters for ROUND ROBIN
    parameters = {'CLIENTS': clients, 'WAIT_GNT_ACK': wait_ack}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',  # Reduced log noise with new clean master
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
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
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # error reporting for new master
        print(f"Round robin test with clean ArbiterMaster failed: {str(e)}")
        print(f"Test configuration: {clients} clients, ACK mode {wait_ack}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")

        # Troubleshooting hints specific to new architecture
        print("\nTroubleshooting hints for new clean ArbiterMaster:")
        print("- Check master startup and initialization in logs")
        print("- Verify flex randomizer profile loading")
        print("- Look for signal interface compatibility issues")
        print("- Check ACK protocol handling in new master")
        print("- Verify clean shutdown without cleanup hacks")

        raise  # Re-raise exception to indicate failure
