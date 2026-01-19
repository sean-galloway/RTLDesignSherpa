# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_round_robin
# Purpose: Test Runner for Round Robin Arbiter with New Clean ArbiterMaster
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test Runner for Round Robin Arbiter with New Clean ArbiterMaster
Clean implementation following existing test runner pattern with flex randomizer integration
"""

import os
import sys
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

# Import the adapted testbench and utilities

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.common.arbiter_round_robin_tb import ArbiterRoundRobinTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from conftest import get_coverage_compile_args

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

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4 clients, both ack modes)
    REG_LEVEL=FUNC: 6 tests (all clients, no-ack only) - default
    REG_LEVEL=FULL: 12 tests (all clients × all ack modes)

    Returns:
        List of tuples: (clients, wait_ack)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    client_counts = [4, 5, 6, 8, 16, 32]

    if reg_level == 'GATE':
        # Quick smoke test: 4 clients, both modes
        return [(4, 0), (4, 1)]

    elif reg_level == 'FUNC':
        # Functional coverage: all clients, no-ack only
        return [(c, 0) for c in client_counts]

    else:  # FULL
        # Comprehensive: all clients × all ack modes
        params = []
        for clients in client_counts:
            params.append((clients, 0))  # no ACK
            params.append((clients, 1))  # wait for ACK
        return params

@pytest.mark.parametrize("clients, wait_ack", generate_test_params())
def test_arbiter_round_robin(request, clients, wait_ack):
    """Run the round robin test with new clean ArbiterMaster"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "arbiter_round_robin"
    toplevel = dut_name

    # Verilog sources for ROUND ROBIN arbiter
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_round_robin.f'
    )

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_c{c_str}_w{w_str}_{reg_level}"

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
    # RTL parameters for ROUND ROBIN
    parameters = {'CLIENTS': clients, 'WAIT_GNT_ACK': wait_ack}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',  # Reduced log noise with new clean master
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())
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
