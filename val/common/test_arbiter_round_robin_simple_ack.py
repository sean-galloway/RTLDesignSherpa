# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_round_robin_simple_ack
# Purpose: Test Runner for Simple Round Robin Arbiter with grant/ack handshake
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-04

"""
Test Runner for Simple Round Robin Arbiter with grant/ack handshake
Grant is registered and held until the owning client returns grant_ack.
Follows the WRR test methodology: request-set scenarios in place of weight scenarios.
"""

import os
import sys
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

# Import the testbench and utilities

# Add repo root to path for CocoTBFramework imports
from TBClasses.common.arbiter_round_robin_simple_ack_tb import ArbiterRoundRobinSimpleAckTB
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args

@cocotb.test(timeout_time=20, timeout_unit="ms")
async def arbiter_round_robin_simple_ack_test(dut):
    """Comprehensive test for the simple round robin ACK arbiter"""
    tb = ArbiterRoundRobinSimpleAckTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'simple round robin ACK arbiter test starting with seed {seed}')

    # One call: starts the clock and drives the reset sequence.
    await tb.setup_clocks_and_reset()

    try:
        # Phase 1: Basic functionality tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 1: Basic Functionality @ {time_ns}ns ===")
        tb.log.info("=== Scenario ARB-01: Basic grant signals ===")
        await tb.test_grant_signals()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 2: Basic arbitration
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 2: Basic Arbitration @ {time_ns}ns ===")
        tb.log.info("=== Scenario ARB-02: Basic arbitration ===")
        await tb.run_basic_arbitration_test(400 * tb.LEVEL_MULT)
        await tb.handle_test_transition_ack_cleanup()

        # Phase 3: Request-set tests (the unweighted analogue of weight scenarios)
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 3: Request-Set Tests @ {time_ns}ns ===")
        tb.log.info("=== Scenario ARB-03: Request-set fairness ===")
        await tb.test_request_fairness()
        tb.log.info("=== Scenario ARB-04: Request-set changes ===")
        await tb.test_request_set_changes()
        tb.log.info("=== Scenario ARB-05: Single client saturation ===")
        await tb.test_single_client_saturation()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 4: Pattern and stress tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 4: Pattern and Stress Tests @ {time_ns}ns ===")
        tb.log.info("=== Scenario ARB-06: Walking requests ===")
        await tb.test_walking_requests()
        tb.log.info("=== Scenario ARB-07: Bursty traffic ===")
        await tb.test_bursty_traffic_pattern()
        tb.log.info("=== Scenario ARB-08: Rapid request changes ===")
        await tb.test_rapid_request_changes()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 5: Handshake directed tests (grant held until ACK)
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 5: Grant/ACK Handshake @ {time_ns}ns ===")
        tb.clear_interface()
        await tb.wait_clocks('clk', 30)
        tb.log.info("=== Scenario ARB-09: Grant held until owner ACK ===")
        await tb.test_grant_held_until_ack()
        tb.log.info("=== Scenario ARB-10: Back-to-back handoff on same-cycle ACK ===")
        await tb.test_back_to_back_handoff()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 6: Dynamic arbitration liveness
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 6: Dynamic Arbitration Liveness @ {time_ns}ns ===")
        tb.log.info("=== Scenario ARB-11: Dynamic arbitration liveness ===")
        await tb.test_dynamic_arbitration_liveness()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 7: Final validation and reporting
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 7: Final Validation @ {time_ns}ns ===")
        tb.check_monitor_errors()

        report_success = tb.generate_final_report()
        if not report_success:
            raise AssertionError("Final report validation failed")

        tb.log.info("=== ALL TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"simple round robin ACK arbiter test failed: {str(e)}")

        try:
            final_stats = tb.monitor.get_comprehensive_stats()
            tb.log.error(f"Final monitor stats: Total grants={final_stats.get('total_grants', 0)}, "
                        f"Fairness={final_stats.get('fairness_index', 0):.3f}")
            tb.log.error(f"Master stats: {tb.master.get_stats()}")
            if tb.monitor_errors:
                tb.log.error(f"Monitor errors: {tb.monitor_errors}")
        except Exception as debug_e:
            tb.log.error(f"Error generating debug info: {debug_e}")

        raise

    finally:
        # Gracefully stop master
        try:
            if tb.master.active:
                await tb.master.shutdown()
        except Exception as e:
            tb.log.warning(f"Error stopping master: {e}")

        # Wait for any pending operations
        await tb.wait_clocks('clk', 20)

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4, 8 clients)
    REG_LEVEL=FUNC: 7 tests (all client counts) - default
    REG_LEVEL=FULL: 7 tests (same as FUNC)

    Returns:
        List of client counts
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_clients = [2, 3, 4, 5, 6, 8, 16]

    if reg_level == 'GATE':
        # Quick smoke test: power-of-2 sizes
        return [4, 8]

    else:  # FUNC or FULL (same for this test)
        # Full coverage: all client counts
        return all_clients

@pytest.mark.parametrize("clients", generate_test_params())
def test_arbiter_round_robin_simple_ack(request, clients):
    """Run the simple round robin ACK test"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "arbiter_round_robin_simple_ack"
    toplevel = dut_name

    # Verilog sources for SIMPLE ROUND ROBIN ACK arbiter
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='arbiter_round_robin_simple_ack'
    )

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_c{c_str}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    # Make sim_build directory
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters for SIMPLE ROUND ROBIN ACK (only N parameter)
    parameters = {'N': clients}

    # Environment variables
    extra_env = {
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', reg_level.lower()),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this
    # the run produces no coverage.dat at all and `make coverage-report`
    # silently reports 0.0% from 0 merged files.
    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

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
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
    except Exception as e:
        print(f"Simple round robin ACK test failed: {str(e)}")
        print(f"Test configuration: {clients} clients")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")

        print("\nTroubleshooting hints for simple ACK arbiter:")
        print("- Check that arbiter_round_robin_simple_ack.sv is present")
        print("- Verify parameter N is correctly passed")
        print("- Look for signal interface compatibility issues")
        print("- Check testbench initialization")

        raise  # Re-raise exception to indicate failure