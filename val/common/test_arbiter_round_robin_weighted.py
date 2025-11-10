# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_round_robin_weighted
# Purpose: Weighted Round Robin Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Weighted Round Robin Test Runner
Adapted from existing WRR test runner with robust testbench integration
"""

import os
import sys
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.common.arbiter_round_robin_weighted_tb import WeightedRoundRobinTB

@cocotb.test(timeout_time=20, timeout_unit="ms")  # Increased timeout for weight testing
async def arbiter_round_robin_weighted_test(dut):
    """comprehensive test for the weighted round-robin arbiter"""
    tb = WeightedRoundRobinTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'weighted round robin test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT (this also starts the monitor)
    await tb.reset_dut()

    try:
        # Phase 1: Basic functionality tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 1: Basic Functionality @ {time_ns}ns ===")
        await tb.test_grant_signals()
        await tb.test_threshold_operation()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 2: Basic weighted arbitration
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 2: Basic Weighted Arbitration @ {time_ns}ns ===")
        await tb.run_basic_arbitration_test(800)
        await tb.handle_test_transition_ack_cleanup()

        # Phase 3: Weight-specific tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 3: Weight-Specific Tests @ {time_ns}ns ===")
        await tb.test_weighted_fairness()
        await tb.test_weight_changes()
        await tb.test_single_client_saturation()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 4: Pattern and stress tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 4: Pattern and Stress Tests @ {time_ns}ns ===")
        await tb.test_walking_requests()
        await tb.test_block_arb()
        await tb.test_bursty_traffic_pattern()
        await tb.test_rapid_request_changes()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 5: ACK mode edge cases (if applicable)
        if tb.WAIT_GNT_ACK:
            time_ns = get_sim_time('ns')
            tb.log.info(f"=== Phase 5: ACK Mode Edge Cases @ {time_ns}ns ===")

            # Clear interface completely before ACK mode tests
            tb.clear_interface()
            await tb.wait_clocks('clk', 30)  # Longer stabilization for weight changes

            await tb.test_ack_mode_edge_cases()
            await tb.handle_test_transition_ack_cleanup()

        # Phase 6: Dynamic arbitration liveness
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 6: Dynamic Arbitration Liveness @ {time_ns}ns ===")
        await tb.test_dynamic_arbitration_liveness()
        await tb.handle_test_transition_ack_cleanup()

        # Phase 7: Final validation and reporting
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Phase 7: Final Validation @ {time_ns}ns ===")

        # Check for any final monitor errors
        tb.check_monitor_errors()

        # Generate comprehensive report with weight analysis
        report_success = tb.generate_final_report()

        if not report_success:
            raise AssertionError("Final weighted report validation failed")

        tb.log.info("=== ALL WEIGHTED TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"weighted test failed: {str(e)}")

        # debug info for weight-specific failures
        try:
            final_stats = tb.monitor.get_comprehensive_stats()
            tb.log.error(f"Final monitor stats: Total grants={final_stats.get('total_grants', 0)}, "
                        f"Fairness={final_stats.get('fairness_index', 0):.3f}")

            # Weight-specific debug info
            if 'weight_analysis' in final_stats:
                weight_analysis = final_stats['weight_analysis']
                tb.log.error(f"Weight changes tracked: {weight_analysis.get('weight_changes_tracked', 0)}")
                tb.log.error(f"Current weights: {tb.current_test_weights}")

            # Master statistics
            master_stats = tb.master.get_stats()
            tb.log.error(f"Master stats: {master_stats}")

            if tb.monitor_errors:
                tb.log.error(f"Monitor errors: {tb.monitor_errors}")

        except Exception as debug_e:
            tb.log.error(f"Error generating debug info: {debug_e}")

        raise
    finally:
        # Wait for any pending operations
        await tb.wait_clocks('clk', 20)

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4 clients, both ack modes)
    REG_LEVEL=FUNC: 6 tests (3 client counts, both ack modes) - default
    REG_LEVEL=FULL: 10 tests (all combinations)

    Returns:
        List of tuples: (clients, max_levels, wait_ack)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_configs = [
        ( 4,  8, 0),  # No wait for ack, 4 clients, max threshold 8
        ( 4,  8, 1),  # Wait for ack, 4 clients, max threshold 8
        ( 6,  8, 0),  # No wait for ack, 6 clients, max threshold 8
        ( 6,  8, 1),  # Wait for ack, 6 clients, max threshold 8
        ( 8, 16, 0),  # No wait for ack, 8 clients, max threshold 16
        ( 8, 16, 1),  # Wait for ack, 8 clients, max threshold 16
        (16, 16, 0),  # No wait for ack, 16 clients, max threshold 16
        (16, 16, 1),  # Wait for ack, 16 clients, max threshold 16
        (32, 16, 0),  # No wait for ack, 32 clients, max threshold 16
        (32, 16, 1),  # Wait for ack, 32 clients, max threshold 16
    ]

    if reg_level == 'GATE':
        # Quick smoke test: 4 clients, both modes
        return [all_configs[0], all_configs[1]]

    elif reg_level == 'FUNC':
        # Functional coverage: 4, 6, 8 clients, both modes
        return all_configs[0:6]

    else:  # FULL
        # Comprehensive: all configurations
        return all_configs

@pytest.mark.parametrize("clients, max_levels, wait_ack", generate_test_params())
def test_arbiter_round_robin_weighted(request, clients, max_levels, wait_ack):
    """Run the weighted round robin test with comprehensive coverage"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "arbiter_round_robin_weighted"
    toplevel = dut_name

    # Verilog sources for WEIGHTED ROUND ROBIN arbiter
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_round_robin_weighted.f'
    )

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    m_str = TBBase.format_dec(max_levels, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_c{c_str}_m{m_str}_w{w_str}_{reg_level}"

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
    # RTL parameters for WEIGHTED ROUND ROBIN
    parameters = {
        'CLIENTS': clients,
        'MAX_LEVELS': max_levels,
        'WAIT_GNT_ACK': wait_ack
        # MAX_LEVELS_WIDTH now computed automatically as localparam ($clog2(MAX_LEVELS))
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',  # Balanced logging for weight complexity
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000))
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
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
        # error reporting for weighted arbiters
        print(f"weighted round robin test failed: {str(e)}")
        print(f"Test configuration: {clients} clients, max_levels {max_levels}, ACK mode {wait_ack}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")

        # Weight-specific troubleshooting hints
        print("\nWeight-Specific Troubleshooting Hints:")
        print("- Check weight management FSM state transitions in waveforms")
        print("- Verify weight threshold packing/unpacking (max_thresh signal)")
        print("- Look for weight change timing relative to grant/ACK cycles")
        print("- Check credit exhaustion and replenishment patterns")
        print("- Verify weight compliance analysis results in logs")
        print("- Examine weight distribution windows for fairness violations")

        # Configuration-specific hints
        if max_levels > 16:
            print("- High MAX_LEVELS may cause longer test times")
        if clients > 16:
            print("- High client count increases arbitration complexity")
        if wait_ack == 1:
            print("- ACK mode with weights requires careful timing analysis")
            print("- Check for weight change conflicts with pending ACKs")

        raise  # Re-raise exception to indicate failure
