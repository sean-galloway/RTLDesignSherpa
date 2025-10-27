# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_round_robin_simple
# Purpose: Test Runner for Simple Round Robin Arbiter
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test Runner for Simple Round Robin Arbiter
Simplified implementation without ACK protocol and block_arb functionality
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
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.common.arbiter_round_robin_simple_tb import ArbiterRoundRobinSimpleTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

@cocotb.test(timeout_time=15, timeout_unit="ms")
async def arbiter_round_robin_simple_test(dut):
    """Simple test for round-robin arbiter without ACK protocol"""
    tb = ArbiterRoundRobinSimpleTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Simple round robin test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Phase 1: Basic functionality tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting grant signal test @ {time_ns}ns ===")
        await tb.test_grant_signals()
        await tb.handle_test_transition()

        # Phase 2: Basic arbitration test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting basic arbitration test @ {time_ns}ns ===")
        await tb.run_basic_arbitration_test(600)
        await tb.handle_test_transition()

        # Phase 3: Pattern tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting pattern tests @ {time_ns}ns ===")
        await tb.test_walking_requests()
        await tb.handle_test_transition()

        # Phase 4: Traffic pattern tests
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting traffic pattern tests @ {time_ns}ns ===")
        await tb.test_single_client_saturation()
        await tb.test_rapid_request_changes()
        await tb.handle_test_transition()

        # Phase 5: Fairness test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting fairness test @ {time_ns}ns ===")
        await tb.test_fairness()
        await tb.handle_test_transition()

        # Final validation
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Final validation @ {time_ns}ns ===")

        # Check for any monitor errors
        tb.check_monitor_errors()

        # Generate report
        report_success = tb.generate_final_report()

        if not report_success:
            raise AssertionError("Final report validation failed")

        tb.log.info("=== ALL SIMPLE ARBITER TESTS PASSED ===")

    except AssertionError as e:
        tb.log.error(f"Simple arbiter test failed: {str(e)}")

        # Debug info on failure
        try:
            final_stats = tb.monitor.get_comprehensive_stats()
            tb.log.error(f"Final monitor stats: Total grants={final_stats.get('total_grants', 0)}, "
                        f"Fairness={final_stats.get('fairness_index', 0):.3f}")

            master_stats = tb.master.get_stats()
            tb.log.error(f"Master stats: {master_stats}")

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
                tb.log.info("Master stopped gracefully")
        except Exception as e:
            tb.log.warning(f"Error stopping master: {e}")

        # Wait for any pending operations
        await tb.wait_clocks('clk', 10)

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4, 8 clients)
    REG_LEVEL=FUNC: 5 tests (all client counts) - default
    REG_LEVEL=FULL: 5 tests (same as FUNC)

    Returns:
        List of client counts
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_clients = [4, 5, 6, 8, 16]

    if reg_level == 'GATE':
        # Quick smoke test: power-of-2 sizes
        return [4, 8]

    else:  # FUNC or FULL (same for this test)
        # Full coverage: all client counts
        return all_clients


@pytest.mark.parametrize("clients", generate_test_params())
def test_arbiter_round_robin_simple(request, clients):
    """Run the simple round robin test"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "arbiter_round_robin_simple"
    toplevel = dut_name

    # Verilog sources for SIMPLE ROUND ROBIN arbiter
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_round_robin_simple.f'
    )

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    test_name_plus_params = f"test_{dut_name}_c{c_str}"

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

    # RTL parameters for SIMPLE ROUND ROBIN (only N parameter)
    parameters = {'N': clients}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
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
        print(f"Simple round robin test failed: {str(e)}")
        print(f"Test configuration: {clients} clients")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")

        print("\nTroubleshooting hints for simple arbiter:")
        print("- Check that arbiter_round_robin_simple.sv is present")
        print("- Verify parameter N is correctly passed")
        print("- Look for signal interface compatibility issues")
        print("- Check testbench initialization")

        raise  # Re-raise exception to indicate failure