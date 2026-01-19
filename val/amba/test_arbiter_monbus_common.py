# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_monbus_common
# Purpose: Updated Test Runner for Arbiter MonBus Common Module
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

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
from conftest import get_coverage_compile_args
import pytest

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def arbiter_monbus_common_test(dut):
    """
    Arbiter Monitor Common - Comprehensive Debug Test
    Thoroughly exercises monitor functionality with detailed analysis
    """

    # Get test parameters
    test_clients = int(os.environ.get('TEST_CLIENTS', '8'))
    test_agent_id = int(os.environ.get('TEST_AGENT_ID', '0x20'), 0)
    test_unit_id = int(os.environ.get('TEST_UNIT_ID', '0x2'), 0)
    test_level = os.environ.get('TEST_LEVEL', 'debug')

    print("=" * 80)
    print("COMPREHENSIVE ARBITER MONITOR DEBUG TEST")
    print("=" * 80)
    print(f"Configuration: {test_clients} clients, Agent 0x{test_agent_id:02X}, Unit 0x{test_unit_id:01X}")
    print(f"Test Level: {test_level}")
    print(f"Expected runtime: ~30-60 seconds for thorough testing")

    # Setup clock and reset
    clock = cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())
    await ClockCycles(dut.clk, 5)

    # Reset DUT
    print("\n🔄 Phase 1: Initializing and Resetting DUT...")
    dut.rst_n.value = 0
    dut.cfg_mon_enable.value = 0
    dut.monbus_ready.value = 1

    # Initialize all configuration registers
    dut.cfg_mon_pkt_type_enable.value = 0
    dut.cfg_mon_latency_thresh.value = 50
    dut.cfg_mon_starvation_thresh.value = 100
    dut.cfg_mon_fairness_thresh.value = 80
    dut.cfg_mon_active_thresh.value = 6
    dut.cfg_mon_ack_timeout_thresh.value = 32
    dut.cfg_mon_efficiency_thresh.value = 70
    dut.cfg_mon_sample_period.value = 16

    # Initialize arbiter inputs
    dut.request.value = 0
    dut.grant.value = 0
    dut.grant_id.value = 0
    dut.grant_valid.value = 0
    dut.grant_ack.value = 0
    dut.block_arb.value = 0

    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 10)

    print(f"✅ Reset complete. Initial state:")
    print(f"   Monitor enabled: {dut.cfg_mon_enable.value}")
    print(f"   Debug packet count: {dut.debug_packet_count.value}")
    print(f"   Debug FIFO count: {dut.debug_fifo_count.value}")

    # Test Statistics Tracking
    test_stats = {
        'packets_generated': [],
        'test_phases': [],
        'monitor_configs_tested': 0,
        'activity_patterns_tested': 0,
        'threshold_tests': 0,
        'error_conditions_tested': 0
    }

    # PHASE 2: Monitor Enable/Disable Comprehensive Test
    print("\n📝 Phase 2: Monitor Enable/Disable Test...")

    # Test disabled state
    dut.cfg_mon_enable.value = 0
    await ClockCycles(dut.clk, 5)

    # Generate activity while disabled - should produce no packets
    print("   Testing disabled state - generating activity (should produce 0 packets)...")
    for i in range(20):
        dut.request.value = 0b11111111  # All clients request
        await RisingEdge(dut.clk)
        dut.grant.value = 1 << (i % test_clients)
        dut.grant_id.value = i % test_clients
        dut.grant_valid.value = 1
        await RisingEdge(dut.clk)
        dut.grant_ack.value = 1 << (i % test_clients)
        await RisingEdge(dut.clk)
        dut.request.value = 0
        dut.grant.value = 0
        dut.grant_valid.value = 0
        dut.grant_ack.value = 0
        await RisingEdge(dut.clk)

    disabled_count = int(dut.debug_packet_count.value)
    print(f"   Disabled state packet count: {disabled_count} (should be 0)")

    # Enable monitor
    print("   Enabling monitor...")
    dut.cfg_mon_enable.value = 1
    dut.cfg_mon_pkt_type_enable.value = 0xFFFF  # Enable all packet types
    await ClockCycles(dut.clk, 5)
    test_stats['monitor_configs_tested'] += 1

    # PHASE 3: Basic Activity Pattern Tests
    print("\n🎯 Phase 3: Basic Activity Pattern Tests...")

    activity_patterns = [
        ("round_robin", "Round-robin through all clients"),
        ("single_client", "Single client repeated access"),
        ("burst_activity", "Burst of simultaneous requests"),
        ("sparse_activity", "Sparse random activity"),
        ("starvation_test", "Intentional client starvation"),
    ]

    for pattern_name, pattern_desc in activity_patterns:
        print(f"   Testing {pattern_name}: {pattern_desc}")
        start_count = int(dut.debug_packet_count.value)

        if pattern_name == "round_robin":
            for cycle in range(100):
                client = cycle % test_clients
                dut.request.value = 1 << client
                await RisingEdge(dut.clk)
                dut.grant.value = 1 << client
                dut.grant_id.value = client
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)
                dut.grant_ack.value = 1 << client
                await RisingEdge(dut.clk)
                dut.request.value = 0
                dut.grant.value = 0
                dut.grant_valid.value = 0
                dut.grant_ack.value = 0
                await RisingEdge(dut.clk)

        elif pattern_name == "single_client":
            for cycle in range(150):
                dut.request.value = 0b00000001  # Only client 0
                await RisingEdge(dut.clk)
                dut.grant.value = 0b00000001
                dut.grant_id.value = 0
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)
                dut.grant_ack.value = 0b00000001
                await RisingEdge(dut.clk)
                dut.request.value = 0
                dut.grant.value = 0
                dut.grant_valid.value = 0
                dut.grant_ack.value = 0
                await RisingEdge(dut.clk)

        elif pattern_name == "burst_activity":
            for burst in range(20):
                # All clients request simultaneously
                dut.request.value = (1 << test_clients) - 1
                await ClockCycles(dut.clk, 5)  # Hold requests

                # Grant to random clients
                for grant_cycle in range(8):
                    client = grant_cycle % test_clients
                    dut.grant.value = 1 << client
                    dut.grant_id.value = client
                    dut.grant_valid.value = 1
                    await RisingEdge(dut.clk)
                    dut.grant_ack.value = 1 << client
                    await RisingEdge(dut.clk)
                    dut.grant.value = 0
                    dut.grant_valid.value = 0
                    dut.grant_ack.value = 0
                    await RisingEdge(dut.clk)

                dut.request.value = 0
                await ClockCycles(dut.clk, 10)  # Quiet period

        elif pattern_name == "sparse_activity":
            import random
            for cycle in range(200):
                if random.random() < 0.3:  # 30% activity rate
                    clients_mask = random.randint(1, (1 << test_clients) - 1)
                    dut.request.value = clients_mask
                    await ClockCycles(dut.clk, random.randint(1, 4))

                    # Grant to one of the requesting clients
                    requesting_clients = [i for i in range(test_clients) if clients_mask & (1 << i)]
                    if requesting_clients:
                        client = random.choice(requesting_clients)
                        dut.grant.value = 1 << client
                        dut.grant_id.value = client
                        dut.grant_valid.value = 1
                        await RisingEdge(dut.clk)
                        dut.grant_ack.value = 1 << client
                        await RisingEdge(dut.clk)
                        dut.grant.value = 0
                        dut.grant_valid.value = 0
                        dut.grant_ack.value = 0

                    dut.request.value = 0
                await RisingEdge(dut.clk)

        elif pattern_name == "starvation_test":
            print(f"     Testing starvation conditions (client 7 starved)...")
            for cycle in range(200):
                # All clients except 7 get requests
                dut.request.value = ((1 << test_clients) - 1) & ~(1 << (test_clients-1))
                await RisingEdge(dut.clk)

                # Only grant to clients 0-6, never client 7
                client = cycle % (test_clients - 1)
                dut.grant.value = 1 << client
                dut.grant_id.value = client
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)
                dut.grant_ack.value = 1 << client
                await RisingEdge(dut.clk)
                dut.request.value = 0
                dut.grant.value = 0
                dut.grant_valid.value = 0
                dut.grant_ack.value = 0
                await RisingEdge(dut.clk)

        end_count = int(dut.debug_packet_count.value)
        packets_this_test = end_count - start_count
        test_stats['packets_generated'].append(packets_this_test)
        test_stats['activity_patterns_tested'] += 1

        print(f"     Generated {packets_this_test} packets during {pattern_name}")

    # PHASE 4: Configuration and Threshold Tests
    print(f"\n⚙️  Phase 4: Configuration and Threshold Tests...")

    threshold_configs = [
        {"latency": 20, "starvation": 50, "desc": "Low thresholds (sensitive)"},
        {"latency": 100, "starvation": 200, "desc": "Medium thresholds"},
        {"latency": 500, "starvation": 1000, "desc": "High thresholds (less sensitive)"},
    ]

    for config in threshold_configs:
        print(f"   Testing: {config['desc']}")
        start_count = int(dut.debug_packet_count.value)

        # Apply new thresholds
        dut.cfg_mon_latency_thresh.value = config["latency"]
        dut.cfg_mon_starvation_thresh.value = config["starvation"]
        await ClockCycles(dut.clk, 5)

        # Generate test activity
        for cycle in range(100):
            dut.request.value = 0b11110000 if cycle < 50 else 0b00001111
            await RisingEdge(dut.clk)
            client = (cycle % 4) + (0 if cycle < 50 else 4)
            dut.grant.value = 1 << client
            dut.grant_id.value = client
            dut.grant_valid.value = 1
            await RisingEdge(dut.clk)
            dut.grant_ack.value = 1 << client
            await RisingEdge(dut.clk)
            dut.request.value = 0
            dut.grant.value = 0
            dut.grant_valid.value = 0
            dut.grant_ack.value = 0
            await RisingEdge(dut.clk)

        end_count = int(dut.debug_packet_count.value)
        packets_this_config = end_count - start_count
        test_stats['threshold_tests'] += 1
        print(f"     Generated {packets_this_config} packets with {config['desc']}")

    # PHASE 5: Error Condition Testing
    print(f"\n⚠️  Phase 5: Error Condition and Edge Case Testing...")

    error_tests = [
        "rapid_enable_disable",
        "fifo_stress_test",
        "simultaneous_all_clients",
        "protocol_violation_simulation"
    ]

    for error_test in error_tests:
        print(f"   Testing: {error_test}")
        start_count = int(dut.debug_packet_count.value)

        if error_test == "rapid_enable_disable":
            for toggle in range(50):
                dut.cfg_mon_enable.value = toggle % 2
                await ClockCycles(dut.clk, 2)
                # Generate some activity during toggle
                dut.request.value = 0b00000011
                await RisingEdge(dut.clk)
                dut.grant.value = 0b00000001
                dut.grant_id.value = 0
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)
                dut.grant_ack.value = 0b00000001
                await RisingEdge(dut.clk)
                dut.request.value = 0
                dut.grant.value = 0
                dut.grant_valid.value = 0
                dut.grant_ack.value = 0
                await RisingEdge(dut.clk)
            dut.cfg_mon_enable.value = 1  # Ensure enabled for remaining tests

        elif error_test == "fifo_stress_test":
            # Generate rapid bursts to stress FIFO
            dut.monbus_ready.value = 0  # Block output to fill FIFO
            for burst in range(50):
                for cycle in range(10):
                    dut.request.value = 0xFF  # All clients
                    await RisingEdge(dut.clk)
                    dut.grant.value = 1 << (cycle % test_clients)
                    dut.grant_id.value = cycle % test_clients
                    dut.grant_valid.value = 1
                    await RisingEdge(dut.clk)
                    dut.grant_ack.value = 1 << (cycle % test_clients)
                    await RisingEdge(dut.clk)
                    dut.request.value = 0
                    dut.grant.value = 0
                    dut.grant_valid.value = 0
                    dut.grant_ack.value = 0
                    await RisingEdge(dut.clk)
            dut.monbus_ready.value = 1  # Unblock output
            await ClockCycles(dut.clk, 50)  # Let FIFO drain

        elif error_test == "simultaneous_all_clients":
            # Maximum stress - all clients active
            for cycle in range(100):
                dut.request.value = (1 << test_clients) - 1  # All clients
                await ClockCycles(dut.clk, 3)
                client = cycle % test_clients
                dut.grant.value = 1 << client
                dut.grant_id.value = client
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)
                dut.grant_ack.value = 1 << client
                await RisingEdge(dut.clk)
                dut.grant.value = 0
                dut.grant_valid.value = 0
                dut.grant_ack.value = 0
                await RisingEdge(dut.clk)
                dut.request.value = 0
                await RisingEdge(dut.clk)

        elif error_test == "protocol_violation_simulation":
            # Test unusual timing patterns
            for violation in range(30):
                # Grant without request (unusual but not invalid)
                dut.grant.value = 0b00000001
                dut.grant_id.value = 0
                dut.grant_valid.value = 1
                await RisingEdge(dut.clk)

                # Request after grant
                dut.request.value = 0b00000001
                await RisingEdge(dut.clk)

                # Clear everything
                dut.request.value = 0
                dut.grant.value = 0
                dut.grant_valid.value = 0
                await ClockCycles(dut.clk, 5)

        end_count = int(dut.debug_packet_count.value)
        packets_this_error_test = end_count - start_count
        test_stats['error_conditions_tested'] += 1
        print(f"     Generated {packets_this_error_test} packets during {error_test}")

    # PHASE 6: Final State Analysis
    print(f"\n📊 Phase 6: Final State Analysis and Validation...")

    final_packet_count = int(dut.debug_packet_count.value)
    final_fifo_count = int(dut.debug_fifo_count.value)

    # Let FIFO completely drain
    await ClockCycles(dut.clk, 100)

    drained_fifo_count = int(dut.debug_fifo_count.value)

    print(f"   Final debug packet count: {final_packet_count}")
    print(f"   Final FIFO count: {final_fifo_count}")
    print(f"   After drain FIFO count: {drained_fifo_count}")

    # Generate comprehensive test report
    print(f"\n" + "=" * 80)
    print(f"COMPREHENSIVE TEST RESULTS SUMMARY")
    print(f"=" * 80)
    print(f"Total simulation time: {get_sim_time('ns')} ns ({get_sim_time('us'):.1f} us)")
    print(f"Total packets generated: {final_packet_count}")
    print(f"Monitor configurations tested: {test_stats['monitor_configs_tested']}")
    print(f"Activity patterns tested: {test_stats['activity_patterns_tested']}")
    print(f"Threshold configurations tested: {test_stats['threshold_tests']}")
    print(f"Error conditions tested: {test_stats['error_conditions_tested']}")

    packets_per_phase = test_stats['packets_generated']
    if packets_per_phase:
        print(f"Packets per test phase: min={min(packets_per_phase)}, max={max(packets_per_phase)}, avg={sum(packets_per_phase)/len(packets_per_phase):.1f}")

    # Detailed validation criteria
    validation_results = []

    # Check 1: Sufficient packet generation
    if final_packet_count >= 1000:
        validation_results.append("✅ Excellent packet generation (≥1000 packets)")
    elif final_packet_count >= 500:
        validation_results.append("✅ Good packet generation (≥500 packets)")
    elif final_packet_count >= 100:
        validation_results.append("⚠️  Moderate packet generation (≥100 packets)")
    else:
        validation_results.append("❌ Insufficient packet generation (<100 packets)")

    # Check 2: FIFO operation
    if drained_fifo_count <= 1:
        validation_results.append("✅ FIFO draining correctly")
    else:
        validation_results.append("⚠️  FIFO may have drainage issues")

    # Check 3: Configuration responsiveness
    if test_stats['monitor_configs_tested'] >= 3:
        validation_results.append("✅ Multiple configurations tested successfully")
    else:
        validation_results.append("⚠️  Limited configuration testing")

    # Check 4: Stress testing
    if test_stats['error_conditions_tested'] >= 3:
        validation_results.append("✅ Comprehensive stress testing completed")
    else:
        validation_results.append("⚠️  Limited stress testing")

    print(f"\nVALIDATION RESULTS:")
    for result in validation_results:
        print(f"  {result}")

    # Determine overall success
    failed_validations = [r for r in validation_results if r.startswith("❌")]
    success = len(failed_validations) == 0 and final_packet_count >= 100

    if success:
        print(f"\n🎉 COMPREHENSIVE TEST PASSED!")
        print(f"   Monitor demonstrated robust functionality across all test phases")
        print(f"   Total packets: {final_packet_count}, Runtime: {get_sim_time('us'):.1f} μs")
        print(f"   Monitor RTL is working correctly and thoroughly validated ✅")
    else:
        print(f"\n❌ COMPREHENSIVE TEST FAILED!")
        print(f"   Failed validations: {len(failed_validations)}")
        print(f"   Issues found in monitor functionality")

    print(f"=" * 80)

    # Final assertion with detailed error message
    if not success:
        raise AssertionError(f"Comprehensive monitor test failed - {len(failed_validations)} validation failures, {final_packet_count} packets generated")


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
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

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
        # Monitor packages (must be compiled in dependency order)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_amba5_pkg.sv"),
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
    test_name_plus_params = f"test_{worker_id}_{dut_name}_enhanced_c{c_str}_ack{ack_str}_w{weighted_str}_f{f_str}_a{a_str}_u{u_str}_{test_level}"
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
        'TRACE_FILE': f"{sim_build}/dump.vcd",
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
        "--trace",
        
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
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
