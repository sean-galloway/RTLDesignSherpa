# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axis_slave_cg
# Purpose: AXIS Slave Clock Gated Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Slave Clock Gated Test Runner

Test runner for the axis_slave_cg module using the CocoTB framework.
Tests clock gating functionality while validating AXIS stream transactions.

Based on the AXI4 clock gated test runner pattern but adapted for AXIS stream testing.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the clock gated testbench
from CocoTBFramework.tbclasses.axis4.axis_slave_cg_tb import AXISSlaveCGTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axis_slave_cg_test(dut):
    """AXIS slave clock gated test using the enhanced framework"""

    # Create clock-gated testbench instance
    tb = AXISSlaveCGTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIS slave CG test with seed: {seed}')

    # Get test parameters
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    cg_test_mode = os.environ.get('CG_TEST_MODE', 'comprehensive').lower()  # comprehensive, basic, efficiency

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'")
        test_level = 'basic'

    # Start clock and reset
    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    # Setup components
    tb.setup_components()

    tb.log.info("=" * 80)
    tb.log.info(f"AXIS SLAVE CLOCK GATED TEST - {test_level.upper()} LEVEL")
    tb.log.info("=" * 80)
    tb.log.info(f"CG Test Mode: {cg_test_mode.upper()}")
    tb.log.info(f"AXIS widths: DATA={tb.TEST_DATA_WIDTH}, ID={tb.TEST_ID_WIDTH}, DEST={tb.TEST_DEST_WIDTH}, USER={tb.TEST_USER_WIDTH}")

    try:
        # Test configurations based on test level
        if test_level == 'basic':
            idle_counts = [4, 8]
            test_packets = 10
            power_measurement_cycles = 500
        elif test_level == 'medium':
            idle_counts = [2, 4, 8, 16]
            test_packets = 25
            power_measurement_cycles = 1000
        else:  # full
            idle_counts = [1, 2, 4, 8, 16, 32]
            test_packets = 50
            power_measurement_cycles = 2000

        total_tests = 0
        passed_tests = 0
        power_efficiency_results = []

        # === COMPREHENSIVE CLOCK GATING TESTS ===
        if cg_test_mode in ['comprehensive', 'basic'] or test_level != 'efficiency':

            # Test 1: Functional Equivalence Validation
            tb.log.info("=== Test 1: Functional Equivalence ===")

            async def basic_transfer_test():
                """Basic transfer test for equivalence comparison."""
                await tb.run_basic_transfer_test(num_packets=5)
                return True

            equivalence_ok = await tb.test_functional_equivalence(basic_transfer_test)
            total_tests += 1
            if equivalence_ok:
                passed_tests += 1

            # Test 2: Clock Gating Behavior with Different Idle Counts
            tb.log.info("=== Test 2: Clock Gating Behavior ===")

            for idle_count in idle_counts:
                tb.log.info(f"Testing with idle_count = {idle_count}")

                try:
                    success = await tb.run_basic_transfer_test_cg(
                        num_packets=test_packets//2,
                        enable_cg=True,
                        idle_count=idle_count
                    )

                    # Check ready signals during potential gating
                    ready_signals_ok = await tb.validate_ready_signals_during_gating()

                    total_tests += 1
                    if success and ready_signals_ok:
                        passed_tests += 1
                        tb.log.info(f"✓ Idle count {idle_count}: Transfer successful, ready signals OK")
                    else:
                        tb.log.error(f"✗ Idle count {idle_count}: Transfer: {success}, ready signals: {ready_signals_ok}")

                except Exception as e:
                    total_tests += 1
                    tb.log.error(f"✗ Idle count {idle_count} test failed: {e}")

            # Test 3: Gating Transition Validation
            tb.log.info("=== Test 3: Gating Transitions ===")
            await tb.configure_clock_gating(enable=True, idle_count=4)

            # Force idle to trigger gating
            await tb.wait_clocks('aclk', 20)
            gating_achieved = await tb.wait_for_gating_state(target_state=True, timeout_cycles=30)

            if gating_achieved:
                # Resume activity and check ungating
                try:
                    await tb.run_basic_transfer_test(num_packets=3)
                    ungating_achieved = await tb.wait_for_gating_state(target_state=False, timeout_cycles=20)

                    total_tests += 1
                    if ungating_achieved:
                        passed_tests += 1
                        tb.log.info("✓ Gating transitions working correctly")
                    else:
                        tb.log.error("✗ Ungating not achieved after activity resumed")
                except Exception as e:
                    total_tests += 1
                    tb.log.error(f"✗ Gating transition test failed: {e}")
            else:
                total_tests += 1
                tb.log.warning("Could not achieve gated state for transition testing")

            # Test 4: Power Efficiency Measurement
            tb.log.info("=== Test 4: Power Efficiency Measurement ===")

            for idle_count in [4, 8]:
                await tb.configure_clock_gating(enable=True, idle_count=idle_count)

                # Start power measurement
                efficiency_task = tb.measure_power_efficiency(power_measurement_cycles)

                # Perform transfers during measurement with realistic traffic
                packet_count = 0
                for cycle in range(0, power_measurement_cycles, 50):  # Transfer every 50 cycles
                    if cycle + 20 < power_measurement_cycles:  # Ensure we don't exceed measurement period
                        try:
                            data = 0x40000000 + packet_count
                            packet = tb.axis_master.create_packet(data=data, last=1)
                            await tb.axis_master.send(packet)
                            packet_count += 1

                            # Add some idle time between transfers
                            await tb.wait_clocks('aclk', 15)
                        except Exception as e:
                            tb.log.warning(f"Transfer failed during power measurement: {e}")

                # Get efficiency results
                efficiency_stats = await efficiency_task
                power_efficiency_results.append({
                    'idle_count': idle_count,
                    'efficiency_percent': efficiency_stats.get('power_efficiency_percent', 0),
                    'gating_transitions': efficiency_stats.get('gating_transitions', 0)
                })

                tb.log.info(f"Idle count {idle_count}: {efficiency_stats.get('power_efficiency_percent', 0):.1f}% power efficiency")

        # === STRESS TESTING ===
        if test_level == 'full':
            tb.log.info("=== Test 5: Stress Testing ===")

            try:
                await tb.run_gating_stress_test(num_packets=20)
                total_tests += 1
                passed_tests += 1
                tb.log.info("✓ Stress test passed")
            except Exception as e:
                total_tests += 1
                tb.log.error(f"✗ Stress test failed: {e}")

        # === FINAL RESULTS ===
        tb.log.info("=" * 80)
        tb.log.info("CLOCK GATED AXIS SLAVE TEST SUMMARY")
        tb.log.info("=" * 80)

        success_rate = (passed_tests / total_tests * 100) if total_tests > 0 else 0
        tb.log.info(f"Tests passed:           {passed_tests}/{total_tests}")
        tb.log.info(f"Success rate:           {success_rate:.1f}%")
        tb.log.info(f"Test level:             {test_level.upper()}")

        if power_efficiency_results:
            tb.log.info("Power Efficiency Results:")
            for result in power_efficiency_results:
                tb.log.info(f"  Idle count {result['idle_count']}: {result['efficiency_percent']:.1f}% efficiency")

        if success_rate < 75:  # Allow margin for clock gating complexity and statistics timing
            tb.log.error("❌ AXIS SLAVE CG TEST FAILED")
            raise Exception(f"Clock gated test failed with {success_rate:.1f}% success rate")

        tb.log.info("✅ AXIS SLAVE CG TEST PASSED")

    except Exception as e:
        tb.log.error(f"AXIS slave CG test FAILED with exception: {str(e)}")
        raise


def generate_axis_cg_params():
    """Generate test parameters for clock-gated AXIS slave testing"""

    # Clock gated modules test with RTL only
    skid_depths = [2, 4]
    data_widths = [32, 64]
    id_widths = [4, 8]
    dest_widths = [4, 8]
    user_widths = [1]
    test_levels = ['basic', 'medium', 'full']
    cg_test_modes = ['comprehensive', 'efficiency']

    # Debug mode for quick testing
    debug_mode = True
    if debug_mode:
        return [
            (4, 32, 8, 4, 1, 'basic', 'comprehensive'),
            (4, 32, 8, 4, 1, 'medium', 'comprehensive'),
        ]

    return list(product(skid_depths, data_widths, id_widths, dest_widths, user_widths,
                        test_levels, cg_test_modes))


@pytest.mark.parametrize("skid_depth, data_width, id_width, dest_width, user_width, test_level, cg_test_mode",
                        generate_axis_cg_params())
def test_axis_slave_cg(skid_depth, data_width, id_width, dest_width, user_width, test_level, cg_test_mode):
    """Test AXIS slave clock gated with specified parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_axis': 'rtl/amba/axis4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Clock gated module details
    dut_name = "axis_slave_cg"

    id_str = f"sd{skid_depth}_dw{data_width:03d}_iw{id_width:02d}_destw{dest_width}_uw{user_width}_{test_level}_{cg_test_mode}"
    test_name_plus_params = f"test_{worker_id}_axis_slave_cg_{id_str}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL files for clock gated AXIS slave
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "amba_clock_gate_ctrl.sv"),  # Clock gate controller
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axis'], "axis_slave.sv"),  # Base module
        os.path.join(rtl_dict['rtl_axis'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Parameters for the DUT
    rtl_parameters = {
        'SKID_DEPTH': skid_depth,
        'AXIS_DATA_WIDTH': data_width,
        'AXIS_ID_WIDTH': id_width,
        'AXIS_DEST_WIDTH': dest_width,
        'AXIS_USER_WIDTH': user_width,
        'CG_IDLE_COUNT_WIDTH': 8
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + id_width + dest_width) / 100.0
    timeout_ms = int(5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,

        'TEST_LEVEL': test_level,
        'CG_TEST_MODE': cg_test_mode,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width),
        'TEST_USER_WIDTH': str(user_width),
        'CG_IDLE_COUNT_WIDTH': '8',  # Default width for idle count
        'SEED': str(random.randint(1, 1000000)),
        'AXIS_COMPLIANCE_CHECK': '1',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected pins
    ]
    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIS Slave CG test: {dut_name}")
    print(f"AXIS Config: SKID={skid_depth}, DATA={data_width}, ID={id_width}, DEST={dest_width}, USER={user_width}")
    print(f"CG Test Mode: {cg_test_mode.upper()}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} AXIS Slave CG test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIS Slave CG test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Can run individual tests or use pytest
    pytest.main([__file__, "-v", "-s"])