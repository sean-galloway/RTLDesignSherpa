# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AmbaClockGateCtrlConfig
# Purpose: Configuration class for AMBA Clock Gate Controller tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import contextlib
import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class AmbaClockGateCtrlConfig:
    """Configuration class for AMBA Clock Gate Controller tests"""
    def __init__(self, name, valid_patterns, idle_count=8):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            valid_patterns: List of valid signal patterns
            idle_count: Number of idle cycles before clock gating activates
        """
        self.name = name
        self.valid_patterns = valid_patterns
        self.idle_count = idle_count


class AmbaClockGateCtrlTB(TBBase):
    """
    Testbench for the AMBA Clock Gate Controller module
    Features:
    - Verify clock gating with different valid signal patterns
    - Test various idle count thresholds
    - Monitor gating behavior and timing
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.CLK_PERIOD_NS = self.convert_to_int(os.environ.get('CLK_PERIOD_NS', '10'))
        self.CG_IDLE_COUNT_WIDTH = self.convert_to_int(os.environ.get('TEST_ICW', '4'))

        # Calculate max idle count value based on width
        self.MAX_IDLE_COUNT = (1 << self.CG_IDLE_COUNT_WIDTH) - 1

        # Calculate clock frequency in MHz
        self.CLK_FREQ_MHZ = 1000 / self.CLK_PERIOD_NS

        # Initialize random generator
        random.seed(self.SEED)

        # Extract clock and reset signals
        self.clk_in = self.dut.clk_in
        self.aresetn = self.dut.aresetn

        # Extract configuration interface signals
        self.cfg_cg_enable = self.dut.cfg_cg_enable
        self.cfg_cg_idle_count = self.dut.cfg_cg_idle_count

        # Extract activity monitoring signals
        self.user_valid = self.dut.user_valid
        self.axi_valid = self.dut.axi_valid

        # Extract clock gating control output signals
        self.clk_out = self.dut.clk_out
        self.gating = self.dut.gating
        self.idle = self.dut.idle

        # Create the AXI Clock Gate Controller testbench class
        self.cg_ctrl = AxiClockGateCtrl(
            dut,
            instance_path="",  # No instance path in this case (top level)
            clock_signal_name="clk_in",
            user_valid_signals=["user_valid"],
            axi_valid_signals=["axi_valid"]
        )

        # Log configuration
        self.log.info("AMBA Clock Gate Controller TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"CLK={self.CLK_PERIOD_NS}ns ({self.CLK_FREQ_MHZ:.1f}MHz)")
        self.log.info(f"CG_IDLE_COUNT_WIDTH={self.CG_IDLE_COUNT_WIDTH} (Max idle count: {self.MAX_IDLE_COUNT})")

        # Monitoring data
        self.activity_stats = []
        self.gating_timestamps = []
        self.idle_timestamps = []

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.aresetn.value = 0
        self.cfg_cg_enable.value = 0
        self.cfg_cg_idle_count.value = 0
        self.user_valid.value = 0
        self.axi_valid.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clk_in', 5)

        # Release reset
        self.aresetn.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk_in', 10)

        # Clear monitoring data
        self.activity_stats.clear()
        self.gating_timestamps.clear()
        self.idle_timestamps.clear()

        self.log.debug('Ending reset_dut')

    async def configure_controller(self, enable=True, idle_count=8):
        """
        Configure the clock gate controller

        Args:
            enable: True to enable clock gating, False to disable
            idle_count: Number of idle cycles before clock gating activates
        """
        # Ensure idle_count doesn't exceed the maximum allowed by the counter width
        if idle_count > self.MAX_IDLE_COUNT:
            self.log.warning(f"Requested idle_count {idle_count} exceeds maximum {self.MAX_IDLE_COUNT}, clamping")
            idle_count = self.MAX_IDLE_COUNT

        self.log.info(f"Configuring controller: enable={enable}, idle_count={idle_count}")

        # Use the AxiClockGateCtrl helper class
        self.cg_ctrl.enable_clock_gating(enable)
        self.cg_ctrl.set_idle_count(idle_count)

        # Wait a few cycles for configuration to take effect
        await self.wait_clocks('clk_in', 5)

        # Verify configuration was applied
        state = self.cg_ctrl.get_current_state()
        self.log.info(f"Controller state: {state}")
        assert state['enabled'] == enable, f"Enable setting mismatch: expected {enable}, got {state['enabled']}"
        assert state['idle_count'] == idle_count, f"Idle count mismatch: expected {idle_count}, got {state['idle_count']}"

    async def drive_valid_pattern(self, valid_pattern, valid_type='user'):
        """
        Drive a pattern of valid signals

        Args:
            valid_pattern: List of 0s and 1s for the valid signal
            valid_type: 'user', 'axi', or 'both' to indicate which valid signal to drive

        Returns:
            Dict with timing stats
        """
        self.log.info(f"Driving {valid_type} valid pattern: {valid_pattern}")

        # Initialize stats
        stats = {
            'pattern_length': len(valid_pattern),
            'valid_cycles': sum(valid_pattern),
            'start_time': get_sim_time('ns'),
            'end_time': None,
            'first_idle_time': None,
            'first_gating_time': None,
        }

        # Monitor for idle and gating in the background
        monitor_task = cocotb.start_soon(self._monitor_idle_and_gating(stats))

        # Drive the pattern
        for i, value in enumerate(valid_pattern):
            self.log.debug(f"Cycle {i}: Setting {valid_type} valid to {value}")
            if valid_type in ['user', 'both']:
                self.user_valid.value = value
            if valid_type in ['axi', 'both']:
                self.axi_valid.value = value
            await RisingEdge(self.clk_in)

        # Clear the valid signals
        if valid_type in ['user', 'both']:
            self.user_valid.value = 0
        if valid_type in ['axi', 'both']:
            self.axi_valid.value = 0

        # Wait for a reasonable time to observe gating
        max_idle_count = int(self.cfg_cg_idle_count.value)
        wait_cycles = max(20, max_idle_count * 2)
        self.log.debug(f"Waiting for {wait_cycles} cycles to observe gating behavior")
        for _ in range(wait_cycles):
            await RisingEdge(self.clk_in)

        # Record end time
        stats['end_time'] = get_sim_time('ns')

        # Wait for monitor to complete
        await monitor_task

        # Get final controller state
        state = self.cg_ctrl.get_current_state()
        stats['final_state'] = state

        self.log.info(f"Pattern complete: idle={state['is_idle']}, gated={state['is_gated']}")
        return stats

    async def _monitor_idle_and_gating(self, stats):
        """
        Monitor for idle and gating signals

        Args:
            stats: Dict to store timing stats
        """
        prev_idle = int(self.idle.value)
        prev_gating = int(self.gating.value)

        while True:
            await RisingEdge(self.clk_in)

            # Check for idle transition
            curr_idle = int(self.idle.value)
            if curr_idle == 1 and prev_idle == 0:
                time_ns = get_sim_time('ns')
                self.idle_timestamps.append(time_ns)
                if stats['first_idle_time'] is None:
                    stats['first_idle_time'] = time_ns
                    self.log.debug(f"First idle detected @ {time_ns}ns")

            # Check for gating transition
            curr_gating = int(self.gating.value)
            if curr_gating == 1 and prev_gating == 0:
                time_ns = get_sim_time('ns')
                self.gating_timestamps.append(time_ns)
                if stats['first_gating_time'] is None:
                    stats['first_gating_time'] = time_ns
                    self.log.debug(f"First gating detected @ {time_ns}ns")

            prev_idle = curr_idle
            prev_gating = curr_gating

            # Exit if both events have occurred or timeout
            if (stats['first_idle_time'] is not None and
                stats['first_gating_time'] is not None):
                break

            # Optional timeout after a long wait
            if (get_sim_time('ns') - stats['start_time'] > 5000):
                self.log.warning("Timeout waiting for idle or gating signals")
                break

    async def verify_basic_operation(self):
        """
        Verify basic clock gating operation

        Returns:
            True if verification passed
        """
        self.log.info("Verifying basic clock gating operation")

        # Test cases to run
        test_cases = [
            # (enable, idle_count, valid_pattern, valid_type)
            (True, 8, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'user'),
            (True, 4, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'user'),
            (True, 8, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'axi'),
            (False, 8, [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'user'),
        ]

        if self.TEST_LEVEL != 'basic':
            # Add more complex test cases for higher test levels
            test_cases.extend([
                (True, 8, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0], 'both'),
                (True, 2, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'user'),
                (True, 16, [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 'user'),
            ])

        all_passed = True

        for i, (enable, idle_count, valid_pattern, valid_type) in enumerate(test_cases):
            self.log.info(f"Test case {i+1}: enable={enable}, idle_count={idle_count}, valid_type={valid_type}")

            # Reset for clean state
            await self.reset_dut()

            # Configure controller
            await self.configure_controller(enable, idle_count)

            # Drive valid pattern
            stats = await self.drive_valid_pattern(valid_pattern, valid_type)

            # Store stats for analysis
            self.activity_stats.append(stats)

            # Verify behavior
            passed = self._verify_test_case(enable, idle_count, valid_pattern, valid_type, stats)
            if not passed:
                self.log.error(f"Test case {i+1} failed")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break  # Stop on first failure in basic mode

        return all_passed

    def _verify_test_case(self, enable, idle_count, valid_pattern, valid_type, stats):
        # sourcery skip: use-next
        """
        Verify a test case

        Args:
            enable: Whether clock gating was enabled
            idle_count: Configured idle count threshold
            valid_pattern: The valid pattern that was driven
            valid_type: Which valid signals were driven
            stats: Collected stats during the test

        Returns:
            True if verification passed
        """
        # If clock gating was disabled, verify no gating occurred
        if not enable:
            if stats['first_gating_time'] is not None:
                self.log.error("Gating occurred when clock gating was disabled")
                return False
            return True

        # If no idle state was detected, the test failed
        if stats['first_idle_time'] is None:
            self.log.error("No idle state detected")
            return False

        # If gating was enabled but no gating occurred, check if the pattern was continuously active
        if stats['first_gating_time'] is None:
            # If the pattern has all 1's or not enough 0's to trigger gating, this is expected
            if sum(valid_pattern) == len(valid_pattern) or len(valid_pattern) - sum(valid_pattern) < idle_count:
                self.log.info("No gating occurred as expected due to continuous activity")
                return True
            self.log.error("No gating occurred when it should have")
            return False

        # Verify gating occurred after idle_count cycles of inactivity
        valid_end_idx = 0
        for i in reversed(range(len(valid_pattern))):
            if valid_pattern[i] == 1:
                valid_end_idx = i
                break

        # Calculate expected earliest gating time
        # valid_end_time = stats['start_time'] + (valid_end_idx + 1) * self.CLK_PERIOD_NS
        # expected_gating_time = valid_end_time + (idle_count + 1) * self.CLK_PERIOD_NS

        # Allow a small tolerance in timing due to simulation variations
        # tolerance_ns = 2 * self.CLK_PERIOD_NS

        # if stats['first_gating_time'] < expected_gating_time - tolerance_ns:
        #     self.log.error(f"Gating occurred too early: {stats['first_gating_time']} < {expected_gating_time} - {tolerance_ns}")
        #     return False

        # if stats['first_gating_time'] > expected_gating_time + tolerance_ns:
        #     self.log.warning(f"Gating occurred later than expected: {stats['first_gating_time']} > {expected_gating_time} + {tolerance_ns}")

        # Check final state
        if stats['final_state']['is_idle'] != True:
            self.log.error("Final idle state incorrect")
            return False

        if stats['final_state']['is_gated'] != True:
            self.log.error("Final gating state incorrect")
            return False

        self.log.info("Test case verification passed")
        return True

    async def run_realistic_workload_test(self):
        """
        Run test with realistic AXI workload patterns

        Returns:
            True if all tests passed
        """
        self.log.info("Running realistic workload test")

        # Define more complex patterns based on test level
        if self.TEST_LEVEL == 'basic':
            # Burst followed by idle
            patterns = [
                [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            ]
        elif self.TEST_LEVEL == 'medium':
            # More varied patterns
            patterns = [
                [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            ]
        else:  # full
            # More complex patterns
            patterns = [
                [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                [1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
            ]

        all_passed = True

        # Reset and configure
        await self.reset_dut()
        await self.configure_controller(True, 8)

        # Run each pattern
        for i, pattern in enumerate(patterns):
            self.log.info(f"Testing pattern {i+1}: {pattern}")

            # Drive the pattern
            stats = await self.drive_valid_pattern(pattern, 'both')

            # Store for analysis
            self.activity_stats.append(stats)

            # Verify behavior
            passed = self._verify_test_case(True, 8, pattern, 'both', stats)
            if not passed:
                self.log.error(f"Workload pattern {i+1} failed")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break  # Stop on first failure in basic mode

        return all_passed

    async def run_idle_count_sweep_test(self):
        """
        Test with different idle count thresholds

        Returns:
            True if all tests passed
        """
        self.log.info("Running idle count sweep test")

        # Set up idle counts to test based on test level and max value
        max_count = self.MAX_IDLE_COUNT

        if self.TEST_LEVEL == 'basic':
            # Use a small and medium value for basic testing
            idle_counts = [2, min(8, max_count)]
        elif self.TEST_LEVEL == 'medium':
            # More extensive testing for medium level
            idle_counts = [1, min(4, max_count), min(8, max_count)]
            # Add the max value if it's not already included
            if max_count > 8:
                idle_counts.append(max_count)
        else:  # full
            # Comprehensive testing for full level
            idle_counts = [1]  # Minimum value

            # Add powers of 2 up to the maximum
            power = 1
            while power <= max_count:
                if power > 1:  # Skip 1 as we already added it
                    idle_counts.append(power)
                power *= 2

            # Add the maximum value if it's not a power of 2
            if max_count not in idle_counts:
                idle_counts.append(max_count)

        # Fixed pattern for consistent comparison
        pattern = [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

        all_passed = True

        for idle_count in idle_counts:
            self.log.info(f"Testing with idle_count={idle_count}")

            # Reset and configure
            await self.reset_dut()
            await self.configure_controller(True, idle_count)

            # Drive the pattern
            stats = await self.drive_valid_pattern(pattern, 'user')

            # Store for analysis
            self.activity_stats.append(stats)

            # Verify behavior
            passed = self._verify_test_case(True, idle_count, pattern, 'user', stats)
            if not passed:
                self.log.error(f"Idle count {idle_count} test failed")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break  # Stop on first failure in basic mode

        return all_passed

    async def run_forced_wakeup_test(self):
        """
        Test forcing a wakeup from gated state

        Returns:
            True if test passed
        """
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping forced wakeup test in basic mode")
            return True

        self.log.info("Running forced wakeup test")

        # Reset and configure
        await self.reset_dut()
        await self.configure_controller(True, 4)

        # Drive pattern to reach gated state
        pattern = [1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
        stats = await self.drive_valid_pattern(pattern, 'user')

        # Verify we reached gated state
        if stats['first_gating_time'] is None:
            self.log.error("Failed to reach gated state")
            return False

        self.log.info("Reached gated state, forcing wakeup")

        # Force wakeup using the API
        original_values = self.cg_ctrl.force_wakeup()
        self.log.info(f"Forced wakeup, original values: {original_values}")

        # Wait a few cycles
        await self.wait_clocks('clk_in', 5)

        # Check if we exited gating state
        state = self.cg_ctrl.get_current_state()
        if state['is_gated']:
            self.log.error("Failed to exit gating state after force wakeup")
            return False

        # Restore original values
        self.cg_ctrl.restore_signals(original_values)
        self.log.info("Restored original values")

        # Wait to return to gated state
        await self.cg_ctrl.wait_for_gating(timeout=1000, units='ns')

        # Check final state
        state = self.cg_ctrl.get_current_state()
        if not state['is_gated']:
            self.log.error("Failed to return to gated state")
            return False

        self.log.info("Forced wakeup test passed")
        return True

    async def wait_for_gating_test(self):
        """
        Test the wait_for_gating and wait_for_idle APIs

        Returns:
            True if test passed
        """
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping wait_for_gating test in basic mode")
            return True

        self.log.info("Running wait_for_gating and wait_for_idle API test")

        # Reset and configure
        await self.reset_dut()
        await self.configure_controller(True, 4)

        # Start a background task to drive activity
        async def drive_activity():
            # Generate activity
            await self.drive_valid_pattern([1, 1, 0, 0, 0, 0, 0, 0, 0, 0], 'user')

        # Start the activity driver
        driver_task = cocotb.start_soon(drive_activity())

        # Wait for idle state
        idle_reached = await self.cg_ctrl.wait_for_idle(timeout=1000, units='ns')
        if not idle_reached:
            self.log.error("Failed to reach idle state")
            return False
        self.log.info("Reached idle state")

        # Wait for gating
        gating_reached = await self.cg_ctrl.wait_for_gating(timeout=1000, units='ns')
        if not gating_reached:
            self.log.error("Failed to reach gating state")
            return False
        self.log.info("Reached gating state")

        # Wait for driver to finish
        await driver_task

        # Final state check
        state = self.cg_ctrl.get_current_state()
        if not state['is_idle'] or not state['is_gated']:
            self.log.error(f"Unexpected final state: idle={state['is_idle']}, gated={state['is_gated']}")
            return False

        self.log.info("Wait for gating/idle API test passed")
        return True

    async def run_monitor_activity_test(self):
        """
        Test the monitor_activity API

        Returns:
            True if test passed
        """
        self.log.info("Running monitor_activity API test")

        # Reset and configure
        await self.reset_dut()
        await self.configure_controller(True, 8)

        # Drive a specific activity pattern
        async def drive_activity():
            # First burst
            self.user_valid.value = 1
            await self.wait_clocks('clk_in', 3)
            self.user_valid.value = 0
            await self.wait_clocks('clk_in', 5)

            # Second burst
            self.axi_valid.value = 1
            await self.wait_clocks('clk_in', 2)
            self.axi_valid.value = 0
            await self.wait_clocks('clk_in', 10)

        # Start the activity driver
        driver_task = cocotb.start_soon(drive_activity())

        # Simultaneously monitor activity
        stats = await self.cg_ctrl.monitor_activity(duration=300, units='ns')
        self.log.info(f"Activity monitoring results: {stats}")

        # Wait for driver to finish
        await driver_task

        # Basic verification of the stats
        if 'active_percent' not in stats:
            self.log.error("Missing active_percent in stats")
            return False

        if 'gated_percent' not in stats:
            self.log.error("Missing gated_percent in stats")
            return False

        # For higher test levels, verify the stats more carefully
        if self.TEST_LEVEL != 'basic':
            # We should have some active cycles (user + axi)
            if stats['active_cycles'] < 5:
                self.log.error(f"Too few active cycles: {stats['active_cycles']}")
                return False

            # We should have some user active cycles
            if stats['user_active_cycles'] < 3:
                self.log.error(f"Too few user active cycles: {stats['user_active_cycles']}")
                return False

            # We should have some axi active cycles
            if stats['axi_active_cycles'] < 2:
                self.log.error(f"Too few axi active cycles: {stats['axi_active_cycles']}")
                return False

        self.log.info("Monitor activity API test passed")
        return True

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}")

        all_passed = True

        # 1. Basic operation test
        self.log.info("1. Running basic operation test")
        basic_test_passed = await self.verify_basic_operation()
        if not basic_test_passed:
            self.log.error("Basic operation test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 2. Realistic workload test
        self.log.info("2. Running realistic workload test")
        workload_test_passed = await self.run_realistic_workload_test()
        if not workload_test_passed:
            self.log.error("Realistic workload test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 3. Idle count sweep test
        self.log.info("3. Running idle count sweep test")
        idle_count_test_passed = await self.run_idle_count_sweep_test()
        if not idle_count_test_passed:
            self.log.error("Idle count sweep test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # Skip the following tests in basic mode
        if self.TEST_LEVEL == 'basic':
            return all_passed

        # 4. Forced wakeup test
        self.log.info("4. Running forced wakeup test")
        wakeup_test_passed = await self.run_forced_wakeup_test()
        if not wakeup_test_passed:
            self.log.error("Forced wakeup test failed")
            all_passed = False
            if self.TEST_LEVEL == 'medium':
                return all_passed

        # 5. Wait for gating test
        self.log.info("5. Running wait for gating test")
        wait_test_passed = await self.wait_for_gating_test()
        if not wait_test_passed:
            self.log.error("Wait for gating test failed")
            all_passed = False
            if self.TEST_LEVEL == 'medium':
                return all_passed

        # 6. Monitor activity test
        self.log.info("6. Running monitor activity test")
        monitor_test_passed = await self.run_monitor_activity_test()
        if not monitor_test_passed:
            self.log.error("Monitor activity test failed")
            all_passed = False

        return all_passed


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = AmbaClockGateCtrlTB(dut)

    # Start clock with configured period
    await tb.start_clock('clk_in', tb.CLK_PERIOD_NS, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


@pytest.mark.parametrize("params", [
    # Test with different configurations
    {'CG_IDLE_COUNT_WIDTH':  4, 'clk_period_ns': 10, 'test_level': 'basic'},
    # {'CG_IDLE_COUNT_WIDTH':  8, 'clk_period_ns': 10, 'test_level': 'medium'},
    # {'CG_IDLE_COUNT_WIDTH': 16, 'clk_period_ns': 10, 'test_level': 'full'},
    # # Different clock frequencies
    # {'CG_IDLE_COUNT_WIDTH':  4, 'clk_period_ns': 5,  'test_level': 'basic'},
    # {'CG_IDLE_COUNT_WIDTH':  8, 'clk_period_ns': 20, 'test_level': 'basic'},
    # {'CG_IDLE_COUNT_WIDTH': 16, 'clk_period_ns': 50, 'test_level': 'basic'},
])
def test_amba_clock_gate_ctrl(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba_shared':'rtl/amba/shared',
         'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "amba_clock_gate_ctrl"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # Create a human-readable test identifier
    t_clk = params['clk_period_ns']
    t_name = params['test_level']
    t_icw = params['CG_IDLE_COUNT_WIDTH']
    test_name_plus_params = f"test_{worker_id}_{dut_name}_clk{t_clk}_icw{t_icw}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["CG_IDLE_COUNT_WIDTH"]}

    # Prepare environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),  # str(seed),
        'TEST_LEVEL': params['test_level'],
        'CLK_PERIOD_NS': str(params['clk_period_ns'])
    }

    # Calculate timeout based on clock period
    timeout_factor = max(1.0, t_clk / 10) * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
            "--trace",
            
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace",  # Tell Verilator to use VCD
            
            "--trace-depth", "99",
    ]

    plusargs = [
            "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
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
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
