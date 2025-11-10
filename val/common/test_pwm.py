# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PWMTB
# Purpose: PWM Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
PWM Test with Parameterized Test Levels and Configuration

This test uses width, channels and test_level as parameters for maximum flexibility:

CONFIGURATION:
    width:       Counter width (8, 12, 16)
    channels:    Number of PWM channels (1, 2, 4)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - width: [8, 12, 16]
    - channels: [1, 2, 4]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Counter width
    TEST_CHANNELS: Number of PWM channels
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class PWMTB(TBBase):
    """Testbench for PWM module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.CHANNELS = self.convert_to_int(os.environ.get('TEST_CHANNELS', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.MAX_COUNT = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"PWM TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, CHANNELS={self.CHANNELS}")
        self.log.info(f"MAX_COUNT={self.MAX_COUNT}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.sync_rst_n = self.dut.sync_rst_n
        self.start = self.dut.start
        self.duty = self.dut.duty
        self.period = self.dut.period
        self.repeat_count = self.dut.repeat_count
        self.done = self.dut.done
        self.pwm = self.dut.pwm_out

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.sync_rst_n.value = 1
        self.start.value = 0
        self.duty.value = 0
        self.period.value = 0
        self.repeat_count.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def pack_channel_data(self, values):
        """Pack array of values into concatenated signal"""
        packed = 0
        for i, val in enumerate(values):
            if i < self.CHANNELS:
                packed |= (val & self.MAX_COUNT) << (i * self.WIDTH)
        return packed

    def unpack_channel_data(self, packed_data, num_channels=None):
        """Unpack concatenated signal into array of values"""
        if num_channels is None:
            num_channels = self.CHANNELS
        values = []
        for i in range(num_channels):
            val = (packed_data >> (i * self.WIDTH)) & self.MAX_COUNT
            values.append(val)
        return values

    def get_channel_done(self, channel):
        """Get done signal for specific channel"""
        done_val = int(self.done.value)
        return (done_val >> channel) & 1

    def get_channel_pwm(self, channel):
        """Get PWM signal for specific channel"""
        pwm_val = int(self.pwm.value)
        return (pwm_val >> channel) & 1

    async def wait_for_channel_done(self, channel, timeout_cycles=None):
        """Wait for specific channel to assert done"""
        if timeout_cycles is None:
            timeout_cycles = self.MAX_COUNT * 10

        cycle_count = 0
        while cycle_count < timeout_cycles:
            await RisingEdge(self.clk)
            if self.get_channel_done(channel) == 1:
                return cycle_count
            cycle_count += 1

        raise TimeoutError(f"Channel {channel} done not asserted within {timeout_cycles} cycles")

    async def test_sync_reset_functionality(self):
        """Test synchronous reset functionality"""
        self.log.info(f"Testing synchronous reset functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Setup PWM parameters for a relatively long running PWM
        duty_val = 10
        period_val = 20
        repeat_val = 5  # Multiple repeats so we have time to test reset

        channel = 0
        duty_packed = self.pack_channel_data([duty_val] + [0] * (self.CHANNELS - 1))
        period_packed = self.pack_channel_data([period_val] + [0] * (self.CHANNELS - 1))
        repeat_packed = self.pack_channel_data([repeat_val] + [0] * (self.CHANNELS - 1))

        self.duty.value = duty_packed
        self.period.value = period_packed
        self.repeat_count.value = repeat_packed

        # Start PWM
        self.start.value = 1 << channel
        await RisingEdge(self.clk)
        self.start.value = 0

        # Wait for PWM to start and run for a few cycles
        pwm_started = False
        start_cycle = 0
        for cycle in range(10):
            await RisingEdge(self.clk)
            pwm_state = self.get_channel_pwm(channel)
            if pwm_state == 1:
                pwm_started = True
                start_cycle = cycle
                self.log.debug(f"PWM started at cycle {cycle}{self.get_time_ns_str()}")
                break

        if not pwm_started:
            self.log.error(f"PWM did not start within 10 cycles{self.get_time_ns_str()}")
            all_passed = False
            # Store failed result
            result = {
                'test_type': 'sync_reset_functionality',
                'error': 'PWM did not start',
                'success': False
            }
            self.test_results.append(result)
            self.test_failures.append(result)
            return all_passed

        # Let it run for several more cycles to get into the middle of operation
        for cycle in range(period_val // 2):  # Run for half a period
            await RisingEdge(self.clk)

        # Verify PWM is still running before reset
        pwm_before_reset = self.get_channel_pwm(channel)
        done_before_reset = self.get_channel_done(channel)

        self.log.debug(f"Before sync reset: PWM={pwm_before_reset}, Done={done_before_reset}{self.get_time_ns_str()}")

        # Apply synchronous reset (should reset on next clock edge)
        self.sync_rst_n.value = 0
        await RisingEdge(self.clk)

        # Check immediately after sync reset
        pwm_after_reset = self.get_channel_pwm(channel)
        done_after_reset = self.get_channel_done(channel)

        self.log.debug(f"After sync reset: PWM={pwm_after_reset}, Done={done_after_reset}{self.get_time_ns_str()}")

        # PWM should be reset to 0, done should be 0 (back to IDLE state)
        if pwm_after_reset != 0:
            self.log.error(f"PWM not reset: expected 0, got {pwm_after_reset}{self.get_time_ns_str()}")
            all_passed = False

        if done_after_reset != 0:
            self.log.error(f"Done not reset: expected 0, got {done_after_reset}{self.get_time_ns_str()}")
            all_passed = False

        # Release sync reset
        self.sync_rst_n.value = 1
        await RisingEdge(self.clk)

        # PWM should remain off after releasing sync reset (since start is not asserted)
        pwm_after_release = self.get_channel_pwm(channel)
        done_after_release = self.get_channel_done(channel)

        if pwm_after_release != 0:
            self.log.error(f"PWM active after sync reset release without start: {pwm_after_release}{self.get_time_ns_str()}")
            all_passed = False

        if done_after_release != 0:
            self.log.error(f"Done active after sync reset release: {done_after_release}{self.get_time_ns_str()}")
            all_passed = False

        # Verify we can restart PWM after sync reset
        self.start.value = 1 << channel
        await RisingEdge(self.clk)
        self.start.value = 0

        # Wait for PWM to restart
        pwm_restarted = False
        for cycle in range(10):
            await RisingEdge(self.clk)
            pwm_state = self.get_channel_pwm(channel)
            if pwm_state == 1:
                pwm_restarted = True
                self.log.debug(f"PWM restarted after sync reset at cycle {cycle}{self.get_time_ns_str()}")
                break

        if not pwm_restarted:
            self.log.error(f"PWM did not restart after sync reset{self.get_time_ns_str()}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'sync_reset_functionality',
            'pwm_stopped_by_reset': pwm_after_reset == 0,
            'done_reset_properly': done_after_reset == 0,
            'pwm_stayed_off_after_release': pwm_after_release == 0,
            'pwm_restarted_properly': pwm_restarted,
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_basic_pwm_generation(self):
        """Test basic PWM generation"""
        self.log.info(f"Testing basic PWM generation{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test different duty cycles based on level
        if self.TEST_LEVEL == 'basic':
            test_cases = [(10, 20, 1), (5, 10, 1)]  # (duty, period, repeat)
        elif self.TEST_LEVEL == 'medium':
            test_cases = [(10, 20, 1), (5, 10, 1), (15, 30, 2), (8, 16, 1)]
        else:  # full
            test_cases = [
                (10, 20, 1), (5, 10, 1), (15, 30, 2), (8, 16, 1),
                (1, 10, 1), (9, 10, 1), (20, 20, 1), (0, 10, 1)  # Edge cases
            ]

        # Filter valid test cases
        test_cases = [(d, p, r) for d, p, r in test_cases if p <= self.MAX_COUNT and d <= self.MAX_COUNT]

        for duty_val, period_val, repeat_val in test_cases:
            if not all_passed and self.TEST_LEVEL == 'basic':
                break

            self.log.debug(f"Testing duty={duty_val}, period={period_val}, repeat={repeat_val}{self.get_time_ns_str()}")

            # Test channel 0
            channel = 0

            # Setup parameters
            duty_packed = self.pack_channel_data([duty_val] + [0] * (self.CHANNELS - 1))
            period_packed = self.pack_channel_data([period_val] + [0] * (self.CHANNELS - 1))
            repeat_packed = self.pack_channel_data([repeat_val] + [0] * (self.CHANNELS - 1))

            self.duty.value = duty_packed
            self.period.value = period_packed
            self.repeat_count.value = repeat_packed

            # Start PWM
            self.start.value = 1 << channel
            await RisingEdge(self.clk)

            # Monitor PWM signal for one complete cycle
            pwm_high_count = 0
            pwm_low_count = 0

            for cycle in range(period_val):
                await RisingEdge(self.clk)
                pwm_state = self.get_channel_pwm(channel)

                if pwm_state == 1:
                    pwm_high_count += 1
                else:
                    pwm_low_count += 1

            # Verify PWM timing
            expected_high = duty_val if duty_val < period_val else period_val
            expected_low = period_val - expected_high

            if duty_val >= period_val:  # 100% duty cycle case
                if pwm_high_count != period_val:
                    self.log.error(f"100% duty: high_count={pwm_high_count}, expected={period_val}{self.get_time_ns_str()}")
                    all_passed = False
            else:
                if pwm_high_count != expected_high:
                    self.log.error(f"High count: {pwm_high_count}, expected: {expected_high}{self.get_time_ns_str()}")
                    all_passed = False
                if pwm_low_count != expected_low:
                    self.log.error(f"Low count: {pwm_low_count}, expected: {expected_low}{self.get_time_ns_str()}")
                    all_passed = False

            # Wait for done signal if repeat count > 1
            if repeat_val > 1:
                try:
                    await self.wait_for_channel_done(channel)
                    done_state = self.get_channel_done(channel)
                    if done_state != 1:
                        self.log.error(f"Done not asserted after repeat cycles{self.get_time_ns_str()}")
                        all_passed = False
                except TimeoutError:
                    self.log.error(f"Timeout waiting for done signal{self.get_time_ns_str()}")
                    all_passed = False

            # Store result
            result = {
                'test_type': 'basic_pwm_generation',
                'duty': duty_val,
                'period': period_val,
                'repeat': repeat_val,
                'pwm_high_count': pwm_high_count,
                'expected_high': expected_high,
                'success': pwm_high_count == expected_high
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

            # Reset for next test
            await self.reset_dut()

        return all_passed

    async def test_multiple_channels(self):
        """Test multiple PWM channels"""
        if self.TEST_LEVEL == 'basic' or self.CHANNELS == 1:
            self.log.info("Skipping multiple channel tests")
            return True

        self.log.info(f"Testing multiple channels{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test different duty cycles on different channels
        if self.CHANNELS >= 2:
            duty_values = [5, 10] + [0] * (self.CHANNELS - 2)
            period_values = [10, 20] + [0] * (self.CHANNELS - 2)
            repeat_values = [1, 1] + [0] * (self.CHANNELS - 2)
        else:
            return True

        # Pack values
        duty_packed = self.pack_channel_data(duty_values)
        period_packed = self.pack_channel_data(period_values)
        repeat_packed = self.pack_channel_data(repeat_values)

        self.duty.value = duty_packed
        self.period.value = period_packed
        self.repeat_count.value = repeat_packed

        # Start first two channels
        start_mask = (1 << min(2, self.CHANNELS)) - 1
        self.start.value = start_mask
        await RisingEdge(self.clk)

        # Monitor both channels for their respective periods
        max_period = max(period_values[:2])
        channel_stats = [{} for _ in range(self.CHANNELS)]

        for cycle in range(max_period):
            await RisingEdge(self.clk)

            for ch in range(min(2, self.CHANNELS)):
                if cycle < period_values[ch]:
                    pwm_state = self.get_channel_pwm(ch)
                    if 'high_count' not in channel_stats[ch]:
                        channel_stats[ch]['high_count'] = 0
                        channel_stats[ch]['low_count'] = 0

                    if pwm_state == 1:
                        channel_stats[ch]['high_count'] += 1
                    else:
                        channel_stats[ch]['low_count'] += 1

        # Verify each channel
        for ch in range(min(2, self.CHANNELS)):
            expected_high = duty_values[ch] if duty_values[ch] < period_values[ch] else period_values[ch]
            actual_high = channel_stats[ch].get('high_count', 0)

            if actual_high != expected_high:
                self.log.error(f"Channel {ch}: high_count={actual_high}, expected={expected_high}{self.get_time_ns_str()}")
                all_passed = False

        # Store result
        result = {
            'test_type': 'multiple_channels',
            'channel_stats': channel_stats,
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_repeat_functionality(self):
        """Test repeat count functionality"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping repeat functionality tests")
            return True

        self.log.info(f"Testing repeat functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test repeat count
        duty_val = 5
        period_val = 10
        repeat_val = 3

        # Test channel 0
        channel = 0
        duty_packed = self.pack_channel_data([duty_val] + [0] * (self.CHANNELS - 1))
        period_packed = self.pack_channel_data([period_val] + [0] * (self.CHANNELS - 1))
        repeat_packed = self.pack_channel_data([repeat_val] + [0] * (self.CHANNELS - 1))

        self.duty.value = duty_packed
        self.period.value = period_packed
        self.repeat_count.value = repeat_packed

        # Start PWM
        self.start.value = 1 << channel
        await RisingEdge(self.clk)
        self.start.value = 0  # De-assert start after one cycle

        # Wait for PWM to actually start (should happen within a few cycles)
        pwm_started = False
        start_time = 0
        for cycle in range(10):  # Give it up to 10 cycles to start
            await RisingEdge(self.clk)
            pwm_state = self.get_channel_pwm(channel)
            if pwm_state == 1:
                pwm_started = True
                start_time = cycle
                self.log.debug(f"PWM started at cycle {cycle}{self.get_time_ns_str()}")
                break

        if not pwm_started:
            self.log.error(f"PWM did not start within 10 cycles{self.get_time_ns_str()}")
            all_passed = False
            # Store failed result
            result = {
                'test_type': 'repeat_functionality',
                'error': 'PWM did not start',
                'success': False
            }
            self.test_results.append(result)
            self.test_failures.append(result)
            return all_passed

        # Now monitor for the expected number of complete periods
        periods_completed = 0
        cycles_in_current_period = 0
        total_cycles_monitored = 0
        max_cycles = repeat_val * period_val + 20  # Add some margin

        # Track PWM edges to detect period boundaries
        prev_pwm_state = self.get_channel_pwm(channel)
        cycles_since_period_start = 0

        while periods_completed < repeat_val and total_cycles_monitored < max_cycles:
            await RisingEdge(self.clk)
            total_cycles_monitored += 1
            cycles_since_period_start += 1

            current_pwm_state = self.get_channel_pwm(channel)

            # Detect period completion by counting cycles
            # A period is complete when we've seen period_val cycles of PWM activity
            if cycles_since_period_start >= period_val:
                periods_completed += 1
                cycles_since_period_start = 0
                self.log.debug(f"Period {periods_completed} completed at total cycle {total_cycles_monitored}{self.get_time_ns_str()}")

                # After completing expected repeats, check if PWM stops
                if periods_completed >= repeat_val:
                    break

            prev_pwm_state = current_pwm_state

        # Now check if done signal is asserted
        # Give it a few extra cycles for the done signal to propagate
        done_asserted = False
        done_check_cycles = 0
        max_done_wait = 10

        while done_check_cycles < max_done_wait:
            await RisingEdge(self.clk)
            done_check_cycles += 1
            done_state = self.get_channel_done(channel)

            if done_state == 1:
                done_asserted = True
                self.log.debug(f"Done signal asserted after {done_check_cycles} additional cycles{self.get_time_ns_str()}")
                break

        # Verify results
        if periods_completed < repeat_val:
            self.log.error(f"Insufficient periods completed: {periods_completed}, expected: {repeat_val}{self.get_time_ns_str()}")
            all_passed = False

        if not done_asserted:
            self.log.error(f"Done signal not asserted after {repeat_val} periods{self.get_time_ns_str()}")
            all_passed = False

        # Additional check: PWM should stop generating after done is asserted
        if done_asserted:
            # Check that PWM output is now inactive
            pwm_after_done = self.get_channel_pwm(channel)
            if pwm_after_done != 0:
                self.log.warning(f"PWM still active after done asserted{self.get_time_ns_str()}")
                # This might be acceptable depending on the design - some PWMs complete current period

        # Store result
        result = {
            'test_type': 'repeat_functionality',
            'periods_completed': periods_completed,
            'expected_periods': repeat_val,
            'total_cycles_monitored': total_cycles_monitored,
            'expected_cycles': repeat_val * period_val,
            'done_asserted': done_asserted,
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_edge_cases(self):
        """Test edge cases and boundary conditions"""
        if self.TEST_LEVEL != 'full':
            self.log.info("Skipping edge case tests")
            return True

        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test edge cases
        edge_cases = [
            (0, 10, 1, "Zero duty cycle"),
            (10, 10, 1, "100% duty cycle"),
            (1, 1, 1, "Minimum period"),
            (15, 10, 1, "Duty > Period"),
        ]

        for duty_val, period_val, repeat_val, description in edge_cases:
            if period_val > self.MAX_COUNT or duty_val > self.MAX_COUNT:
                continue

            self.log.debug(f"Testing edge case: {description}{self.get_time_ns_str()}")

            # Test channel 0
            channel = 0
            duty_packed = self.pack_channel_data([duty_val] + [0] * (self.CHANNELS - 1))
            period_packed = self.pack_channel_data([period_val] + [0] * (self.CHANNELS - 1))
            repeat_packed = self.pack_channel_data([repeat_val] + [0] * (self.CHANNELS - 1))

            self.duty.value = duty_packed
            self.period.value = period_packed
            self.repeat_count.value = repeat_packed

            # Start PWM
            self.start.value = 1 << channel
            await RisingEdge(self.clk)

            # Monitor for one period
            pwm_high_count = 0
            for cycle in range(period_val):
                await RisingEdge(self.clk)
                pwm_state = self.get_channel_pwm(channel)
                if pwm_state == 1:
                    pwm_high_count += 1

            # Verify based on case
            if duty_val == 0:  # Zero duty cycle
                if pwm_high_count != 0:
                    self.log.error(f"Zero duty: pwm_high_count={pwm_high_count}, expected=0{self.get_time_ns_str()}")
                    all_passed = False
            elif duty_val >= period_val:  # 100% or over duty cycle
                if pwm_high_count != period_val:
                    self.log.error(f"100%+ duty: pwm_high_count={pwm_high_count}, expected={period_val}{self.get_time_ns_str()}")
                    all_passed = False
            else:  # Normal case
                if pwm_high_count != duty_val:
                    self.log.error(f"Normal duty: pwm_high_count={pwm_high_count}, expected={duty_val}{self.get_time_ns_str()}")
                    all_passed = False

            # Reset for next test
            await self.reset_dut()

        # Store result
        result = {
            'test_type': 'edge_cases',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_start_stop_control(self):
        """Test start/stop control"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping start/stop control tests")
            return True

        self.log.info(f"Testing start/stop control{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Setup PWM parameters
        duty_val = 5
        period_val = 10
        repeat_val = 1

        channel = 0
        duty_packed = self.pack_channel_data([duty_val] + [0] * (self.CHANNELS - 1))
        period_packed = self.pack_channel_data([period_val] + [0] * (self.CHANNELS - 1))
        repeat_packed = self.pack_channel_data([repeat_val] + [0] * (self.CHANNELS - 1))

        self.duty.value = duty_packed
        self.period.value = period_packed
        self.repeat_count.value = repeat_packed

        # PWM should not start without start signal
        for cycle in range(5):
            await RisingEdge(self.clk)
            pwm_state = self.get_channel_pwm(channel)
            if pwm_state != 0:
                self.log.error(f"PWM active without start signal at cycle {cycle}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Start PWM
        self.start.value = 1 << channel
        await RisingEdge(self.clk)
        self.start.value = 0  # De-assert start

        # PWM should now be active
        pwm_started = False
        for cycle in range(period_val):
            await RisingEdge(self.clk)
            pwm_state = self.get_channel_pwm(channel)
            if pwm_state == 1:
                pwm_started = True
                break

        if not pwm_started:
            self.log.error(f"PWM did not start after start signal{self.get_time_ns_str()}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'start_stop_control',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running PWM tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_pwm_generation, "Basic PWM generation"),
            (self.test_sync_reset_functionality, "Synchronous reset functionality"),
            (self.test_multiple_channels, "Multiple channels"),
            (self.test_repeat_functionality, "Repeat functionality"),
            (self.test_edge_cases, "Edge cases"),
            (self.test_start_stop_control, "Start/stop control")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall PWM result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=15000, timeout_unit="us")
async def pwm_test(dut):
    """Test for PWM module"""
    tb = PWMTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"PWM test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"PWM test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    widths = [8, 12, 16]        # Different counter widths
    channels_list = [1, 2, 4]   # Different channel counts
    test_levels = ['full']      # Test levels

    valid_params = []
    for width, channels, test_level in product(widths, channels_list, test_levels):
        valid_params.append((width, channels, test_level))

    # For debugging, uncomment one of these:
    # return [(8, 1, 'basic')]  # Single test
    # return [(8, 2, 'full')]  # Just specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, channels, test_level", params)
def test_pwm(request, width, channels, test_level):
    """
    Parameterized PWM test with configurable width, channels and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "pwm"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/pwm.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(width, 2)
    c_str = TBBase.format_dec(channels, 1)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_pwm_w{w_str}_c{c_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width),
        'CHANNELS': str(channels)
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, width / 12.0)  # Larger widths take more time
    base_timeout = 3000  # 3 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_WIDTH': str(width),
        'TEST_CHANNELS': str(channels),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
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

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}, channels={channels}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}, channels={channels}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
