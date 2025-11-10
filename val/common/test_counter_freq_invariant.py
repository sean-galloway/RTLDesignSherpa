# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_counter_freq_invariant
# Purpose: Test runner for counter_freq_invariant module
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for counter_freq_invariant module.

This module provides pytest test functions for validating a frequency-invariant
counter that generates microsecond ticks independent of input clock frequency.

Test Scenarios:
- Programming model (sync_reset_n control)
- Synchronous reset functionality
- Frequency sweep (100MHz to 2GHz)
- Microsecond tick generation
- Counter sequence verification

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (8-bit counter)
    FUNC: 2 tests (~5 min) - functional coverage - DEFAULT
    FULL: 3 tests (~10 min) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width = 1 test
    FUNC: 2 widths = 2 tests (8, 16-bit)
    FULL: 3 widths = 3 tests (8, 16, 24-bit)
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Division factor mapping for each frequency selection value (microsecond-based)
# Each value represents clock cycles needed for 1 microsecond
FACTOR_MAP = {
    # 100-200 MHz range
    0:   100,    # 100MHz   -> 100 cycles/μs
    1:   105,    # 105MHz   -> 105 cycles/μs
    2:   110,    # 110MHz   -> 110 cycles/μs
    3:   115,    # 115MHz   -> 115 cycles/μs
    4:   120,    # 120MHz   -> 120 cycles/μs
    5:   125,    # 125MHz   -> 125 cycles/μs
    6:   130,    # 130MHz   -> 130 cycles/μs
    7:   135,    # 135MHz   -> 135 cycles/μs
    8:   140,    # 140MHz   -> 140 cycles/μs
    9:   145,    # 145MHz   -> 145 cycles/μs
    10:  150,    # 150MHz   -> 150 cycles/μs
    11:  160,    # 160MHz   -> 160 cycles/μs
    12:  170,    # 170MHz   -> 170 cycles/μs
    13:  180,    # 180MHz   -> 180 cycles/μs
    14:  190,    # 190MHz   -> 190 cycles/μs
    15:  200,    # 200MHz   -> 200 cycles/μs

    # 200-500 MHz range
    16:  220,    # 220MHz   -> 220 cycles/μs
    17:  240,    # 240MHz   -> 240 cycles/μs
    18:  250,    # 250MHz   -> 250 cycles/μs
    19:  260,    # 260MHz   -> 260 cycles/μs
    20:  280,    # 280MHz   -> 280 cycles/μs
    21:  300,    # 300MHz   -> 300 cycles/μs
    22:  320,    # 320MHz   -> 320 cycles/μs
    23:  340,    # 340MHz   -> 340 cycles/μs
    24:  360,    # 360MHz   -> 360 cycles/μs
    25:  380,    # 380MHz   -> 380 cycles/μs
    26:  400,    # 400MHz   -> 400 cycles/μs
    27:  420,    # 420MHz   -> 420 cycles/μs
    28:  440,    # 440MHz   -> 440 cycles/μs
    29:  460,    # 460MHz   -> 460 cycles/μs
    30:  480,    # 480MHz   -> 480 cycles/μs
    31:  500,    # 500MHz   -> 500 cycles/μs

    # 500MHz-1GHz range
    32:  520,    # 520MHz   -> 520 cycles/μs
    33:  540,    # 540MHz   -> 540 cycles/μs
    34:  560,    # 560MHz   -> 560 cycles/μs
    35:  580,    # 580MHz   -> 580 cycles/μs
    36:  600,    # 600MHz   -> 600 cycles/μs
    37:  620,    # 620MHz   -> 620 cycles/μs
    38:  640,    # 640MHz   -> 640 cycles/μs
    39:  660,    # 660MHz   -> 660 cycles/μs
    40:  680,    # 680MHz   -> 680 cycles/μs
    41:  700,    # 700MHz   -> 700 cycles/μs
    42:  750,    # 750MHz   -> 750 cycles/μs
    43:  800,    # 800MHz   -> 800 cycles/μs
    44:  850,    # 850MHz   -> 850 cycles/μs
    45:  900,    # 900MHz   -> 900 cycles/μs
    46:  950,    # 950MHz   -> 950 cycles/μs
    47:  1000,   # 1000MHz  -> 1000 cycles/μs

    # 1GHz-1.5GHz range
    48:  1050,   # 1050MHz  -> 1050 cycles/μs
    49:  1100,   # 1100MHz  -> 1100 cycles/μs
    50:  1150,   # 1150MHz  -> 1150 cycles/μs
    51:  1200,   # 1200MHz  -> 1200 cycles/μs
    52:  1250,   # 1250MHz  -> 1250 cycles/μs
    53:  1300,   # 1300MHz  -> 1300 cycles/μs
    54:  1350,   # 1350MHz  -> 1350 cycles/μs
    55:  1400,   # 1400MHz  -> 1400 cycles/μs
    56:  1450,   # 1450MHz  -> 1450 cycles/μs
    57:  1500,   # 1500MHz  -> 1500 cycles/μs

    # 1.5GHz-2GHz range
    58:  1550,   # 1550MHz  -> 1550 cycles/μs
    59:  1600,   # 1600MHz  -> 1600 cycles/μs
    60:  1650,   # 1650MHz  -> 1650 cycles/μs
    61:  1700,   # 1700MHz  -> 1700 cycles/μs
    62:  1750,   # 1750MHz  -> 1750 cycles/μs
    63:  1800,   # 1800MHz  -> 1800 cycles/μs
    64:  1850,   # 1850MHz  -> 1850 cycles/μs
    65:  1900,   # 1900MHz  -> 1900 cycles/μs
    66:  1950,   # 1950MHz  -> 1950 cycles/μs
    67:  2000,   # 2000MHz  -> 2000 cycles/μs
}

class CounterFreqConfig:
    """Configuration class for counter frequency tests"""
    def __init__(self, name, freq_sel_seq, expected_division_factors=None):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            freq_sel_seq: List of frequency selection values
            expected_division_factors: List of expected division factors (if None, will be calculated)
        """
        self.name = name
        self.freq_sel_seq = freq_sel_seq

        # Calculate expected division factors if not provided
        if expected_division_factors is None:
            self.expected_division_factors = []
            self.expected_division_factors.extend(
                self._get_division_factor(freq_sel) for freq_sel in freq_sel_seq
            )
        else:
            self.expected_division_factors = expected_division_factors

        # Initialize iterators
        self.reset_iterators()

    def reset_iterators(self):
        """Reset all iterators to the beginning of sequences"""
        self._freq_sel_iter = iter(self.freq_sel_seq)
        self._division_factor_iter = iter(self.expected_division_factors)

    def next_freq_sel(self):
        """Get next frequency selection value"""
        return next(self._freq_sel_iter)

    def next_division_factor(self):
        """Get next expected division factor"""
        return next(self._division_factor_iter)

    def _get_division_factor(self, freq_sel):
        """Get the expected division factor for a given frequency selection"""
        return FACTOR_MAP.get(freq_sel, 1000)  # Default to 1GHz if invalid

class CounterFreqInvariantTB(TBBase):
    """
    Testbench for the enhanced counter_freq_invariant module
    Features:
    - Microsecond-based frequency selection testing (100MHz to 2GHz)
    - Counter output verification
    - Tick signal monitoring (1MHz rate)
    - Frequency change verification
    - Synchronous reset testing
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.COUNTER_WIDTH = self.convert_to_int(os.environ.get('TEST_COUNTER_WIDTH', '16'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n
        self.sync_reset_n = self.dut.sync_reset_n

        # Log configuration
        self.log.info(f"Enhanced Counter Frequency Invariant TB initialized with COUNTER_WIDTH={self.COUNTER_WIDTH}")
        self.log.info(f"SEED={self.SEED}")
        self.log.info("Supports frequencies from 100MHz to 2GHz with microsecond tick generation")

        # Test completion flag
        self.done = False

        # Counter monitoring
        self.counter_changes = []
        self.tick_events = []
        self.current_freq_sel = 0
        self.current_division_factor = 1000

        # Calculate the rollover value
        self.counter_max = (2 ** self.COUNTER_WIDTH) - 1

    def _get_division_factor(self, freq_sel):
        """Get the expected division factor for a given frequency selection"""
        return FACTOR_MAP.get(freq_sel, 1000)  # Default to 1GHz if invalid

    async def reset_dut(self):
        """Reset the DUT using the asynchronous reset"""
        self.log.debug('Starting asynchronous reset_dut')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.sync_reset_n.value = 0  # Start with sync reset active (programming model)
        self.dut.freq_sel.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clk', 10)

        # Release async reset but keep sync reset active
        self.reset_n.value = 1
        await self.wait_clocks('clk', 5)

        # Clear monitoring data
        self.counter_changes.clear()
        self.tick_events.clear()

        self.log.debug('Ending asynchronous reset_dut (sync_reset_n still active)')

    async def sync_reset_dut(self):
        """Reset the DUT using the synchronous reset"""
        self.log.debug('Starting synchronous reset_dut')

        # Ensure async reset is inactive
        self.reset_n.value = 1

        # Apply synchronous reset
        self.sync_reset_n.value = 0

        # Hold sync reset for multiple cycles
        await self.wait_clocks('clk', 5)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        # Clear monitoring data
        self.counter_changes.clear()
        self.tick_events.clear()

        self.log.debug('Ending synchronous reset_dut')

    async def monitor_counter(self, num_cycles):
        """
        Monitor counter and tick signal for a number of cycles

        Args:
            num_cycles: Number of clock cycles to monitor

        Returns:
            Tuple of (counter_changes, tick_events)
        """
        self.log.info(f"Monitoring counter for {num_cycles} cycles with freq_sel={self.current_freq_sel} (div={self.current_division_factor})")

        # Clear previous data
        self.counter_changes.clear()
        self.tick_events.clear()

        # Initial values
        prev_counter = int(self.dut.o_counter.value)
        self.counter_changes.append((0, prev_counter))

        # Monitor for specified cycles
        for cycle in range(1, num_cycles + 1):
            await RisingEdge(self.clock)

            # Check counter value
            current_counter = int(self.dut.o_counter.value)
            if current_counter != prev_counter:
                self.counter_changes.append((cycle, current_counter))
                self.log.debug(f"Cycle {cycle}: Counter changed to {current_counter}")
                prev_counter = current_counter

            # Check tick signal
            if int(self.dut.tick.value) == 1:
                self.tick_events.append(cycle)
                self.log.debug(f"Cycle {cycle}: Tick detected")

            # For higher frequencies, we can stop early once we have enough data
            if len(self.counter_changes) > 20 and self.current_division_factor >= 1000:
                self.log.info(f"Collected enough data points ({len(self.counter_changes)}), stopping early")
                break

        # Provide a warning if we didn't get enough data
        if len(self.counter_changes) < 2:
            self.log.warning(f"Very few counter changes observed ({len(self.counter_changes)}) - may not be enough for verification")

        return self.counter_changes, self.tick_events

    def set_frequency_selection(self, freq_sel):
        """
        Set the frequency selection value and update the current division factor
        Following the programming model: set freq_sel, then activate sync_reset_n

        Args:
            freq_sel: Frequency selection value (0-67)
        """
        # Validate range
        if freq_sel < 0 or freq_sel > 67:
            time_ns = get_sim_time('ns')
            self.log.error(f"Invalid frequency selection: {freq_sel} @ {time_ns}ns")
            freq_sel = 47  # Default to 1GHz

        # Set sync reset active first (programming model)
        self.sync_reset_n.value = 0

        # Set the selection value
        self.dut.freq_sel.value = freq_sel
        self.current_freq_sel = freq_sel

        # Update the current division factor
        self.current_division_factor = self._get_division_factor(freq_sel)

        # Calculate expected frequency
        expected_freq_mhz = self.current_division_factor  # Since division factor = MHz for microsecond timing

        self.log.info(f"Set frequency selection to {freq_sel} (division factor: {self.current_division_factor}, freq: {expected_freq_mhz}MHz)")

    async def activate_frequency(self):
        """
        Activate the configured frequency by releasing sync_reset_n
        """
        # Release sync reset to activate the frequency
        self.sync_reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        self.log.info(f"Activated frequency selection {self.current_freq_sel}")

    def verify_counter_changes(self, counter_changes, expected_division_factor):
        """
        Verify that counter changes occur at the expected intervals (microsecond rate)

        Args:
            counter_changes: List of (cycle, value) tuples
            expected_division_factor: Expected division factor (cycles per microsecond)

        Returns:
            True if verification passed, False otherwise
        """
        if len(counter_changes) < 3:
            self.log.warning(f"Too few counter changes to verify: {len(counter_changes)}")
            return False

        # Check intervals between counter changes
        # Skip the first interval as it might be affected by reset or frequency change
        intervals = []
        for i in range(2, len(counter_changes)):
            interval = counter_changes[i][0] - counter_changes[i-1][0]
            intervals.append(interval)
            self.log.debug(f"Interval {i-1}: {interval} cycles")

        # Calculate average interval
        avg_interval = sum(intervals) / len(intervals)

        # Calculate standard deviation to check consistency
        if len(intervals) >= 2:
            variance = sum((x - avg_interval) ** 2 for x in intervals) / len(intervals)
            std_dev = variance ** 0.5
            rel_std_dev = (std_dev / avg_interval) * 100 if avg_interval else 0
            self.log.info(f"Interval std deviation: {std_dev:.2f} cycles ({rel_std_dev:.1f}%)")

            # High variation indicates inconsistent timing
            if rel_std_dev > 15 and expected_division_factor > 100:
                self.log.warning(f"High variation in counter intervals: {rel_std_dev:.1f}%")

        # Tolerance for microsecond-based timing
        # Lower frequencies (higher division factors) get more tolerance
        if expected_division_factor <= 200:
            tolerance = 0.05  # 5% for low frequencies
        elif expected_division_factor <= 500:
            tolerance = 0.08  # 8% for medium frequencies
        elif expected_division_factor <= 1000:
            tolerance = 0.10  # 10% for high frequencies
        else:
            tolerance = 0.12  # 12% for very high frequencies

        min_acceptable = expected_division_factor * (1 - tolerance)
        max_acceptable = expected_division_factor * (1 + tolerance)
        time_ns = get_sim_time('ns')

        self.log.info(f"Average interval: {avg_interval:.2f}, Expected: {expected_division_factor} " +
                        f"(range: {min_acceptable:.2f} - {max_acceptable:.2f})")

        if min_acceptable <= avg_interval <= max_acceptable:
            self.log.info("Counter interval verification passed")
            return True
        else:
            self.log.error(f"Counter interval verification failed: {avg_interval:.2f} not within " +
                            f"{min_acceptable:.2f} - {max_acceptable:.2f} @ {time_ns}ns")
            return False

    def verify_counter_sequence(self, counter_changes):
        """
        Verify that counter values follow the expected sequence

        Args:
            counter_changes: List of (cycle, value) tuples

        Returns:
            True if verification passed, False otherwise
        """
        if len(counter_changes) < 2:
            self.log.warning("Too few counter changes to verify sequence")
            return False

        # Extract just the counter values and their cycle times
        values_with_cycles = list(counter_changes)

        # Check for sequence errors
        errors = 0
        error_details = []

        # Analyze segments of the counter sequence
        segments = []
        current_segment = [values_with_cycles[0]]

        for i in range(1, len(values_with_cycles)):
            cycle, value = values_with_cycles[i]
            prev_cycle, prev_value = values_with_cycles[i-1]
            cycle_diff = cycle - prev_cycle

            # If the cycle difference is much larger than usual, this might be
            # due to a frequency change or monitoring gap
            if i > 1:
                prev_cycle_diff = values_with_cycles[i-1][0] - values_with_cycles[i-2][0]
                if cycle_diff > 3 * prev_cycle_diff and prev_cycle_diff > 0:
                    # Large gap detected, end current segment and start a new one
                    segments.append(current_segment)
                    current_segment = [(cycle, value)]
                    continue

            # Check if the value follows the expected sequence
            expected_value = (prev_value + 1) & self.counter_max

            if value != expected_value and (prev_value != self.counter_max or value != 0):
                errors += 1
                error_details.append((i, prev_value, value, expected_value))

                # If we detect a sequence error, end the current segment
                segments.append(current_segment)
                current_segment = [(cycle, value)]
                continue

            # Add this value to the current segment
            current_segment.append((cycle, value))

        # Add the last segment
        if current_segment:
            segments.append(current_segment)

        # Log information about the segments
        self.log.info(f"Counter sequence analyzed in {len(segments)} segments")

        # Report any errors
        if errors > 0:
            time_ns = get_sim_time('ns')
            self.log.error(f"Counter sequence verification failed: {errors} errors @ {time_ns}ns")
            for idx, prev, curr, exp in error_details:
                self.log.error(f"  Index {idx}: {prev} -> {curr}, expected {exp}")
            return False
        else:
            self.log.info("Counter sequence verification passed")
            return True

    def verify_tick_signal(self, tick_events, counter_changes):
        """
        Verify that tick signal occurs at the correct times (every microsecond)

        Args:
            tick_events: List of cycle numbers when tick was high
            counter_changes: List of (cycle, value) tuples

        Returns:
            True if verification passed, False otherwise
        """
        if not tick_events:
            self.log.info("No tick events recorded - this might be expected for short monitoring periods")
            return True

        # In the updated RTL, tick occurs every microsecond when prescaler is done
        # and also when counter reaches maximum value
        self.log.info(f"Recorded {len(tick_events)} tick events: {tick_events}")

        # For microsecond timing, we expect ticks every division_factor cycles
        expected_tick_interval = self.current_division_factor

        if len(tick_events) >= 2:
            # Check intervals between tick events
            tick_intervals = []
            for i in range(1, len(tick_events)):
                interval = tick_events[i] - tick_events[i-1]
                tick_intervals.append(interval)
                self.log.debug(f"Tick interval {i}: {interval} cycles")

            # Calculate average tick interval
            avg_tick_interval = sum(tick_intervals) / len(tick_intervals)

            # Allow some tolerance for tick timing
            tolerance = 0.15  # 15% tolerance
            min_acceptable = expected_tick_interval * (1 - tolerance)
            max_acceptable = expected_tick_interval * (1 + tolerance)

            self.log.info(f"Average tick interval: {avg_tick_interval:.2f}, Expected: {expected_tick_interval} " +
                            f"(range: {min_acceptable:.2f} - {max_acceptable:.2f})")

            if min_acceptable <= avg_tick_interval <= max_acceptable:
                self.log.info("Tick signal timing verification passed")
                return True
            else:
                time_ns = get_sim_time('ns')
                self.log.error(f"Tick signal timing verification failed @ {time_ns}ns")
                return False
        else:
            self.log.info("Only one tick event recorded - timing verification skipped")
            return True

    async def run_sync_reset_test(self):
        """
        Test the synchronous reset functionality with programming model

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing synchronous reset functionality ===")

        # Reset for clean state
        await self.reset_dut()

        # Set a moderate frequency (500MHz)
        freq_sel = 31  # 500MHz
        self.set_frequency_selection(freq_sel)
        await self.activate_frequency()

        # Wait for counter to start incrementing
        await self.wait_clocks('clk', 1000)

        # Capture counter value before sync reset
        counter_before = int(self.dut.o_counter.value)
        self.log.info(f"Counter value before sync reset: {counter_before}")

        # Apply synchronous reset (following programming model)
        self.sync_reset_n.value = 0

        # Wait one cycle for the sync reset to propagate
        await self.wait_clocks('clk', 1)

        # Check counter immediately after sync reset assertion
        counter_immediate = int(self.dut.o_counter.value)
        tick_immediate = int(self.dut.tick.value)
        self.log.info(f"Counter immediately after sync_reset_n=0: {counter_immediate}")
        self.log.info(f"Tick immediately after sync_reset_n=0: {tick_immediate}")

        # Wait a few more cycles to ensure reset is stable
        await self.wait_clocks('clk', 4)

        # Capture counter value during sync reset (should be stable at 0)
        counter_during = int(self.dut.o_counter.value)
        tick_during = int(self.dut.tick.value)
        self.log.info(f"Counter value during sync reset: {counter_during}")
        self.log.info(f"Tick value during sync reset: {tick_during}")

        # Verify counter and tick are held at 0 during sync reset
        sync_reset_effective = (counter_during == 0 and tick_during == 0)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Wait one cycle for sync reset release to propagate
        await self.wait_clocks('clk', 1)

        # Check counter immediately after sync reset release
        counter_after_release = int(self.dut.o_counter.value)
        tick_after_release = int(self.dut.tick.value)
        self.log.info(f"Counter immediately after sync_reset_n=1: {counter_after_release}")
        self.log.info(f"Tick immediately after sync_reset_n=1: {tick_after_release}")

        # Wait a bit for the prescaler to stabilize
        await self.wait_clocks('clk', 10)

        # Check initial state after sync reset release
        counter_initial = int(self.dut.o_counter.value)
        self.log.info(f"Counter value after stabilization: {counter_initial}")

        # Wait for counter to start incrementing again
        await self.wait_clocks('clk', 1000)

        # Monitor counter behavior after sync reset
        counter_changes, tick_events = await self.monitor_counter(2000)

        # Verify counter is incrementing correctly after sync reset
        counter_restart_ok = len(counter_changes) > 1
        sequence_ok = self.verify_counter_sequence(counter_changes)

        # Additional check: verify counter is incrementing at correct rate
        timing_ok = True
        if len(counter_changes) >= 3:
            timing_ok = self.verify_counter_changes(counter_changes, self.current_division_factor)

        # Return overall test status
        test_passed = sync_reset_effective and counter_restart_ok and sequence_ok and timing_ok

        if test_passed:
            self.log.info("Synchronous reset test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Synchronous reset test failed @ {time_ns}ns")

            if not sync_reset_effective:
                self.log.error(f"Counter/tick not held at 0 during sync reset (counter: {counter_during}, tick: {tick_during})")
            if not counter_restart_ok:
                self.log.error("Counter did not restart incrementing after sync reset")
            if not sequence_ok:
                self.log.error("Counter sequence incorrect after sync reset")
            if not timing_ok:
                self.log.error("Counter timing incorrect after sync reset")

        return test_passed

    async def run_frequency_sweep_test(self):
        """
        Test multiple frequencies to verify microsecond timing

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing frequency sweep (microsecond timing) ===")

        # Test a representative set of frequencies
        test_frequencies = [
            0,   # 100MHz
            15,  # 200MHz
            31,  # 500MHz
            47,  # 1000MHz (1GHz)
            57,  # 1500MHz
            67,  # 2000MHz (2GHz)
        ]

        all_passed = True

        for freq_sel in test_frequencies:
            self.log.info(f"--- Testing frequency selection {freq_sel} ---")

            # Reset and configure frequency
            await self.reset_dut()
            self.set_frequency_selection(freq_sel)
            await self.activate_frequency()

            # Calculate cycles needed to see counter changes
            division_factor = self._get_division_factor(freq_sel)
            monitor_cycles = min(division_factor * 10, 10000)  # Monitor for up to 10 microseconds

            self.log.info(f"Monitoring {monitor_cycles} cycles for {division_factor} cycles/μs")

            # Monitor counter behavior
            counter_changes, tick_events = await self.monitor_counter(monitor_cycles)

            # Verify timing
            if len(counter_changes) >= 3:
                timing_ok = self.verify_counter_changes(counter_changes, division_factor)
                sequence_ok = self.verify_counter_sequence(counter_changes)
                tick_ok = self.verify_tick_signal(tick_events, counter_changes)

                freq_passed = timing_ok and sequence_ok and tick_ok

                if not freq_passed:
                    self.log.error(f"Frequency {freq_sel} test failed")
                    all_passed = False
                else:
                    self.log.info(f"Frequency {freq_sel} test passed")
            else:
                self.log.warning(f"Insufficient data for frequency {freq_sel} verification")

        if all_passed:
            self.log.info("Frequency sweep test passed")
        else:
            self.log.error("Frequency sweep test failed")

        return all_passed

    async def run_programming_model_test(self):
        """
        Test the programming model: sync_reset_n=0 by default, set freq_sel, then sync_reset_n=1

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing programming model ===")

        # Reset for clean state
        await self.reset_dut()

        # Verify that sync_reset_n=0 keeps counter at 0
        self.sync_reset_n.value = 0
        self.dut.freq_sel.value = 47  # 1GHz
        await self.wait_clocks('clk', 100)

        counter_during_reset = int(self.dut.o_counter.value)
        tick_during_reset = int(self.dut.tick.value)

        # Counter should be 0 and tick should be 0 during reset
        reset_holds_counter = (counter_during_reset == 0)
        reset_holds_tick = (tick_during_reset == 0)

        self.log.info(f"During sync_reset_n=0: counter={counter_during_reset}, tick={tick_during_reset}")

        # Now activate by setting sync_reset_n=1
        self.sync_reset_n.value = 1
        await self.wait_clocks('clk', 2000)

        # Monitor to verify operation
        counter_changes, tick_events = await self.monitor_counter(2000)

        # Verify counter starts operating
        counter_operating = len(counter_changes) > 1

        # Verify tick signal is generated
        tick_operating = len(tick_events) > 0

        self.log.info(f"After sync_reset_n=1: {len(counter_changes)} counter changes, {len(tick_events)} tick events")

        # Test changing frequency while running
        self.log.info("Testing frequency change during operation")

        # Change frequency (this should trigger internal reset)
        old_freq = 47
        new_freq = 15  # 200MHz

        self.set_frequency_selection(new_freq)
        await self.activate_frequency()

        # Monitor new frequency operation
        counter_changes_new, tick_events_new = await self.monitor_counter(1000)

        # Verify new frequency works
        new_freq_operating = len(counter_changes_new) > 1

        # Overall test result
        test_passed = (reset_holds_counter and reset_holds_tick and
                      counter_operating and tick_operating and new_freq_operating)

        if test_passed:
            self.log.info("Programming model test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Programming model test failed @ {time_ns}ns")

            if not reset_holds_counter:
                self.log.error("sync_reset_n=0 did not hold counter at 0")
            if not reset_holds_tick:
                self.log.error("sync_reset_n=0 did not hold tick at 0")
            if not counter_operating:
                self.log.error("Counter did not operate after sync_reset_n=1")
            if not tick_operating:
                self.log.error("Tick signal not generated after sync_reset_n=1")
            if not new_freq_operating:
                self.log.error("Counter did not operate correctly after frequency change")

        return test_passed

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def counter_freq_invariant_enhanced_test(dut):
    """Test enhanced frequency invariant counter with microsecond timing"""
    tb = CounterFreqInvariantTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Start the clock (1ns period = 1GHz for testing)
    print('Starting clk')
    await tb.start_clock('clk', 1, 'ns')

    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    try:
        print('# Test 1: Programming model test')
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Test 1: Programming model test @ {time_ns}ns ===")
        passed = await tb.run_programming_model_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Programming model test failed @ {time_ns}ns"

        print('# Test 2: Synchronous reset test')
        tb.log.info("=== Test 2: Synchronous reset test ===")
        passed = await tb.run_sync_reset_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Synchronous reset test failed @ {time_ns}ns"

        print('# Test 3: Frequency sweep test')
        tb.log.info("=== Test 3: Frequency sweep test ===")
        passed = await tb.run_frequency_sweep_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Frequency sweep test failed @ {time_ns}ns"

        await tb.wait_clocks('clk', 100)
        tb.log.info(f"Enhanced frequency invariant counter tests completed successfully @ {time_ns}ns")

    finally:
        # Set done flag
        tb.done = True
        # Wait for any pending tasks
        await tb.wait_clocks('clk', 10)

def generate_test_parameters():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (8-bit counter)
    REG_LEVEL=FUNC: 2 tests (functional coverage) - default
    REG_LEVEL=FULL: 3 tests (all configurations)

    Returns:
        List of counter widths
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # All available configurations
    all_widths = [
        8,   # 256 microseconds rollover
        16,  # 65.5 milliseconds rollover
        24,  # 16.7 seconds rollover
    ]

    if reg_level == 'GATE':
        # Quick smoke test: 8-bit only
        widths = [all_widths[0]]

    elif reg_level == 'FUNC':
        # Functional coverage: 8, 16-bit
        widths = all_widths[:2]

    else:  # FULL
        # Comprehensive: all widths
        widths = all_widths

    return widths

@pytest.mark.parametrize("counter_width", generate_test_parameters())
def test_counter_freq_invariant_enhanced(request, counter_width):
    """Run the enhanced test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "counter_freq_invariant"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_freq_invariant.f'
    )

    # Create a human readable test identifier
    cw_str = TBBase.format_dec(counter_width, 3)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_enhanced_cw{cw_str}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    rtl_parameters = {
        "COUNTER_WIDTH": str(counter_width),
        "PRESCALER_MAX": "2048"  # Support up to 2GHz
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'TEST_COUNTER_WIDTH': str(counter_width),
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
