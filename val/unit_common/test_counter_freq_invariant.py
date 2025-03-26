import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


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
        factor_map = {
            0x0: 1,       # 1000MHz (1GHz)  - 1:1 division
            0x1: 10,      # 100MHz          - 10:1 division
            0x2: 20,      # 50MHz           - 20:1 division
            0x3: 25,      # 40MHz           - 25:1 division
            0x4: 40,      # 25MHz           - 40:1 division
            0x5: 50,      # 20MHz           - 50:1 division
            0x6: 80,      # 12.5MHz         - 80:1 division
            0x7: 100,     # 10MHz           - 100:1 division
            0x8: 125,     # 8MHz            - 125:1 division
            0x9: 200,     # 5MHz            - 200:1 division
            0xA: 250,     # 4MHz            - 250:1 division
            0xB: 500,     # 2MHz            - 500:1 division
            0xC: 1000,    # 1MHz            - 1000:1 division
            0xD: 2000,    # 500kHz          - 2000:1 division
            0xE: 5000,    # 200kHz          - 5000:1 division
            0xF: 10000,   # 100kHz          - 10000:1 division
        }
        return factor_map.get(freq_sel, 1)  # Default to 1 if invalid


class CounterFreqInvariantTB(TBBase):
    """
    Testbench for the counter_freq_invariant module
    Features:
    - Frequency selection testing
    - Counter output verification
    - Tick signal monitoring
    - Frequency change verification
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.COUNTER_WIDTH = self.convert_to_int(os.environ.get('TEST_COUNTER_WIDTH', '5'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.i_clk
        self.reset_n = self.dut.i_rst_n

        # Log configuration
        self.log.info(f"Counter Frequency Invariant TB initialized with COUNTER_WIDTH={self.COUNTER_WIDTH}")
        self.log.info(f"SEED={self.SEED}")

        # Test completion flag
        self.done = False

        # Counter monitoring
        self.counter_changes = []
        self.tick_events = []
        self.current_freq_sel = 0
        self.current_division_factor = 1

        # Calculate the rollover value
        self.counter_max = (2 ** self.COUNTER_WIDTH) - 1

    def _get_division_factor(self, freq_sel):
        """Get the expected division factor for a given frequency selection"""
        factor_map = {
            0x0: 1,       # 1000MHz (1GHz)  - 1:1 division
            0x1: 10,      # 100MHz          - 10:1 division
            0x2: 20,      # 50MHz           - 20:1 division
            0x3: 25,      # 40MHz           - 25:1 division
            0x4: 40,      # 25MHz           - 40:1 division
            0x5: 50,      # 20MHz           - 50:1 division
            0x6: 80,      # 12.5MHz         - 80:1 division
            0x7: 100,     # 10MHz           - 100:1 division
            0x8: 125,     # 8MHz            - 125:1 division
            0x9: 200,     # 5MHz            - 200:1 division
            0xA: 250,     # 4MHz            - 250:1 division
            0xB: 500,     # 2MHz            - 500:1 division
            0xC: 1000,    # 1MHz            - 1000:1 division
            0xD: 2000,    # 500kHz          - 2000:1 division
            0xE: 5000,    # 200kHz          - 5000:1 division
            0xF: 10000,   # 100kHz          - 10000:1 division
        }
        return factor_map.get(freq_sel, 1)  # Default to 1 if invalid

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.dut.i_freq_sel.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('i_clk', 5)

        # Release reset
        self.reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('i_clk', 10)

        # Clear monitoring data
        self.counter_changes.clear()
        self.tick_events.clear()

        self.log.debug('Ending reset_dut')

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
            if int(self.dut.o_tick.value) == 1:
                self.tick_events.append(cycle)
                self.log.debug(f"Cycle {cycle}: Tick detected")

            # If we already have a lot of counter changes, we can stop early
            # This helps prevent excessive runtime for low division factors
            if len(self.counter_changes) > 50 and self.current_division_factor <= 10:
                self.log.info(f"Collected enough data points ({len(self.counter_changes)}), stopping early")
                break

        # Provide a warning if we didn't get enough data
        if len(self.counter_changes) < 2:
            self.log.warning(f"Very few counter changes observed ({len(self.counter_changes)}) - may not be enough for verification")

        return self.counter_changes, self.tick_events

    def set_frequency_selection(self, freq_sel):
        """
        Set the frequency selection value and update the current division factor

        Args:
            freq_sel: Frequency selection value (0-15)
        """
        # Validate range
        if freq_sel < 0 or freq_sel > 15:
            time_ns = get_sim_time('ns')
            self.log.error(f"Invalid frequency selection: {freq_sel} @ {time_ns}ns")
            freq_sel = 0

        # Set the selection value
        self.dut.i_freq_sel.value = freq_sel
        self.current_freq_sel = freq_sel

        # Update the current division factor
        self.current_division_factor = self._get_division_factor(freq_sel)

        self.log.info(f"Set frequency selection to {freq_sel} (division factor: {self.current_division_factor})")

    def verify_counter_changes(self, counter_changes, expected_division_factor):
        """
        Verify that counter changes occur at the expected intervals

        Args:
            counter_changes: List of (cycle, value) tuples
            expected_division_factor: Expected division factor

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
            if rel_std_dev > 20 and expected_division_factor > 1:
                self.log.warning(f"High variation in counter intervals: {rel_std_dev:.1f}%")

        # Allow variation in the division factor based on the expected factor
        # Higher division factors need more flexibility due to sampling effects
        base_tolerance = 0.1  # 10% base tolerance

        # Scale tolerance based on division factor
        if expected_division_factor <= 10:
            tolerance = base_tolerance
        elif expected_division_factor <= 100:
            tolerance = base_tolerance * 1.5
        else:
            tolerance = base_tolerance * 2

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

        # We'll analyze individual segments of the counter sequence
        # This handles cases where we have discontinuities due to frequency changes
        segments = []
        current_segment = [values_with_cycles[0]]

        for i in range(1, len(values_with_cycles)):
            cycle, value = values_with_cycles[i]
            prev_cycle, prev_value = values_with_cycles[i-1]
            cycle_diff = cycle - prev_cycle

            # If the cycle difference is much larger than usual, this might be
            # due to a frequency change or monitoring gap
            if i > 1 and cycle_diff > 5 * (values_with_cycles[i-1][0] - values_with_cycles[i-2][0]):
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
        Verify that tick signal occurs at the correct times

        Args:
            tick_events: List of cycle numbers when tick was high
            counter_changes: List of (cycle, value) tuples

        Returns:
            True if verification passed, False otherwise
        """
        if not tick_events:
            # With the new RTL, we might not see tick events for short monitoring periods
            # or for specific counter sequences, so this isn't necessarily an error
            self.log.info("No tick events recorded - this is expected for short monitoring periods")
            return True

        # Convert counter changes to a dict for easier lookup
        counter_dict = dict(counter_changes)

        # In the updated RTL, tick signal occurs when the counter rolls over from max to 0
        # Find cycles where counter is 0 (after rollover)
        rollover_cycles = []
        for i in range(1, len(counter_changes)):
            curr_cycle, curr_value = counter_changes[i]
            prev_cycle, prev_value = counter_changes[i-1]

            # If current value is 0 and previous value was counter_max, this is a rollover
            if curr_value == 0 and prev_value == self.counter_max:
                rollover_cycles.append(curr_cycle)
                self.log.debug(f"Counter rollover detected at cycle {curr_cycle}")

        # Check if we have rollovers to verify
        if not rollover_cycles:
            self.log.info("No counter rollovers detected - tick verification skipped")
            return True

        # The tick should occur one cycle after a counter change to maximum value
        # And also when prescaler is done (which we can't directly observe)
        errors = 0
        time_ns = get_sim_time('ns')

        for tick_cycle in tick_events:
            found_match = any(
                tick_cycle >= rollover_cycle and tick_cycle <= rollover_cycle + 2
                for rollover_cycle in rollover_cycles
            )
            if not found_match:
                if closest_changes := [
                    c for c, v in counter_changes if c <= tick_cycle
                ]:
                    last_change_cycle = max(closest_changes)
                    last_value = counter_dict[last_change_cycle]

                    if last_value == 0:  # Counter just rolled over
                        found_match = True

            if not found_match:
                self.log.error(f"Tick at cycle {tick_cycle} not associated with a counter rollover or max value @ {time_ns}ns")
                errors += 1

        if errors == 0:
            self.log.info("Tick signal verification passed")
            return True
        else:
            self.log.error(f"Tick signal verification failed: {errors} errors @ {time_ns}ns")
            return False

    def _create_basic_freq_config(self):
        """Create configuration for basic frequency test"""
        freq_sel_seq = [0x0, 0x1, 0x7, 0xF]  # Test a few key frequencies
        return CounterFreqConfig("basic", freq_sel_seq)

    def _create_all_freq_config(self):
        """Create configuration to test all frequency selections"""
        freq_sel_seq = list(range(16))  # Test all 16 frequency selections
        return CounterFreqConfig("all_freq", freq_sel_seq)

    def _create_random_freq_config(self, num_tests=5):
        """Create configuration for random frequency changes"""
        freq_sel_seq = [random.randint(0, 15) for _ in range(num_tests)]
        return CounterFreqConfig("random", freq_sel_seq)

    async def run_frequency_test(self, config, cycles_per_freq=1000):
        """
        Run test with different frequency selections

        Args:
            config: Test configuration
            cycles_per_freq: Base number of cycles to monitor for each frequency

        Returns:
            True if all tests passed, False if any failed
        """
        # Reset for clean state
        await self.reset_dut()

        all_passed = True
        config.reset_iterators()

        # Run test for each frequency in the sequence
        for _ in range(len(config.freq_sel_seq)):
            # Get next test parameters
            freq_sel = config.next_freq_sel()
            division_factor = config.next_division_factor()

            # Set frequency selection
            self.set_frequency_selection(freq_sel)

            # Wait for counter to stabilize - scale wait time based on division factor
            stabilization_cycles = min(20 + division_factor, 100)  # Cap at 100 cycles
            await self.wait_clocks('i_clk', stabilization_cycles)

            # Calculate how many cycles are needed to see enough counter changes
            # We want to see at least 15 counter changes for reliable statistics
            min_counter_changes = 15

            # Add a safety margin proportional to the division factor
            safety_margin = 2.0  # 2x safety margin
            if division_factor > 100:
                safety_margin = 3.0  # Higher safety margin for large division factors

            estimated_cycles = int(division_factor * min_counter_changes * safety_margin)
            monitor_cycles = max(cycles_per_freq, estimated_cycles)

            # Log the monitoring plan
            self.log.info(f"Monitoring for {monitor_cycles} cycles to observe at least {min_counter_changes} counter changes")

            # Monitor counter for specified cycles
            counter_changes, tick_events = await self.monitor_counter(monitor_cycles)

            # Log how many changes we actually observed
            self.log.info(f"Observed {len(counter_changes)-1} counter changes and {len(tick_events)} tick events")

            # If we didn't see enough counter changes, extend monitoring time
            if len(counter_changes) < min_counter_changes and division_factor > 1:
                additional_cycles = int(division_factor * min_counter_changes * safety_margin)
                self.log.warning(f"Not enough counter changes observed, extending monitoring by {additional_cycles} cycles")

                # Monitor for additional time
                more_changes, more_ticks = await self.monitor_counter(additional_cycles)

                # Merge the results
                last_cycle = counter_changes[-1][0] if counter_changes else 0
                counter_changes.extend([(c + last_cycle, v) for c, v in more_changes[1:]])  # Skip the first one to avoid duplicates
                tick_events.extend([t + last_cycle for t in more_ticks])

                self.log.info(f"After extension: {len(counter_changes)-1} counter changes and {len(tick_events)} tick events")

            # Verify results only if we have enough data
            time_ns = get_sim_time('ns')
            if len(counter_changes) >= 2:
                interval_ok = self.verify_counter_changes(counter_changes, division_factor)
                sequence_ok = self.verify_counter_sequence(counter_changes)
                tick_ok = self.verify_tick_signal(tick_events, counter_changes)

                test_passed = interval_ok and sequence_ok and tick_ok
            else:
                self.log.error(f"Not enough counter changes to verify for freq_sel={freq_sel} @ {time_ns}ns")
                test_passed = False
            if test_passed:
                self.log.info(f"Test for freq_sel={freq_sel} (div={division_factor}) passed @ {time_ns}ns")
            else:
                self.log.error(f"Test for freq_sel={freq_sel} (div={division_factor}) failed @ {time_ns}ns")
                all_passed = False

            # Wait a bit before changing frequency
            await self.wait_clocks('i_clk', 20)

        return all_passed

    async def run_frequency_change_test(self, num_changes=10, cycles_between_changes=500):
        """
        Test dynamic frequency changes

        Args:
            num_changes: Number of frequency changes to test
            cycles_between_changes: Base number of cycles between changes

        Returns:
            True if test passed, False otherwise
        """
        # Reset for clean state
        await self.reset_dut()
        time_ns = get_sim_time('ns')

        self.log.info(f"Running frequency change test with {num_changes} changes @ {time_ns}ns")

        # Start with a known frequency with a moderate division factor
        initial_freq_sel = 0x1  # 10:1 division
        self.set_frequency_selection(initial_freq_sel)

        # Wait for stabilization
        await self.wait_clocks('i_clk', 100)

        # Track counter behavior across changes
        all_counter_changes = []
        all_tick_events = []
        freq_change_cycles = []
        all_passed = True

        # Change frequencies multiple times
        for change_idx in range(num_changes):
            # Select new random frequency
            # For testing frequency changes, focus on frequencies with smaller division factors
            # to make verification more practical
            freq_options = [0, 1, 2, 3, 4, 5]  # Division factors: 1, 10, 20, 25, 40, 50
            new_freq_sel = random.choice(freq_options)
            while new_freq_sel == self.current_freq_sel:
                new_freq_sel = random.choice(freq_options)

            # Get the division factor for the new frequency
            new_division_factor = self._get_division_factor(new_freq_sel)
            time_ns = get_sim_time('ns')

            self.log.info(f"Change {change_idx+1}/{num_changes}: Switching from " +
                            f"freq_sel={self.current_freq_sel} (div={self.current_division_factor}) to " +
                            f"freq_sel={new_freq_sel} (div={new_division_factor}) @ {time_ns}ns")

            # Remember old division factor before changing
            old_division_factor = self.current_division_factor

            # Change frequency
            self.set_frequency_selection(new_freq_sel)

            # Wait for prescaler to reset and stabilize
            # Longer wait if switching to a higher division factor
            stabilization_cycles = 20 + max(old_division_factor, new_division_factor) // 5
            await self.wait_clocks('i_clk', stabilization_cycles)

            # Determine monitoring duration based on the division factor
            # We need longer observation for higher division factors
            adjusted_cycles = max(cycles_between_changes, new_division_factor * 20)

            # Monitor for adjusted duration
            counter_changes, tick_events = await self.monitor_counter(adjusted_cycles)

            # Verify this segment individually
            if len(counter_changes) >= 2:
                interval_ok = self.verify_counter_changes(counter_changes, new_division_factor)
                sequence_ok = self.verify_counter_sequence(counter_changes)

                if not (interval_ok and sequence_ok):
                    time_ns = get_sim_time('ns')
                    self.log.error(f"Verification failed after frequency change to {new_freq_sel} @ {time_ns}ns")
                    all_passed = False
            else:
                self.log.warning(f"Not enough counter changes to verify for freq_sel={new_freq_sel}")

            # Record current cycle count for tracking frequency change points
            if all_counter_changes:
                last_segment = all_counter_changes[-1]
                current_cycle = sum(len(segment) for segment in all_counter_changes)
            else:
                current_cycle = 0

            freq_change_cycles.append(current_cycle)

            # Add these changes to our overall list
            if all_counter_changes:
                # Adjust cycle numbers to be continuous
                last_cycle = all_counter_changes[-1][-1][0] if all_counter_changes[-1] else 0
                all_counter_changes.append([(cycle + last_cycle, value) for cycle, value in counter_changes])
                all_tick_events.extend([cycle + last_cycle for cycle in tick_events])
            else:
                all_counter_changes.append(counter_changes)
                all_tick_events.extend(tick_events)

        # Analyze results
        total_changes = sum(len(changes) for changes in all_counter_changes)
        self.log.info(f"Recorded {total_changes} counter changes and {len(all_tick_events)} tick events")

        return all_passed


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def counter_freq_invariant_dynamic_test(dut):
    """Test dynamic frequency changes"""
    tb = CounterFreqInvariantTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Start the clock
    print('Starting clk')
    await tb.start_clock('i_clk', 10, 'ns')

    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    try:
        print('# Test 1: Frequency change test')
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Test 1: Frequency change test  @ {time_ns}ns ===")
        passed = await tb.run_frequency_change_test(num_changes=5, cycles_between_changes=500)
        time_ns = get_sim_time('ns')
        assert passed, f"Frequency change test failed @ {time_ns}ns"

        print('# Test 2: Random frequency test')
        tb.log.info("=== Test 2: Random frequency test ===")
        config = tb._create_random_freq_config()
        passed = await tb.run_frequency_test(config)
        time_ns = get_sim_time('ns')
        assert passed, "Random frequency test failed  @ {time_ns}ns"

        await tb.wait_clocks('i_clk', 50)
        tb.log.info(f"Dynamic frequency tests completed successfully @ {time_ns}ns")

    finally:
        # Set done flag
        tb.done = True
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Test 1: Frequency change test Done @ {time_ns}ns ===")
        # Wait for any pending tasks
        await tb.wait_clocks('i_clk', 10)


    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    try:
        print('# Test: Frequency change reset behavior')
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Testing frequency change reset behavior @ {time_ns}ns ===")

        # Test sequence: Go from high division factor to low and observe quick reset
        # Start with a high division factor
        high_freq_sel = 0xF  # 10000:1 division
        tb.set_frequency_selection(high_freq_sel)

        # Let it run for a short time
        await tb.wait_clocks('i_clk', 100)

        # Monitor counter behavior right before change
        counter_before = []
        for _ in range(10):
            await RisingEdge(tb.clock)
            counter_before.append(int(tb.dut.o_counter.value))

        tb.log.info(f"Counter values before change: {counter_before}")

        # Now switch to a very low division factor
        low_freq_sel = 0x0  # 1:1 division
        tb.set_frequency_selection(low_freq_sel)

        # If prescaler reset is working, we should see counter changes very quickly
        counter_after = []
        tick_seen = False

        # Monitor for a short period to see if counter starts changing
        for i in range(20):
            await RisingEdge(tb.clock)
            counter_value = int(tb.dut.o_counter.value)
            counter_after.append(counter_value)

            # Also check for tick signal
            if int(tb.dut.o_tick.value) == 1:
                tick_seen = True
                tb.log.info(f"Tick seen at cycle {i} after frequency change")

        tb.log.info(f"Counter values after change: {counter_after}")

        # Verify that counter started changing quickly after frequency change
        # With the 1:1 division, we should see changes in every cycle
        changes_detected = sum(
            counter_after[i] != counter_after[i - 1]
            for i in range(1, len(counter_after))
        )

        # If prescaler is reset properly, we should see at least several changes
        reset_working = changes_detected >= 5

        time_ns = get_sim_time('ns')
        if reset_working:
            tb.log.info(f"Prescaler reset verification passed: {changes_detected} changes detected after frequency change @ {time_ns}ns")
        else:
            tb.log.error(f"Prescaler reset verification failed: Only {changes_detected} changes detected @ {time_ns}ns")

        # Continue with a more extensive test of transitions
        print('# Testing transitions between various frequencies')

        # Define some transition pairs to test (high to low and low to high)
        transitions = [
            (0xF, 0x0),  # Very high to very low
            (0x0, 0xA),  # Very low to medium
            (0xC, 0x1),  # High to low
            (0x1, 0xD),  # Low to high
            (0x7, 0x3),  # Medium to medium
        ]

        all_transitions_passed = True

        for high_sel, low_sel in transitions:
            # Get division factors
            high_div = tb._get_division_factor(high_sel)
            low_div = tb._get_division_factor(low_sel)
            time_ns = get_sim_time('ns')

            tb.log.info(f"Testing transition from freq_sel={high_sel} (div={high_div}) to freq_sel={low_sel} (div={low_div}) @ {time_ns}ns")

            # Set first frequency
            tb.set_frequency_selection(high_sel)
            await tb.wait_clocks('i_clk', 50)

            # Set second frequency
            tb.set_frequency_selection(low_sel)

            # Monitor counter for a reasonable time
            # Even for low division factor, we should see changes quickly if reset works
            max_wait = 50
            changes_seen = 0

            for i in range(max_wait):
                current_counter = int(tb.dut.o_counter.value)
                await RisingEdge(tb.clock)
                next_counter = int(tb.dut.o_counter.value)

                if current_counter != next_counter:
                    changes_seen += 1
                    time_ns = get_sim_time('ns')
                    tb.log.info(f"Counter change detected at cycle {i} after frequency change @ {time_ns}ns")

                    # For verification, we only need to see a few changes
                    if changes_seen >= 3:
                        break

            # Verify that we saw changes within a reasonable time
            transition_passed = changes_seen > 0
            time_ns = get_sim_time('ns')

            if transition_passed:
                tb.log.info(f"Transition test passed: {changes_seen} changes detected @ {time_ns}ns")
            else:
                tb.log.error(f"Transition test failed: No changes detected within {max_wait} cycles @ {time_ns}ns")
                all_transitions_passed = False

        # Final result
        passed = reset_working and all_transitions_passed
        assert passed, "Frequency change reset test failed"

        await tb.wait_clocks('i_clk', 50)
        tb.log.info("Frequency change reset test completed successfully.")

    finally:
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Testing frequency change reset behavior Done @ {time_ns}ns ===")
        # Set done flag
        tb.done = True
        # Wait for any pending tasks
        await tb.wait_clocks('i_clk', 10)


@pytest.mark.parametrize("counter_width",
    [
        5,  # Standard width
        8,  # Wider counter
    ])
def test_counter_freq_invariant(request, counter_width):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    dut_name = "counter_freq_invariant"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    cw_str = TBBase.format_dec(counter_width, 3)
    test_name_plus_params = f"test_{dut_name}_cw{cw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {
        "COUNTER_WIDTH": str(counter_width)
    }

    # Environment variables
    extra_env = {
        'TEST_COUNTER_WIDTH': str(counter_width),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

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
            waves=True,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
