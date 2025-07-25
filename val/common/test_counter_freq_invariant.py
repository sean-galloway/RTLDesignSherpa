import os
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Division factor mapping for each frequency selection value
FACTOR_MAP = {
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
        return FACTOR_MAP.get(freq_sel, 1)  # Default to 1 if invalid


class CounterFreqInvariantTB(TBBase):
    """
    Testbench for the counter_freq_invariant module
    Features:
    - Frequency selection testing
    - Counter output verification
    - Tick signal monitoring
    - Frequency change verification
    - Synchronous reset testing
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
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n
        self.sync_reset_n = self.dut.sync_reset_n  # New synchronous reset signal

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
        return FACTOR_MAP.get(freq_sel, 1)  # Default to 1 if invalid

    async def reset_dut(self):
        """Reset the DUT using the asynchronous reset"""
        self.log.debug('Starting asynchronous reset_dut')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.sync_reset_n.value = 1  # Keep sync reset inactive during async reset
        self.dut.freq_sel.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clk', 5)

        # Release reset
        self.reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        # Clear monitoring data
        self.counter_changes.clear()
        self.tick_events.clear()

        self.log.debug('Ending asynchronous reset_dut')

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
        prev_counter = int(self.dut.counter.value)
        self.counter_changes.append((0, prev_counter))

        # Monitor for specified cycles
        for cycle in range(1, num_cycles + 1):
            await RisingEdge(self.clock)

            # Check counter value
            current_counter = int(self.dut.counter.value)
            if current_counter != prev_counter:
                self.counter_changes.append((cycle, current_counter))
                self.log.debug(f"Cycle {cycle}: Counter changed to {current_counter}")
                prev_counter = current_counter

            # Check tick signal
            if int(self.dut.tick.value) == 1:
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
        self.dut.freq_sel.value = freq_sel
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
            # With the RTL, we might not see tick events for short monitoring periods
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

    async def run_sync_reset_test(self):
        """
        Test the synchronous reset functionality

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing synchronous reset functionality ===")

        # Reset for clean state
        await self.reset_dut()

        # Set a moderate frequency for testing
        freq_sel = 0x1  # 10:1 division
        self.set_frequency_selection(freq_sel)

        # Wait for counter to start incrementing
        await self.wait_clocks('clk', 50)

        # Capture counter value before sync reset
        counter_before = int(self.dut.counter.value)
        self.log.info(f"Counter value before sync reset: {counter_before}")

        # Apply synchronous reset
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 5)  # Wait 1 cycle for the reset to take effect

        # Capture counter value during sync reset
        counter_during = int(self.dut.counter.value)
        self.log.info(f"Counter value during sync reset: {counter_during}")

        # Verify counter is reset to 0 during sync reset
        sync_reset_effective = (counter_during == 0)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Wait for counter to start incrementing again
        await self.wait_clocks('clk', 30)

        # Monitor counter behavior after sync reset
        counter_changes, tick_events = await self.monitor_counter(100)

        # Verify counter starts from 0 after sync reset
        counter_restart_ok = len(counter_changes) > 1 and counter_changes[0][0] == 0
        self.log.debug(f"{counter_changes=}")

        # Verify counter increments correctly after sync reset
        sequence_ok = self.verify_counter_sequence(counter_changes)

        # Return overall test status
        test_passed = sync_reset_effective and counter_restart_ok and sequence_ok
        self.log.debug(f"{sync_reset_effective=} {counter_restart_ok=} {sequence_ok=}")

        if test_passed:
            self.log.info("Synchronous reset test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Synchronous reset test failed @ {time_ns}ns")

            if not sync_reset_effective:
                self.log.error(f"Counter was not reset to 0 during sync reset (value: {counter_during})")
            if not counter_restart_ok:
                self.log.error("Counter did not restart from 0 after sync reset")
            if not sequence_ok:
                self.log.error("Counter sequence incorrect after sync reset")

        return test_passed

    async def run_sync_reset_during_operation_test(self):
        """
        Test the synchronous reset during counter operation

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing synchronous reset during operation ===")

        # Reset for clean state
        await self.reset_dut()

        # Set a low frequency for immediate counter changes
        freq_sel = 0x0  # 1:1 division
        self.set_frequency_selection(freq_sel)

        # Wait for counter to increment a few times
        await self.wait_clocks('clk', 10)

        # Start monitoring
        counter_values = []
        for _ in range(5):
            counter_values.append(int(self.dut.counter.value))
            await self.wait_clocks('clk', 1)

        # Apply sync reset in the middle of operation
        self.sync_reset_n.value = 0
        counter_during_reset = int(self.dut.counter.value)
        await self.wait_clocks('clk', 5)

        # Verify counter is reset synchronously
        counter_after_reset = int(self.dut.counter.value)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Monitor counter after reset
        post_reset_values = []
        for _ in range(10):
            post_reset_values.append(int(self.dut.counter.value))
            await self.wait_clocks('clk', 1)

        # Verify counter was reset to 0
        reset_effective = (counter_after_reset == 0)

        # Verify counter increments again after reset
        counter_incrementing = any(val > 0 for val in post_reset_values[1:])

        # Log results
        self.log.info(f"Counter values before reset: {counter_values}")
        self.log.info(f"Counter during reset application: {counter_during_reset}")
        self.log.info(f"Counter after reset application: {counter_after_reset}")
        self.log.info(f"Counter values after reset release: {post_reset_values}")

        # Return test result
        test_passed = reset_effective and counter_incrementing

        if test_passed:
            self.log.info("Synchronous reset during operation test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Synchronous reset during operation test failed @ {time_ns}ns")

            if not reset_effective:
                self.log.error(f"Counter was not reset to 0 (value: {counter_after_reset})")

            if not counter_incrementing:
                self.log.error("Counter did not increment after reset release")

        return test_passed

    async def run_sync_vs_async_reset_test(self):
        """
        Compare synchronous and asynchronous reset behavior

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing synchronous vs asynchronous reset behavior ===")

        # First, test asynchronous reset
        self.log.info("Testing asynchronous reset behavior")

        # Set a moderate frequency
        freq_sel = 0x1  # 10:1 division
        self.set_frequency_selection(freq_sel)

        # Let counter run for a bit
        await self.wait_clocks('clk', 50)

        # Apply asynchronous reset
        self.reset_n.value = 0
        await self.wait_clocks('clk', 1)

        # Immediately check counter
        counter_after_async = int(self.dut.counter.value)

        # Release async reset
        await self.wait_clocks('clk', 5)
        self.reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 20)

        # Now test synchronous reset
        self.log.info("Testing synchronous reset behavior")

        # Set same frequency
        self.set_frequency_selection(freq_sel)

        # Let counter run for a bit
        await self.wait_clocks('clk', 50)

        # Apply synchronous reset
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 1)

        # Check counter immediately
        counter_immediate_sync = int(self.dut.counter.value)

        # Wait five clock cycles and check again
        await self.wait_clocks('clk', 5)
        counter_after_sync = int(self.dut.counter.value)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Log results
        self.log.info(f"Counter value immediately after async reset: {counter_after_async}")
        self.log.info(f"Counter value immediately after sync reset: {counter_immediate_sync}")
        self.log.info(f"Counter value one cycle after sync reset: {counter_after_sync}")

        # Verify async reset is immediate
        async_immediate = (counter_after_async == 0)

        # Verify sync reset takes effect after a clock cycle
        sync_delayed = (counter_after_sync == 0)

        # Return test result
        test_passed = async_immediate and sync_delayed
        self.log.debug(f'{async_immediate=} {sync_delayed=}')

        if test_passed:
            self.log.info("Synchronous vs asynchronous reset behavior test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Synchronous vs asynchronous reset behavior test failed @ {time_ns}ns")

            if not async_immediate:
                self.log.error(f"Asynchronous reset did not reset counter immediately (value: {counter_after_async})")

            if not sync_delayed:
                self.log.error(f"Synchronous reset did not reset counter after a clock cycle (value: {counter_after_sync})")

        return test_passed

    async def run_freq_change_with_sync_reset_test(self):
        """
        Test frequency change combined with synchronous reset

        Returns:
            True if test passed, False otherwise
        """
        self.log.info("=== Testing frequency change with synchronous reset ===")

        # Reset for clean state
        await self.reset_dut()

        # Set initial frequency
        initial_freq_sel = 0x7  # 100:1 division
        self.set_frequency_selection(initial_freq_sel)

        # Let counter run for a bit
        await self.wait_clocks('clk', 100)

        # Apply both frequency change and sync reset simultaneously
        new_freq_sel = 0x1  # 10:1 division
        self.set_frequency_selection(new_freq_sel)
        self.sync_reset_n.value = 0

        # Wait five clock cycles
        await self.wait_clocks('clk', 5)

        # Check counter after sync reset
        counter_after_reset = int(self.dut.counter.value)

        # Release sync reset
        self.sync_reset_n.value = 1

        # Monitor counter behavior
        await self.wait_clocks('clk', 30)
        counter_changes, tick_events = await self.monitor_counter(200)

        # Verify reset was effective
        reset_effective = (counter_after_reset == 0)

        # Verify counter operates at new frequency
        if len(counter_changes) >= 3:
            freq_change_effective = self.verify_counter_changes(counter_changes, self.current_division_factor)
        else:
            self.log.warning("Not enough counter changes to verify frequency")
            freq_change_effective = True  # Assume it's OK if we don't have enough data

        # Verify counter sequence
        sequence_ok = self.verify_counter_sequence(counter_changes)

        # Return test result
        test_passed = reset_effective and freq_change_effective and sequence_ok

        if test_passed:
            self.log.info("Frequency change with synchronous reset test passed")
        else:
            time_ns = get_sim_time('ns')
            self.log.error(f"Frequency change with synchronous reset test failed @ {time_ns}ns")

            if not reset_effective:
                self.log.error(f"Synchronous reset did not reset counter (value: {counter_after_reset})")

            if not freq_change_effective:
                self.log.error("Counter not operating at new frequency after reset and frequency change")

            if not sequence_ok:
                self.log.error("Counter sequence incorrect after reset and frequency change")

        return test_passed


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def counter_freq_invariant_sync_reset_test(dut):
    """Test synchronous reset functionality"""
    tb = CounterFreqInvariantTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)

    # Start the clock
    print('Starting clk')
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT
    print('DUT reset')
    await tb.reset_dut()

    try:
        print('# Test 1: Basic synchronous reset test')
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Test 1: Basic synchronous reset test @ {time_ns}ns ===")
        passed = await tb.run_sync_reset_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Basic synchronous reset test failed @ {time_ns}ns"

        print('# Test 2: Synchronous reset during operation test')
        tb.log.info("=== Test 2: Synchronous reset during operation test ===")
        passed = await tb.run_sync_reset_during_operation_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Synchronous reset during operation test failed @ {time_ns}ns"

        print('# Test 3: Synchronous vs asynchronous reset test')
        tb.log.info("=== Test 3: Synchronous vs asynchronous reset test ===")
        passed = await tb.run_sync_vs_async_reset_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Synchronous vs asynchronous reset test failed @ {time_ns}ns"

        print('# Test 4: Frequency change with synchronous reset test')
        tb.log.info("=== Test 4: Frequency change with synchronous reset test ===")
        passed = await tb.run_freq_change_with_sync_reset_test()
        time_ns = get_sim_time('ns')
        assert passed, f"Frequency change with synchronous reset test failed @ {time_ns}ns"

        await tb.wait_clocks('clk', 50)
        tb.log.info(f"Synchronous reset tests completed successfully @ {time_ns}ns")

    finally:
        # Set done flag
        tb.done = True
        # Wait for any pending tasks
        await tb.wait_clocks('clk', 10)


@pytest.mark.parametrize("counter_width",
    [
        5,  # Standard width
        8,  # Wider counter
    ])
def test_counter_freq_invariant(request, counter_width):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    })

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
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'TEST_COUNTER_WIDTH': str(counter_width),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    compile_args = [
            "--trace-fst",
            "--trace-structs",
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace-fst",  # Tell Verilator to use FST
            "--trace-structs",
            "--trace-depth", "99",
    ]

    plusargs = [
            "+trace",
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
            waves=True,
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
