import contextlib
import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


class CDCValidReadyS2FConfig:
    """Configuration class for CDC valid/ready S2F (Slow to Fast) tests"""
    def __init__(self, name, valid_patterns, ready_patterns=None):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            valid_patterns: List of valid signal patterns
            ready_patterns: List of ready signal patterns (if None, will be all 1's)
        """
        self.name = name
        self.valid_patterns = valid_patterns

        # If ready patterns not provided, default to always ready
        if ready_patterns is None:
            self.ready_patterns = [[1] * len(pattern) for pattern in valid_patterns]
        else:
            self.ready_patterns = ready_patterns

        # Initialize iterators
        self.reset_iterators()

    def reset_iterators(self):
        """Reset all iterators to the beginning of sequences"""
        self._valid_iter = iter(self.valid_patterns)
        self._ready_iter = iter(self.ready_patterns)

    def next_valid_pattern(self):
        """Get next valid signal pattern"""
        return next(self._valid_iter)

    def next_ready_pattern(self):
        """Get next ready signal pattern"""
        return next(self._ready_iter)


class CDCValidReadyS2FTB(TBBase):
    """
    Testbench for the CDC handshake module
    Features:
    - Verify correct handshaking across clock domains
    - Test various valid/ready patterns
    - Test different clock ratios
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.CLKA_PERIOD_NS = self.convert_to_int(os.environ.get('CLKA_PERIOD_NS', '50'))
        self.CLKB_PERIOD_NS = self.convert_to_int(os.environ.get('CLKB_PERIOD_NS', '10'))

        # Calculate clock frequencies in MHz
        self.CLKA_FREQ_MHZ = 1000 / self.CLKA_PERIOD_NS
        self.CLKB_FREQ_MHZ = 1000 / self.CLKB_PERIOD_NS

        # Initialize random generator
        random.seed(self.SEED)

        # Extract clock and reset signals
        self.clka = self.dut.clka
        self.rsta_n = self.dut.rsta_n
        self.clkb = self.dut.clkb
        self.rstb_n = self.dut.rstb_n

        # Extract data interface signals
        self.valid_a = self.dut.valid_a
        self.ready_a = self.dut.ready_a
        self.data_a = self.dut.data_a
        self.valid_b = self.dut.valid_b
        self.ready_b = self.dut.ready_b
        self.data_b = self.dut.data_b

        # Try to extract internal debug signals
        try:
            self.r_src_state = self.dut.r_src_state
            self.r_dst_state = self.dut.r_dst_state
            self.r_req_a = self.dut.r_req_a
            self.r_ack_b = self.dut.r_ack_b
            self.internal_signals_available = True
        except Exception as e:
            self.log.warning(f"Internal signals not accessible: {e}")
            self.internal_signals_available = False

        # Log configuration
        self.log.info("CDC Valid/Ready S2F TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"CLKA={self.CLKA_PERIOD_NS}ns ({self.CLKA_FREQ_MHZ:.1f}MHz)")
        self.log.info(f"CLKB={self.CLKB_PERIOD_NS}ns ({self.CLKB_FREQ_MHZ:.1f}MHz)")

        # Test completion flag
        self.done = False

        # Monitoring data
        self.clka_transactions = []
        self.clkb_transactions = []

        # Track valid pulse information for verification
        self.valid_pulses = []
        self.valid_pulse_durations = []

        # Enhanced debug tracking
        self.debug_clka_signals = []  # Store clka domain signal history
        self.debug_clkb_signals = []  # Store clkb domain signal history

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.rsta_n.value = 0
        self.rstb_n.value = 0
        self.valid_a.value = 0
        self.ready_b.value = 0
        self.data_a.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clka', 5)
        await self.wait_clocks('clkb', 5)

        # Release reset
        self.rsta_n.value = 1
        self.rstb_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clka', 10)
        await self.wait_clocks('clkb', 10)

        # Clear monitoring data
        self.clka_transactions.clear()
        self.clkb_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()

        # Clear debug tracking
        self.debug_clka_signals.clear()
        self.debug_clkb_signals.clear()

        self.log.debug('Ending reset_dut')

    async def monitor_a_to_b(self, clka_cycles, clkb_cycles):
        """
        Monitor transactions from domain A to domain B

        Args:
            clka_cycles: Number of clka cycles to monitor
            clkb_cycles: Number of clkb cycles to monitor

        Returns:
            Tuple of (clka_transactions, clkb_transactions)
        """
        # Clear previous data
        self.clka_transactions.clear()
        self.clkb_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()

        # Clear debug tracking
        self.debug_clka_signals.clear()
        self.debug_clkb_signals.clear()

        # Set up concurrent monitoring of both clock domains
        clka_task = cocotb.start_soon(self._monitor_clka_domain(clka_cycles))
        clkb_task = cocotb.start_soon(self._monitor_clkb_domain(clkb_cycles))

        # Wait for both monitoring tasks to complete
        await clka_task
        await clkb_task

        # Print debug summary
        self.print_debug_summary()

        return self.clka_transactions, self.clkb_transactions

    async def monitor_a_to_b_with_target(self, expected_transactions):
        """
        Monitor transactions with automatic exit when target is reached

        Args:
            expected_transactions: Number of transactions to wait for before exiting

        Returns:
            Tuple of (clka_transactions, clkb_transactions)
        """
        # Clear previous data
        self.clka_transactions.clear()
        self.clkb_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()
        self.debug_clka_signals.clear()
        self.debug_clkb_signals.clear()

        # Create completion event
        target_reached = cocotb.triggers.Event()

        # Define maximum cycles to prevent infinite monitoring
        max_clka_cycles = max(500, int(50 * self.CLKA_PERIOD_NS / 10)) * expected_transactions
        max_clkb_cycles = max(500, int(50 * self.CLKB_PERIOD_NS / 10)) * expected_transactions

        # Define the checker function that will run in the background
        async def check_completion():
            while True:
                # Check if we've reached the target transaction count in both domains
                if (len(self.clka_transactions) >= expected_transactions and
                    len(self.clkb_transactions) >= expected_transactions):
                    # Give it a few more cycles to ensure we capture everything
                    await Timer(5 * max(self.CLKA_PERIOD_NS, self.CLKB_PERIOD_NS), units='ns')
                    target_reached.set()
                    break
                await Timer(min(self.CLKA_PERIOD_NS, self.CLKB_PERIOD_NS), units='ns')

        # Start the checker
        checker_task = cocotb.start_soon(check_completion())

        # Start the monitoring tasks with max limits
        clka_task = cocotb.start_soon(self._monitor_clka_domain(max_clka_cycles))
        clkb_task = cocotb.start_soon(self._monitor_clkb_domain(max_clkb_cycles))

        # Wait for either target to be reached or max cycles to complete
        t = await cocotb.triggers.First(
            target_reached.wait(),
            cocotb.triggers.Join(clka_task),
            cocotb.triggers.Join(clkb_task)
        )

        # If early exit (target reached), cancel the monitoring tasks
        if target_reached.is_set():
            self.log.info(f"Target of {expected_transactions} transactions reached - exiting monitoring early")
            if not clka_task.done():
                clka_task.kill()
            if not clkb_task.done():
                clkb_task.kill()
            if not checker_task.done():
                checker_task.kill()
            # Small delay to allow tasks to clean up
            await Timer(1, units='ns')
        else:
            # Otherwise, wait for any remaining tasks
            if not clka_task.done():
                await clka_task
            if not clkb_task.done():
                await clkb_task
            if not checker_task.done():
                checker_task.kill()
                await Timer(1, units='ns')

        # Print debug summary
        self.print_debug_summary()

        return self.clka_transactions, self.clkb_transactions

    def print_debug_summary(self):    # sourcery skip: extract-method, remove-redundant-fstring, simplify-constant-sum, use-contextlib-suppress
        """Print comprehensive debug information from the monitoring session"""
        time_ns = get_sim_time('ns')
        self.log.info(f"=== DEBUG SUMMARY @ {time_ns}ns ===")

        # Transaction analysis
        self.log.info("Transaction analysis:")
        self.log.info(f"  CLKA transactions: {len(self.clka_transactions)}")
        self.log.info(f"  CLKB transactions: {len(self.clkb_transactions)}")

        # Valid pulse analysis
        self.log.info("Valid pulse analysis:")
        self.log.info(f"  Total valid pulses detected: {len(self.valid_pulses)}")
        for i, ((start, end), duration) in enumerate(zip(self.valid_pulses, self.valid_pulse_durations)):
            self.log.info(f"  Valid pulse {i}: cycles {start}-{end}, duration={duration}")

        # Signal state analysis
        if self.debug_clka_signals:
            valid_high_count = sum(1 for _, _, v, _, _ in self.debug_clka_signals if v == 1)
            ready_high_count = sum(1 for _, _, _, r, _ in self.debug_clka_signals if r == 1)
            total_clka = len(self.debug_clka_signals)
            self.log.info(f"  CLKA domain signal states:")
            self.log.info(f"    Valid high: {valid_high_count}/{total_clka} cycles ({valid_high_count/total_clka*100:.1f}%)")
            self.log.info(f"    Ready high: {ready_high_count}/{total_clka} cycles ({ready_high_count/total_clka*100:.1f}%)")

        if self.debug_clkb_signals:
            valid_high_count = sum(1 for _, _, v, _, _ in self.debug_clkb_signals if v == 1)
            ready_high_count = sum(1 for _, _, _, r, _ in self.debug_clkb_signals if r == 1)
            total_clkb = len(self.debug_clkb_signals)
            self.log.info(f"  CLKB domain signal states:")
            self.log.info(f"    Valid high: {valid_high_count}/{total_clkb} cycles ({valid_high_count/total_clkb*100:.1f}%)")
            self.log.info(f"    Ready high: {ready_high_count}/{total_clkb} cycles ({ready_high_count/total_clkb*100:.1f}%)")

        # Internal signals dump if available
        if self.internal_signals_available:
            self.log.info("  Latest internal signal values:")
            try:
                self.log.info(f"    r_src_state: {int(self.r_src_state.value)}")
                self.log.info(f"    r_dst_state: {int(self.r_dst_state.value)}")
                self.log.info(f"    r_req_a: {int(self.r_req_a.value)}")
                self.log.info(f"    r_ack_b: {int(self.r_ack_b.value)}")
            except Exception:
                pass

        # CDC latency analysis
        if self.clka_transactions and self.clkb_transactions:
            min_count = min(len(self.clka_transactions), len(self.clkb_transactions))
            if min_count > 0:
                latencies = [
                    self.clkb_transactions[i][1] - self.clka_transactions[i][1]
                    for i in range(min_count)
                ]
                avg_latency = sum(latencies) / len(latencies)
                min_latency = min(latencies)
                max_latency = max(latencies)

                self.log.info(f"CDC Latency Analysis:")
                self.log.info(f"  Average latency: {avg_latency:.2f} ns")
                self.log.info(f"  Minimum latency: {min_latency:.2f} ns")
                self.log.info(f"  Maximum latency: {max_latency:.2f} ns")

        self.log.info(f"=== END DEBUG SUMMARY ===")

    async def _monitor_clka_domain(self, cycles):
        # sourcery skip: use-contextlib-suppress
        """Monitor transactions in clock domain A"""
        self.log.debug(f"Monitoring clka domain for {cycles} cycles")

        for cycle in range(cycles):
            await RisingEdge(self.clka)

            valid = int(self.valid_a.value)
            ready = int(self.ready_a.value)
            data = int(self.data_a.value)
            time_ns = get_sim_time('ns')

            # Track all signal states for debugging
            self.debug_clka_signals.append((cycle, time_ns, valid, ready, data))

            # Record valid transactions (when valid and ready are both high)
            if valid and ready:
                self.clka_transactions.append((cycle, time_ns, data))
                self.log.debug(f"clka cycle {cycle}: Transaction @ {time_ns}ns (Valid={valid}, Ready={ready}, Data=0x{data:02x})")

                # Log internal state if available
                if self.internal_signals_available:
                    try:
                        state = int(self.r_src_state.value)
                        self.log.debug(f"  Source state: {state}")
                    except Exception:
                        pass

    async def _monitor_clkb_domain(self, cycles):
        """Monitor transactions in clock domain B"""
        self.log.debug(f"Monitoring clkb domain for {cycles} cycles")

        # Track valid pulses for verification
        valid_duration = 0
        valid_start_cycle = -1
        last_valid = 0

        for cycle in range(cycles):
            await RisingEdge(self.clkb)

            valid = int(self.valid_b.value)
            ready = int(self.ready_b.value)
            data = int(self.data_b.value)
            time_ns = get_sim_time('ns')

            # Track all signal states for debugging
            self.debug_clkb_signals.append((cycle, time_ns, valid, ready, data))

            # Detect rising edge of valid
            if valid == 1 and last_valid == 0:
                valid_start_cycle = cycle
                valid_duration = 1
                self.log.debug(f"clkb cycle {cycle}: Valid pulse started @ {time_ns}ns")

            # Track ongoing valid pulse
            elif valid == 1:
                valid_duration += 1
            # Detect falling edge of valid (end of pulse)
            elif valid == 0 and last_valid == 1:
                self.valid_pulses.append((valid_start_cycle, cycle - 1))
                self.valid_pulse_durations.append(valid_duration)
                self.log.debug(f"clkb cycle {cycle}: Valid pulse ended, duration={valid_duration} @ {time_ns}ns")
                valid_duration = 0
                valid_start_cycle = -1

            last_valid = valid

            # Record valid transactions (when valid and ready are both high)
            if valid and ready:
                self.clkb_transactions.append((cycle, time_ns, data))
                self.log.debug(f"clkb cycle {cycle}: Transaction @ {time_ns}ns (Valid={valid}, Ready={ready}, Data=0x{data:02x})")

                # Log internal state if available
                if self.internal_signals_available:
                    with contextlib.suppress(Exception):
                        state = int(self.r_dst_state.value)
                        self.log.debug(f"  Destination state: {state}")
        # Handle case where valid is still high at end of monitoring
        if valid_start_cycle != -1:
            self.valid_pulses.append((valid_start_cycle, cycles - 1))
            self.valid_pulse_durations.append(valid_duration)
            self.log.debug(f"clkb end: Valid pulse still active, duration so far={valid_duration}")

    async def drive_single_handshake(self, data_value, ready_delay=0, preset_ready=False):
        """
        Drive a single valid/ready handshake

        Args:
            data_value: The data to send
            ready_delay: Number of cycles to delay ready_b assertion after valid_b
            preset_ready: If True, assumes ready_b is already set externally

        Returns:
            True if handshake completed successfully
        """
        self.log.info(f"Starting single handshake with data=0x{data_value:02x}, ready_delay={ready_delay}, preset_ready={preset_ready}")

        # Calculate monitoring cycles based on clock frequencies and expected CDC latency
        clka_cycles = max(50, int(50 * self.CLKA_PERIOD_NS / 10))
        clkb_cycles = max(50, int(50 * self.CLKB_PERIOD_NS / 10))

        # Start monitoring
        monitor_task = cocotb.start_soon(self.monitor_a_to_b(clka_cycles, clkb_cycles))

        # Only start the responder task if not using preset ready
        respond_task = None
        if not preset_ready:
            # Create a task to respond with ready_b when valid_b is detected
            async def respond_with_ready_b():
                # Wait for valid_b to be asserted
                while not self.done:
                    await RisingEdge(self.clkb)
                    if int(self.valid_b.value) == 1:
                        break

                # Optional delay before asserting ready_b
                for _ in range(ready_delay):
                    await RisingEdge(self.clkb)
                    if int(self.valid_b.value) == 0:  # If valid_b deasserts prematurely
                        self.log.error("valid_b deasserted before ready_b was asserted!")
                        return False

                # Assert ready_b to accept the data
                self.ready_b.value = 1

                # Wait one cycle and then deassert ready_b
                await RisingEdge(self.clkb)
                self.ready_b.value = 0

                return True

            # Start the responder task
            respond_task = cocotb.start_soon(respond_with_ready_b())

        try:
            # Drive the handshake from domain A
            time_ns = get_sim_time('ns')
            self.log.debug(f'Driving valid_a and data=0x{data_value:02x} @ {time_ns}ns')

            # Assert valid_a and data
            self.data_a.value = data_value
            self.valid_a.value = 1

            # Wait for ready_a to be asserted (handshake completed in source domain)
            cycles_waited = 0
            max_wait_cycles = 5000  # Maximum cycles to wait

            while True:
                await RisingEdge(self.clka)
                cycles_waited += 1

                if int(self.ready_a.value) == 1:
                    time_ns = get_sim_time('ns')
                    self.log.debug(f"ready_a asserted after {cycles_waited} cycles @ {time_ns}ns")
                    break

                if cycles_waited >= max_wait_cycles:
                    self.log.error(f"ready_a not asserted after {max_wait_cycles} cycles!")
                    return False

            # Deassert valid_a after handshake completes
            self.valid_a.value = 0
            self.data_a.value = 0

            # Wait a bit to ensure all effects propagate
            await self.wait_clocks('clka', 10)
            await self.wait_clocks('clkb', 20)

            # Verify respond_task completed successfully (if not using preset_ready)
            if respond_task is not None:
                respond_result = await respond_task
                if not respond_result:
                    return False

            # Wait for monitor to finish
            await monitor_task

            # Verify transactions
            return self.verify_handshake(data_value)

        finally:
            # Clean up
            self.valid_a.value = 0
            self.data_a.value = 0

            # Don't deassert ready_b if preset_ready was True
            # as it was set externally and should be cleared externally
            if not preset_ready:
                self.ready_b.value = 0

    async def drive_multiple_handshakes(self, data_values, ready_delays=None, preset_ready_b=False):
        """
        Drive multiple handshakes with different data values - robust implementation

        Args:
            data_values: List of data values to send
            ready_delays: List of ready_b delay cycles (optional)
            preset_ready_b: If True, sets ready_b at the start to test ready-before-valid condition

        Returns:
            True if all handshakes completed successfully
        """
        self.log.info(f"Starting multiple handshakes with {len(data_values)} values")

        # Reset for clean state
        await self.reset_dut()

        # Setup ready delays
        if ready_delays is None:
            ready_delays = [0] * len(data_values)

        # Ensure ready_delays is at least as long as data_values
        if len(ready_delays) < len(data_values):
            ready_delays = ready_delays + [0] * (len(data_values) - len(ready_delays))

        # Initialize monitoring
        expected_transactions = len(data_values)
        monitor_task = cocotb.start_soon(self.monitor_a_to_b_with_target(expected_transactions))

        # Set up valid_b response tracking
        valid_b_response_needed = not preset_ready_b
        valid_count = 0
        ready_b_responder_active = True

        # If testing ready-before-valid, set ready_b now
        if preset_ready_b:
            self.ready_b.value = 1

        # Launch a background task to monitor valid_b and respond with ready_b
        async def monitor_and_respond_to_valid_b():
            nonlocal valid_count, ready_b_responder_active

            # Keep running until we've seen all expected valid_b pulses
            while valid_count < len(data_values) and ready_b_responder_active:
                # Check for valid_b assertion on every clkb edge
                await RisingEdge(self.clkb)

                if int(self.valid_b.value) == 1:
                    # Log valid_b detection
                    time_ns = get_sim_time('ns')
                    self.log.debug(f"valid_b detected for transaction {valid_count+1} @ {time_ns}ns")

                    # Get delay for this transaction
                    delay = ready_delays[valid_count % len(ready_delays)]

                    # Apply configured delay before asserting ready_b
                    for _ in range(delay):
                        await RisingEdge(self.clkb)
                        # Check if valid_b deasserted during delay
                        if int(self.valid_b.value) == 0:
                            self.log.error(f"valid_b deasserted during ready delay (transaction {valid_count+1})")
                            return False

                    # Assert ready_b to accept the data
                    self.ready_b.value = 1
                    self.log.debug(f"Asserting ready_b for transaction {valid_count+1}")

                    # Wait one cycle and then deassert ready_b
                    await RisingEdge(self.clkb)
                    self.ready_b.value = 0

                    # Count this valid-ready handshake
                    valid_count += 1

                    # Wait for valid_b to deassert before looking for next transaction
                    while int(self.valid_b.value) == 1 and ready_b_responder_active:
                        await RisingEdge(self.clkb)

        # Only start the responder if we're not using preset_ready_b
        ready_response_task = None
        if valid_b_response_needed:
            ready_response_task = cocotb.start_soon(monitor_and_respond_to_valid_b())

        all_successful = True

        try:
            # Send data values in sequence
            for i, data_value in enumerate(data_values):
                self.log.info(f"Sending data {i+1}/{len(data_values)}: 0x{data_value:02x}")

                # Drive the handshake from domain A
                time_ns = get_sim_time('ns')
                self.log.debug(f'Driving valid_a and data=0x{data_value:02x} @ {time_ns}ns')

                # Assert valid_a and data
                self.data_a.value = data_value
                self.valid_a.value = 1

                # Wait for ready_a to be asserted (handshake completed in source domain)
                cycles_waited = 0
                max_wait_cycles = 5000  # Maximum cycles to wait

                # Log state before waiting if debug signals available
                if self.internal_signals_available:
                    self.log.debug(f"Before waiting for ready_a: src_state={int(self.r_src_state.value)}, "
                                f"dst_state={int(self.r_dst_state.value)}, "
                                f"r_req_a={int(self.r_req_a.value)}, r_ack_b={int(self.r_ack_b.value)}")

                # Wait for ready_a with debug logging
                while True:
                    await RisingEdge(self.clka)
                    cycles_waited += 1

                    # Log periodic debug info
                    if cycles_waited % 100 == 0:
                        time_ns = get_sim_time('ns')
                        self.log.debug(f"Still waiting for ready_a: {cycles_waited} cycles @ {time_ns}ns")
                        # Log current state of key signals
                        if self.internal_signals_available:
                            self.log.debug(f"  Current states: src={int(self.r_src_state.value)}, dst={int(self.r_dst_state.value)}")
                            self.log.debug(f"  Control signals: req_a={int(self.r_req_a.value)}, ack_b={int(self.r_ack_b.value)}")
                            self.log.debug(f"  Interface signals: valid_b={int(self.valid_b.value)}, ready_b={int(self.ready_b.value)}")

                    if int(self.ready_a.value) == 1:
                        time_ns = get_sim_time('ns')
                        self.log.debug(f"ready_a asserted after {cycles_waited} cycles @ {time_ns}ns")
                        break

                    if cycles_waited >= max_wait_cycles:
                        time_ns = get_sim_time('ns')
                        self.log.error(f"ready_a not asserted after {max_wait_cycles} cycles for data {i+1} @ {time_ns}ns")
                        all_successful = False
                        break

                # Deassert valid_a after handshake completes
                self.valid_a.value = 0
                self.data_a.value = 0

                # Wait a reasonable amount of time between transactions
                # This helps prevent issues with back-to-back transactions
                await self.wait_clocks('clka', 5)

                # Break early if there was a failure and we're in basic test mode
                if not all_successful and self.TEST_LEVEL == 'basic':
                    break

            # Wait for all transactions to complete
            await monitor_task

            # Verify expected number of transactions occurred
            if len(self.clka_transactions) != expected_transactions:
                self.log.error(f"Transaction count mismatch in A domain: expected {expected_transactions}, got {len(self.clka_transactions)}")
                all_successful = False

            if len(self.clkb_transactions) != expected_transactions:
                self.log.error(f"Transaction count mismatch in B domain: expected {expected_transactions}, got {len(self.clkb_transactions)}")
                all_successful = False

            # Verify all data values were transferred correctly
            for i, ((_, _, data_a), (_, _, data_b)) in enumerate(zip(self.clka_transactions, self.clkb_transactions)):
                if i < len(data_values) and (data_a != data_values[i] or data_b != data_values[i]):
                    self.log.error(f"Data mismatch in transaction {i+1}: expected 0x{data_values[i]:02x}, got A=0x{data_a:02x}, B=0x{data_b:02x}")
                    all_successful = False

            # Verify transaction ordering (B transactions must occur after A)
            for i, ((_, time_a, _), (_, time_b, _)) in enumerate(zip(self.clka_transactions, self.clkb_transactions)):
                if time_b <= time_a:
                    self.log.error(f"Transaction {i+1} timing error: A={time_a}ns, B={time_b}ns")
                    all_successful = False

        finally:
            # Clean up
            self.valid_a.value = 0
            self.data_a.value = 0

            # Ensure responder is stopped
            ready_b_responder_active = False

            # Clear ready_b if we set it
            if preset_ready_b:
                self.ready_b.value = 0

            # Cancel the response task if it exists and is still running
            if ready_response_task is not None and not ready_response_task.done():
                ready_response_task.kill()
                await Timer(1, units='ns')

        return all_successful

    def verify_handshake(self, expected_data=None):
        """
        Verify that the handshake was successful

        Args:
            expected_data: Expected data value (optional)

        Returns:
            True if verification passed, False otherwise
        """
        # Check transaction counts
        clka_count = len(self.clka_transactions)
        clkb_count = len(self.clkb_transactions)

        self.log.info(f"Verifying handshake: clka_count={clka_count}, clkb_count={clkb_count}")

        if clka_count != clkb_count:
            self.log.error(f"Transaction count mismatch: clka={clka_count}, clkb={clkb_count}")
            return False

        if clka_count == 0:
            self.log.error("No transactions detected")
            return False

        # Verify data integrity
        if expected_data is not None:
            for i, (_, _, data_a) in enumerate(self.clka_transactions):
                if data_a != expected_data:
                    self.log.error(f"Data mismatch in clka transaction {i}: expected=0x{expected_data:02x}, actual=0x{data_a:02x}")
                    return False

            for i, (_, _, data_b) in enumerate(self.clkb_transactions):
                if data_b != expected_data:
                    self.log.error(f"Data mismatch in clkb transaction {i}: expected=0x{expected_data:02x}, actual=0x{data_b:02x}")
                    return False

        # Verify data consistency between domains
        for i, ((_, _, data_a), (_, _, data_b)) in enumerate(zip(self.clka_transactions, self.clkb_transactions)):
            if data_a != data_b:
                self.log.error(f"Data mismatch in transaction {i}: A=0x{data_a:02x}, B=0x{data_b:02x}")
                return False

        # Verify transaction ordering (clkb transactions should come after clka)
        for i, ((_, time_a, _), (_, time_b, _)) in enumerate(zip(self.clka_transactions, self.clkb_transactions)):
            if time_b <= time_a:
                self.log.error(f"Transaction {i} timing error: A={time_a}ns, B={time_b}ns")
                return False

        # Verify valid_b pulse behavior
        if len(self.valid_pulses) != clka_count:
            self.log.error(f"Valid pulse count mismatch: detected {len(self.valid_pulses)}, expected {clka_count}")
            return False

        # All checks passed
        self.log.info("Handshake verification PASSED")
        return True

    async def run_back_pressure_test(self, data_value=0xA5):
        """
        Test back-pressure by incrementally increasing ready_b delay

        Args:
            data_value: Data value to use for testing

        Returns:
            True if all tests passed
        """
        # Determine max delay based on test level
        if self.TEST_LEVEL == 'basic':
            max_delay = 5
        elif self.TEST_LEVEL == 'medium':
            max_delay = 10
        else:  # full
            max_delay = 15

        self.log.info(f"Running back-pressure test with delays 0 to {max_delay}")

        all_passed = True

        # First, test with standard ready-after-valid behavior
        for delay in range(0, max_delay + 1, 3):  # Test with increasing delays
            self.log.info(f"Testing with ready_b delay of {delay} cycles")

            # Reset for clean state
            await self.reset_dut()

            # Drive a handshake with the specified delay
            success = await self.drive_single_handshake(data_value, delay)

            if not success:
                self.log.error(f"Back-pressure test failed with delay={delay}")
                all_passed = False
                if self.TEST_LEVEL != 'full':
                    break  # Stop on first failure unless in full test mode
            else:
                self.log.info(f"Back-pressure test passed with delay={delay}")

            # Wait between tests
            await self.wait_clocks('clka', 5)
            await self.wait_clocks('clkb', 10)

        # Now, if still passing, test the preset ready scenario
        if all_passed and self.TEST_LEVEL != 'basic':
            self.log.info("Testing preset ready_b scenario")
            await self.reset_dut()

            # Set ready_b before driving valid
            self.ready_b.value = 1

            # Wait a few cycles for stability
            await self.wait_clocks('clkb', 5)

            # Drive a handshake with preset ready
            success = await self.drive_single_handshake(data_value, 0, preset_ready=True)

            if not success:
                self.log.error("Back-pressure test failed with preset ready_b")
                all_passed = False
            else:
                self.log.info("Back-pressure test passed with preset ready_b")

            # Clear ready_b for cleanup
            self.ready_b.value = 0

        return all_passed

    async def run_clock_ratio_test(self):
        """
        Test across different clock frequency ratios

        Returns:
            True if all tests passed
        """
        # Use the currently configured clock ratio
        clka_period_ns = self.CLKA_PERIOD_NS
        clkb_period_ns = self.CLKB_PERIOD_NS
        ratio = clkb_period_ns / clka_period_ns

        self.log.info(f"Running clock ratio test with ratio 1:{ratio:.1f}")

        # Test with different data patterns based on test level
        if self.TEST_LEVEL == 'basic':
            data_values = [0xA5]
        elif self.TEST_LEVEL == 'medium':
            data_values = [0xA5, 0x5A, 0xC3]
        else:  # full
            data_values = [0xA5, 0x5A, 0xC3, 0x3C, 0xFF, 0x00]

        # Run handshake test with current clock ratio
        return await self.drive_multiple_handshakes(data_values)


    async def run_data_pattern_test(self):
        """
        Test with various data patterns

        Returns:
            True if all patterns were successful
        """
        # Define test patterns based on test level
        if self.TEST_LEVEL == 'basic':
            patterns = [
                [0x00, 0xFF, 0x55, 0xAA],  # Basic patterns
            ]
        elif self.TEST_LEVEL == 'medium':
            patterns = [
                [0x00, 0xFF, 0x55, 0xAA],  # Basic patterns
                [0x01, 0x02, 0x04, 0x08],  # Walking ones
            ]
        else:  # full
            patterns = [
                [0x00, 0xFF, 0x55, 0xAA],  # Basic patterns
                [0x01, 0x02, 0x04, 0x08],  # Walking ones
                [0x80, 0x40, 0x20, 0x10],  # Walking zeros
                [0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3F, 0x7F, 0xFF],  # Incrementing bits
            ]

        # Reset for clean state
        await self.reset_dut()
        self.log.info(f"Running data pattern test with {len(patterns)} patterns")

        all_passed = True

        for pattern_idx, pattern in enumerate(patterns):
            self.log.info(f"Testing pattern {pattern_idx+1}: {[hex(x) for x in pattern]}")

            # For longer patterns, use a longer wait time between transactions
            wait_cycles = 30 if len(pattern) > 4 else 15
            self.log.info(f"Using inter-transaction wait of {wait_cycles} clka cycles")

            # For other patterns, use the standard approach
            success = await self.drive_multiple_handshakes(pattern)

            if not success:
                self.log.error(f"Pattern test {pattern_idx+1} failed")
                all_passed = False
                if self.TEST_LEVEL != 'full':
                    break  # Stop on first failure unless in full test mode
            else:
                self.log.info(f"Pattern test {pattern_idx+1} passed")

            # Wait between patterns
            await self.wait_clocks('clka', 10)
            await self.wait_clocks('clkb', 20)

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}")

        all_passed = True

        if self.TEST_LEVEL not in ['medium_only', 'full_only']:
            # 1. Single handshake test
            self.log.info("1. Running single handshake test")
            await self.reset_dut()
            single_test_passed = await self.drive_single_handshake(0xA5)
            if not single_test_passed:
                self.log.error("Single handshake test failed")
                all_passed = False

            # 2. Multiple handshakes test
            self.log.info("2. Running multiple handshakes test")
            await self.reset_dut()
            multi_test_passed = await self.drive_multiple_handshakes([0xA5, 0x5A, 0xC3, 0x3C], preset_ready_b=False)
            if not multi_test_passed:
                self.log.error("Multiple handshakes test failed")
                all_passed = False

            # 2.5 Multiple handshakes test
            self.log.info("2.5 Running multiple handshakes test, preset ready_b")
            await self.reset_dut()
            multi_test_passed = await self.drive_multiple_handshakes([0xA5, 0x5A, 0xC3, 0x3C], preset_ready_b=True)
            if not multi_test_passed:
                self.log.error("Multiple handshakes test failed")
                all_passed = False

        if self.TEST_LEVEL not in ['medium', 'full']:
            return all_passed

        if self.TEST_LEVEL not in ['full_only']:
            # 3. Back-pressure test
            self.log.info("3. Running back-pressure test")
            bp_test_passed = await self.run_back_pressure_test()
            if not bp_test_passed:
                self.log.error("Back-pressure test failed")
                all_passed = False

            # 4. Data pattern test
            self.log.info("4. Running data pattern test")
            pattern_test_passed = await self.run_data_pattern_test()
            if not pattern_test_passed:
                self.log.error("Data pattern test failed")
                all_passed = False

        # Tests below this point only run in full test level
        if self.TEST_LEVEL not in ['full']:
            return all_passed

        # 5. Additional advanced tests for full test level
        self.log.info("5. Running additional tests for full test level")

        # Extended back-pressure test with multiple data values and longer delays
        self.log.info("5.1 Running extended back-pressure test")
        await self.reset_dut()
        data_values = [0x55, 0xAA, 0x33, 0xCC, 0xFF]
        ready_delays = [1, 5, 10, 15, 20]
        ext_bp_test_passed = await self.drive_multiple_handshakes(data_values, ready_delays, preset_ready_b=False)
        if not ext_bp_test_passed:
            self.log.error("Extended back-pressure test failed")
            all_passed = False

        # 5.5 Additional advanced tests for full test level
        self.log.info("5.1.5 Running additional tests for full test level, preset ready_b")

        # Extended back-pressure test with multiple data values and longer delays
        self.log.info("5.1.5 Running extended back-pressure test, preset ready_b")
        await self.reset_dut()
        data_values = [0x55, 0xAA, 0x33, 0xCC, 0xFF]
        ready_delays = [1, 5, 10, 15, 20]
        ext_bp_test_passed = await self.drive_multiple_handshakes(data_values, ready_delays, preset_ready_b=True)
        if not ext_bp_test_passed:
            self.log.error("Extended back-pressure test failed with preset ready_b")
            all_passed = False

        # Stress test with random data
        self.log.info("5.2 Running stress test with random data")
        await self.reset_dut()
        random_data = [random.randint(0, 255) for _ in range(20)]
        stress_test_passed = await self.drive_multiple_handshakes(random_data, preset_ready_b=False)
        if not stress_test_passed:
            self.log.error("Stress test failed")
            all_passed = False

        # Stress test with random data
        self.log.info("5.2.5 Running stress test with random data, preset ready_b")
        await self.reset_dut()
        random_data = [random.randint(0, 255) for _ in range(20)]
        stress_test_passed = await self.drive_multiple_handshakes(random_data, preset_ready_b=True)
        if not stress_test_passed:
            self.log.error("Stress test with preset ready_b failed")
            all_passed = False

        return all_passed


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = CDCValidReadyS2FTB(dut)

    # Start clocks with configured periods
    await tb.start_clock('clka', tb.CLKA_PERIOD_NS, 'ns')
    await tb.start_clock('clkb', tb.CLKB_PERIOD_NS, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


@pytest.mark.parametrize("params", [

    # clka slower than clkb
    {'clka_period_ns':  15, 'clkb_period_ns': 10, 'test_level': 'full'}, # 'basic', 'medium', 'full'
    {'clka_period_ns':  20, 'clkb_period_ns': 10, 'test_level': 'full'},
    {'clka_period_ns':  50, 'clkb_period_ns': 10, 'test_level': 'full'},
    {'clka_period_ns': 100, 'clkb_period_ns': 10, 'test_level': 'full'},
    {'clka_period_ns': 200, 'clkb_period_ns': 10, 'test_level': 'full'},

    # # clka faster than clkb
    {'clka_period_ns': 10, 'clkb_period_ns':  15, 'test_level': 'full'},
    {'clka_period_ns': 10, 'clkb_period_ns':  20, 'test_level': 'full'},
    {'clka_period_ns': 10, 'clkb_period_ns':  50, 'test_level': 'full'},
    {'clka_period_ns': 10, 'clkb_period_ns': 100, 'test_level': 'full'},
    {'clka_period_ns': 10, 'clkb_period_ns': 200, 'test_level': 'full'},

])
def test_cdc_handshake(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_axi': 'rtl/axi'})

    dut_name = "cdc_handshake"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human-readable test identifier with clock ratio and test level
    ratio = params['clka_period_ns'] / params['clkb_period_ns']

    t_clka = params['clka_period_ns']
    t_clkb = params['clkb_period_ns']
    t_name = params['test_level']
    test_name_plus_params = f"test_{dut_name}_clka{t_clka}_clkb{t_clkb}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # Prepare environment variables
    seed = random.randint(0, 100000)
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347), # str(seed),
        'TEST_LEVEL': params['test_level'],
        'CLKA_PERIOD_NS': str(params['clka_period_ns']),
        'CLKB_PERIOD_NS': str(params['clkb_period_ns'])
    }

    # Calculate timeout based on clock periods
    timeout_factor = max(1.0, t_clka / 10, t_clkb / 10) * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
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
