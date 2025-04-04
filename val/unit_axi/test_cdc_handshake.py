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
        self.clk_src_PERIOD_NS = self.convert_to_int(os.environ.get('clk_src_PERIOD_NS', '50'))
        self.clk_dst_PERIOD_NS = self.convert_to_int(os.environ.get('clk_dst_PERIOD_NS', '10'))

        # Calculate clock frequencies in MHz
        self.clk_src_FREQ_MHZ = 1000 / self.clk_src_PERIOD_NS
        self.clk_dst_FREQ_MHZ = 1000 / self.clk_dst_PERIOD_NS

        # Initialize random generator
        random.seed(self.SEED)

        # Extract clock and reset signals
        self.clk_src = self.dut.clk_src
        self.rst_src_n = self.dut.rst_src_n
        self.clk_dst = self.dut.clk_dst
        self.rst_dst_n = self.dut.rst_dst_n

        # Extract data interface signals
        self.valid_src = self.dut.valid_src
        self.ready_src = self.dut.ready_src
        self.data_src = self.dut.data_src
        self.valid_dst = self.dut.valid_dst
        self.ready_dst = self.dut.ready_dst
        self.data_dst = self.dut.data_dst

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
        self.log.info(f"clk_src={self.clk_src_PERIOD_NS}ns ({self.clk_src_FREQ_MHZ:.1f}MHz)")
        self.log.info(f"clk_dst={self.clk_dst_PERIOD_NS}ns ({self.clk_dst_FREQ_MHZ:.1f}MHz)")

        # Test completion flag
        self.done = False

        # Monitoring data
        self.clk_src_transactions = []
        self.clk_dst_transactions = []

        # Track valid pulse information for verification
        self.valid_pulses = []
        self.valid_pulse_durations = []

        # Enhanced debug tracking
        self.debug_clk_src_signals = []  # Store clk_src domain signal history
        self.debug_clk_dst_signals = []  # Store clk_dst domain signal history

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.rst_src_n.value = 0
        self.rst_dst_n.value = 0
        self.valid_src.value = 0
        self.ready_dst.value = 0
        self.data_src.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clk_src', 5)
        await self.wait_clocks('clk_dst', 5)

        # Release reset
        self.rst_src_n.value = 1
        self.rst_dst_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk_src', 10)
        await self.wait_clocks('clk_dst', 10)

        # Clear monitoring data
        self.clk_src_transactions.clear()
        self.clk_dst_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()

        # Clear debug tracking
        self.debug_clk_src_signals.clear()
        self.debug_clk_dst_signals.clear()

        self.log.debug('Ending reset_dut')

    async def monitor_a_to_b(self, clk_src_cycles, clk_dst_cycles):
        """
        Monitor transactions from domain A to domain B

        Args:
            clk_src_cycles: Number of clk_src cycles to monitor
            clk_dst_cycles: Number of clk_dst cycles to monitor

        Returns:
            Tuple of (clk_src_transactions, clk_dst_transactions)
        """
        # Clear previous data
        self.clk_src_transactions.clear()
        self.clk_dst_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()

        # Clear debug tracking
        self.debug_clk_src_signals.clear()
        self.debug_clk_dst_signals.clear()

        # Set up concurrent monitoring of both clock domains
        clk_src_task = cocotb.start_soon(self._monitor_clk_src_domain(clk_src_cycles))
        clk_dst_task = cocotb.start_soon(self._monitor_clk_dst_domain(clk_dst_cycles))

        # Wait for both monitoring tasks to complete
        await clk_src_task
        await clk_dst_task

        # Print debug summary
        self.print_debug_summary()

        return self.clk_src_transactions, self.clk_dst_transactions

    async def monitor_a_to_b_with_target(self, expected_transactions):
        """
        Monitor transactions with automatic exit when target is reached

        Args:
            expected_transactions: Number of transactions to wait for before exiting

        Returns:
            Tuple of (clk_src_transactions, clk_dst_transactions)
        """
        # Clear previous data
        self.clk_src_transactions.clear()
        self.clk_dst_transactions.clear()
        self.valid_pulses.clear()
        self.valid_pulse_durations.clear()
        self.debug_clk_src_signals.clear()
        self.debug_clk_dst_signals.clear()

        # Create completion event
        target_reached = cocotb.triggers.Event()

        # Define maximum cycles to prevent infinite monitoring
        max_clk_src_cycles = max(500, int(50 * self.clk_src_PERIOD_NS / 10)) * expected_transactions
        max_clk_dst_cycles = max(500, int(50 * self.clk_dst_PERIOD_NS / 10)) * expected_transactions

        # Define the checker function that will run in the background
        async def check_completion():
            while True:
                # Check if we've reached the target transaction count in both domains
                if (len(self.clk_src_transactions) >= expected_transactions and
                    len(self.clk_dst_transactions) >= expected_transactions):
                    # Give it a few more cycles to ensure we capture everything
                    await Timer(5 * max(self.clk_src_PERIOD_NS, self.clk_dst_PERIOD_NS), units='ns')
                    target_reached.set()
                    break
                await Timer(min(self.clk_src_PERIOD_NS, self.clk_dst_PERIOD_NS), units='ns')

        # Start the checker
        checker_task = cocotb.start_soon(check_completion())

        # Start the monitoring tasks with max limits
        clk_src_task = cocotb.start_soon(self._monitor_clk_src_domain(max_clk_src_cycles))
        clk_dst_task = cocotb.start_soon(self._monitor_clk_dst_domain(max_clk_dst_cycles))

        # Wait for either target to be reached or max cycles to complete
        t = await cocotb.triggers.First(
            target_reached.wait(),
            cocotb.triggers.Join(clk_src_task),
            cocotb.triggers.Join(clk_dst_task)
        )

        # If early exit (target reached), cancel the monitoring tasks
        if target_reached.is_set():
            self.log.info(f"Target of {expected_transactions} transactions reached - exiting monitoring early")
            if not clk_src_task.done():
                clk_src_task.kill()
            if not clk_dst_task.done():
                clk_dst_task.kill()
            if not checker_task.done():
                checker_task.kill()
            # Small delay to allow tasks to clean up
            await Timer(1, units='ns')
        else:
            # Otherwise, wait for any remaining tasks
            if not clk_src_task.done():
                await clk_src_task
            if not clk_dst_task.done():
                await clk_dst_task
            if not checker_task.done():
                checker_task.kill()
                await Timer(1, units='ns')

        # Print debug summary
        self.print_debug_summary()

        return self.clk_src_transactions, self.clk_dst_transactions

    def print_debug_summary(self):    # sourcery skip: extract-method, remove-redundant-fstring, simplify-constant-sum, use-contextlib-suppress
        """Print comprehensive debug information from the monitoring session"""
        time_ns = get_sim_time('ns')
        self.log.info(f"=== DEBUG SUMMARY @ {time_ns}ns ===")

        # Transaction analysis
        self.log.info("Transaction analysis:")
        self.log.info(f"  clk_src transactions: {len(self.clk_src_transactions)}")
        self.log.info(f"  clk_dst transactions: {len(self.clk_dst_transactions)}")

        # Valid pulse analysis
        self.log.info("Valid pulse analysis:")
        self.log.info(f"  Total valid pulses detected: {len(self.valid_pulses)}")
        for i, ((start, end), duration) in enumerate(zip(self.valid_pulses, self.valid_pulse_durations)):
            self.log.info(f"  Valid pulse {i}: cycles {start}-{end}, duration={duration}")

        # Signal state analysis
        if self.debug_clk_src_signals:
            valid_high_count = sum(1 for _, _, v, _, _ in self.debug_clk_src_signals if v == 1)
            ready_high_count = sum(1 for _, _, _, r, _ in self.debug_clk_src_signals if r == 1)
            total_clk_src = len(self.debug_clk_src_signals)
            self.log.info(f"  clk_src domain signal states:")
            self.log.info(f"    Valid high: {valid_high_count}/{total_clk_src} cycles ({valid_high_count/total_clk_src*100:.1f}%)")
            self.log.info(f"    Ready high: {ready_high_count}/{total_clk_src} cycles ({ready_high_count/total_clk_src*100:.1f}%)")

        if self.debug_clk_dst_signals:
            valid_high_count = sum(1 for _, _, v, _, _ in self.debug_clk_dst_signals if v == 1)
            ready_high_count = sum(1 for _, _, _, r, _ in self.debug_clk_dst_signals if r == 1)
            total_clk_dst = len(self.debug_clk_dst_signals)
            self.log.info(f"  clk_dst domain signal states:")
            self.log.info(f"    Valid high: {valid_high_count}/{total_clk_dst} cycles ({valid_high_count/total_clk_dst*100:.1f}%)")
            self.log.info(f"    Ready high: {ready_high_count}/{total_clk_dst} cycles ({ready_high_count/total_clk_dst*100:.1f}%)")

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
        if self.clk_src_transactions and self.clk_dst_transactions:
            min_count = min(len(self.clk_src_transactions), len(self.clk_dst_transactions))
            if min_count > 0:
                latencies = [
                    self.clk_dst_transactions[i][1] - self.clk_src_transactions[i][1]
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

    async def _monitor_clk_src_domain(self, cycles):
        # sourcery skip: use-contextlib-suppress
        """Monitor transactions in clock domain A"""
        self.log.debug(f"Monitoring clk_src domain for {cycles} cycles")

        for cycle in range(cycles):
            await RisingEdge(self.clk_src)

            valid = int(self.valid_src.value)
            ready = int(self.ready_src.value)
            data = int(self.data_src.value)
            time_ns = get_sim_time('ns')

            # Track all signal states for debugging
            self.debug_clk_src_signals.append((cycle, time_ns, valid, ready, data))

            # Record valid transactions (when valid and ready are both high)
            if valid and ready:
                self.clk_src_transactions.append((cycle, time_ns, data))
                self.log.debug(f"clk_src cycle {cycle}: Transaction @ {time_ns}ns (Valid={valid}, Ready={ready}, Data=0x{data:02x})")

                # Log internal state if available
                if self.internal_signals_available:
                    try:
                        state = int(self.r_src_state.value)
                        self.log.debug(f"  Source state: {state}")
                    except Exception:
                        pass

    async def _monitor_clk_dst_domain(self, cycles):
        """Monitor transactions in clock domain B"""
        self.log.debug(f"Monitoring clk_dst domain for {cycles} cycles")

        # Track valid pulses for verification
        valid_duration = 0
        valid_start_cycle = -1
        last_valid = 0

        for cycle in range(cycles):
            await RisingEdge(self.clk_dst)

            valid = int(self.valid_dst.value)
            ready = int(self.ready_dst.value)
            data = int(self.data_dst.value)
            time_ns = get_sim_time('ns')

            # Track all signal states for debugging
            self.debug_clk_dst_signals.append((cycle, time_ns, valid, ready, data))

            # Detect rising edge of valid
            if valid == 1 and last_valid == 0:
                valid_start_cycle = cycle
                valid_duration = 1
                self.log.debug(f"clk_dst cycle {cycle}: Valid pulse started @ {time_ns}ns")

            # Track ongoing valid pulse
            elif valid == 1:
                valid_duration += 1
            # Detect falling edge of valid (end of pulse)
            elif valid == 0 and last_valid == 1:
                self.valid_pulses.append((valid_start_cycle, cycle - 1))
                self.valid_pulse_durations.append(valid_duration)
                self.log.debug(f"clk_dst cycle {cycle}: Valid pulse ended, duration={valid_duration} @ {time_ns}ns")
                valid_duration = 0
                valid_start_cycle = -1

            last_valid = valid

            # Record valid transactions (when valid and ready are both high)
            if valid and ready:
                self.clk_dst_transactions.append((cycle, time_ns, data))
                self.log.debug(f"clk_dst cycle {cycle}: Transaction @ {time_ns}ns (Valid={valid}, Ready={ready}, Data=0x{data:02x})")

                # Log internal state if available
                if self.internal_signals_available:
                    with contextlib.suppress(Exception):
                        state = int(self.r_dst_state.value)
                        self.log.debug(f"  Destination state: {state}")
        # Handle case where valid is still high at end of monitoring
        if valid_start_cycle != -1:
            self.valid_pulses.append((valid_start_cycle, cycles - 1))
            self.valid_pulse_durations.append(valid_duration)
            self.log.debug(f"clk_dst end: Valid pulse still active, duration so far={valid_duration}")

    async def drive_single_handshake(self, data_value, ready_delay=0, preset_ready=False):
        """
        Drive a single valid/ready handshake

        Args:
            data_value: The data to send
            ready_delay: Number of cycles to delay ready_dst assertion after valid_dst
            preset_ready: If True, assumes ready_dst is already set externally

        Returns:
            True if handshake completed successfully
        """
        self.log.info(f"Starting single handshake with data=0x{data_value:02x}, ready_delay={ready_delay}, preset_ready={preset_ready}")

        # Calculate monitoring cycles based on clock frequencies and expected CDC latency
        clk_src_cycles = max(50, int(50 * self.clk_src_PERIOD_NS / 10))
        clk_dst_cycles = max(50, int(50 * self.clk_dst_PERIOD_NS / 10))

        # Start monitoring
        monitor_task = cocotb.start_soon(self.monitor_a_to_b(clk_src_cycles, clk_dst_cycles))

        # Only start the responder task if not using preset ready
        respond_task = None
        if not preset_ready:
            # Create a task to respond with ready_dst when valid_dst is detected
            async def respond_with_ready_dst():
                # Wait for valid_dst to be asserted
                while not self.done:
                    await RisingEdge(self.clk_dst)
                    if int(self.valid_dst.value) == 1:
                        break

                # Optional delay before asserting ready_dst
                for _ in range(ready_delay):
                    await RisingEdge(self.clk_dst)
                    if int(self.valid_dst.value) == 0:  # If valid_dst deasserts prematurely
                        self.log.error("valid_dst deasserted before ready_dst was asserted!")
                        return False

                # Assert ready_dst to accept the data
                self.ready_dst.value = 1

                # Wait one cycle and then deassert ready_dst
                await RisingEdge(self.clk_dst)
                self.ready_dst.value = 0

                return True

            # Start the responder task
            respond_task = cocotb.start_soon(respond_with_ready_dst())

        try:
            # Drive the handshake from domain A
            time_ns = get_sim_time('ns')
            self.log.debug(f'Driving valid_src and data=0x{data_value:02x} @ {time_ns}ns')

            # Assert valid_src and data
            self.data_src.value = data_value
            self.valid_src.value = 1

            # Wait for ready_src to be asserted (handshake completed in source domain)
            cycles_waited = 0
            max_wait_cycles = 5000  # Maximum cycles to wait

            while True:
                await RisingEdge(self.clk_src)
                cycles_waited += 1

                if int(self.ready_src.value) == 1:
                    time_ns = get_sim_time('ns')
                    self.log.debug(f"ready_src asserted after {cycles_waited} cycles @ {time_ns}ns")
                    break

                if cycles_waited >= max_wait_cycles:
                    self.log.error(f"ready_src not asserted after {max_wait_cycles} cycles!")
                    return False

            # Deassert valid_src after handshake completes
            self.valid_src.value = 0
            self.data_src.value = 0

            # Wait a bit to ensure all effects propagate
            await self.wait_clocks('clk_src', 10)
            await self.wait_clocks('clk_dst', 20)

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
            self.valid_src.value = 0
            self.data_src.value = 0

            # Don't deassert ready_dst if preset_ready was True
            # as it was set externally and should be cleared externally
            if not preset_ready:
                self.ready_dst.value = 0

    async def drive_multiple_handshakes(self, data_values, ready_delays=None, preset_ready_dst=False):
        """
        Drive multiple handshakes with different data values - robust implementation

        Args:
            data_values: List of data values to send
            ready_delays: List of ready_dst delay cycles (optional)
            preset_ready_dst: If True, sets ready_dst at the start to test ready-before-valid condition

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

        # Set up valid_dst response tracking
        valid_dst_response_needed = not preset_ready_dst
        valid_count = 0
        ready_dst_responder_active = True

        # If testing ready-before-valid, set ready_dst now
        if preset_ready_dst:
            self.ready_dst.value = 1

        # Launch a background task to monitor valid_dst and respond with ready_dst
        async def monitor_and_respond_to_valid_dst():
            nonlocal valid_count, ready_dst_responder_active

            # Keep running until we've seen all expected valid_dst pulses
            while valid_count < len(data_values) and ready_dst_responder_active:
                # Check for valid_dst assertion on every clk_dst edge
                await RisingEdge(self.clk_dst)

                if int(self.valid_dst.value) == 1:
                    # Log valid_dst detection
                    time_ns = get_sim_time('ns')
                    self.log.debug(f"valid_dst detected for transaction {valid_count+1} @ {time_ns}ns")

                    # Get delay for this transaction
                    delay = ready_delays[valid_count % len(ready_delays)]

                    # Apply configured delay before asserting ready_dst
                    for _ in range(delay):
                        await RisingEdge(self.clk_dst)
                        # Check if valid_dst deasserted during delay
                        if int(self.valid_dst.value) == 0:
                            self.log.error(f"valid_dst deasserted during ready delay (transaction {valid_count+1})")
                            return False

                    # Assert ready_dst to accept the data
                    self.ready_dst.value = 1
                    self.log.debug(f"Asserting ready_dst for transaction {valid_count+1}")

                    # Wait one cycle and then deassert ready_dst
                    await RisingEdge(self.clk_dst)
                    self.ready_dst.value = 0

                    # Count this valid-ready handshake
                    valid_count += 1

                    # Wait for valid_dst to deassert before looking for next transaction
                    while int(self.valid_dst.value) == 1 and ready_dst_responder_active:
                        await RisingEdge(self.clk_dst)

        # Only start the responder if we're not using preset_ready_dst
        ready_response_task = None
        if valid_dst_response_needed:
            ready_response_task = cocotb.start_soon(monitor_and_respond_to_valid_dst())

        all_successful = True

        try:
            # Send data values in sequence
            for i, data_value in enumerate(data_values):
                self.log.info(f"Sending data {i+1}/{len(data_values)}: 0x{data_value:02x}")

                # Drive the handshake from domain A
                time_ns = get_sim_time('ns')
                self.log.debug(f'Driving valid_src and data=0x{data_value:02x} @ {time_ns}ns')

                # Assert valid_src and data
                self.data_src.value = data_value
                self.valid_src.value = 1

                # Wait for ready_src to be asserted (handshake completed in source domain)
                cycles_waited = 0
                max_wait_cycles = 5000  # Maximum cycles to wait

                # Log state before waiting if debug signals available
                if self.internal_signals_available:
                    self.log.debug(f"Before waiting for ready_src: src_state={int(self.r_src_state.value)}, "
                                f"dst_state={int(self.r_dst_state.value)}, "
                                f"r_req_a={int(self.r_req_a.value)}, r_ack_b={int(self.r_ack_b.value)}")

                # Wait for ready_src with debug logging
                while True:
                    await RisingEdge(self.clk_src)
                    cycles_waited += 1

                    # Log periodic debug info
                    if cycles_waited % 100 == 0:
                        time_ns = get_sim_time('ns')
                        self.log.debug(f"Still waiting for ready_src: {cycles_waited} cycles @ {time_ns}ns")
                        # Log current state of key signals
                        if self.internal_signals_available:
                            self.log.debug(f"  Current states: src={int(self.r_src_state.value)}, dst={int(self.r_dst_state.value)}")
                            self.log.debug(f"  Control signals: req_a={int(self.r_req_a.value)}, ack_b={int(self.r_ack_b.value)}")
                            self.log.debug(f"  Interface signals: valid_dst={int(self.valid_dst.value)}, ready_dst={int(self.ready_dst.value)}")

                    if int(self.ready_src.value) == 1:
                        time_ns = get_sim_time('ns')
                        self.log.debug(f"ready_src asserted after {cycles_waited} cycles @ {time_ns}ns")
                        break

                    if cycles_waited >= max_wait_cycles:
                        time_ns = get_sim_time('ns')
                        self.log.error(f"ready_src not asserted after {max_wait_cycles} cycles for data {i+1} @ {time_ns}ns")
                        all_successful = False
                        break

                # Deassert valid_src after handshake completes
                self.valid_src.value = 0
                self.data_src.value = 0

                # Wait a reasonable amount of time between transactions
                # This helps prevent issues with back-to-back transactions
                await self.wait_clocks('clk_src', 5)

                # Break early if there was a failure and we're in basic test mode
                if not all_successful and self.TEST_LEVEL == 'basic':
                    break

            # Wait for all transactions to complete
            await monitor_task

            # Verify expected number of transactions occurred
            if len(self.clk_src_transactions) != expected_transactions:
                self.log.error(f"Transaction count mismatch in A domain: expected {expected_transactions}, got {len(self.clk_src_transactions)}")
                all_successful = False

            if len(self.clk_dst_transactions) != expected_transactions:
                self.log.error(f"Transaction count mismatch in B domain: expected {expected_transactions}, got {len(self.clk_dst_transactions)}")
                all_successful = False

            # Verify all data values were transferred correctly
            for i, ((_, _, data_src), (_, _, data_dst)) in enumerate(zip(self.clk_src_transactions, self.clk_dst_transactions)):
                if i < len(data_values) and (data_src != data_values[i] or data_dst != data_values[i]):
                    self.log.error(f"Data mismatch in transaction {i+1}: expected 0x{data_values[i]:02x}, got A=0x{data_src:02x}, B=0x{data_dst:02x}")
                    all_successful = False

            # Verify transaction ordering (B transactions must occur after A)
            for i, ((_, time_a, _), (_, time_b, _)) in enumerate(zip(self.clk_src_transactions, self.clk_dst_transactions)):
                if time_b <= time_a:
                    self.log.error(f"Transaction {i+1} timing error: A={time_a}ns, B={time_b}ns")
                    all_successful = False

        finally:
            # Clean up
            self.valid_src.value = 0
            self.data_src.value = 0

            # Ensure responder is stopped
            ready_dst_responder_active = False

            # Clear ready_dst if we set it
            if preset_ready_dst:
                self.ready_dst.value = 0

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
        clk_src_count = len(self.clk_src_transactions)
        clk_dst_count = len(self.clk_dst_transactions)

        self.log.info(f"Verifying handshake: clk_src_count={clk_src_count}, clk_dst_count={clk_dst_count}")

        if clk_src_count != clk_dst_count:
            self.log.error(f"Transaction count mismatch: clk_src={clk_src_count}, clk_dst={clk_dst_count}")
            return False

        if clk_src_count == 0:
            self.log.error("No transactions detected")
            return False

        # Verify data integrity
        if expected_data is not None:
            for i, (_, _, data_src) in enumerate(self.clk_src_transactions):
                if data_src != expected_data:
                    self.log.error(f"Data mismatch in clk_src transaction {i}: expected=0x{expected_data:02x}, actual=0x{data_src:02x}")
                    return False

            for i, (_, _, data_dst) in enumerate(self.clk_dst_transactions):
                if data_dst != expected_data:
                    self.log.error(f"Data mismatch in clk_dst transaction {i}: expected=0x{expected_data:02x}, actual=0x{data_dst:02x}")
                    return False

        # Verify data consistency between domains
        for i, ((_, _, data_src), (_, _, data_dst)) in enumerate(zip(self.clk_src_transactions, self.clk_dst_transactions)):
            if data_src != data_dst:
                self.log.error(f"Data mismatch in transaction {i}: A=0x{data_src:02x}, B=0x{data_dst:02x}")
                return False

        # Verify transaction ordering (clk_dst transactions should come after clk_src)
        for i, ((_, time_a, _), (_, time_b, _)) in enumerate(zip(self.clk_src_transactions, self.clk_dst_transactions)):
            if time_b <= time_a:
                self.log.error(f"Transaction {i} timing error: A={time_a}ns, B={time_b}ns")
                return False

        # Verify valid_dst pulse behavior
        if len(self.valid_pulses) != clk_src_count:
            self.log.error(f"Valid pulse count mismatch: detected {len(self.valid_pulses)}, expected {clk_src_count}")
            return False

        # All checks passed
        self.log.info("Handshake verification PASSED")
        return True

    async def run_back_pressure_test(self, data_value=0xA5):
        """
        Test back-pressure by incrementally increasing ready_dst delay

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
            self.log.info(f"Testing with ready_dst delay of {delay} cycles")

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
            await self.wait_clocks('clk_src', 5)
            await self.wait_clocks('clk_dst', 10)

        # Now, if still passing, test the preset ready scenario
        if all_passed and self.TEST_LEVEL != 'basic':
            self.log.info("Testing preset ready_dst scenario")
            await self.reset_dut()

            # Set ready_dst before driving valid
            self.ready_dst.value = 1

            # Wait a few cycles for stability
            await self.wait_clocks('clk_dst', 5)

            # Drive a handshake with preset ready
            success = await self.drive_single_handshake(data_value, 0, preset_ready=True)

            if not success:
                self.log.error("Back-pressure test failed with preset ready_dst")
                all_passed = False
            else:
                self.log.info("Back-pressure test passed with preset ready_dst")

            # Clear ready_dst for cleanup
            self.ready_dst.value = 0

        return all_passed

    async def run_clock_ratio_test(self):
        """
        Test across different clock frequency ratios

        Returns:
            True if all tests passed
        """
        # Use the currently configured clock ratio
        clk_src_period_ns = self.clk_src_PERIOD_NS
        clk_dst_period_ns = self.clk_dst_PERIOD_NS
        ratio = clk_dst_period_ns / clk_src_period_ns

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
            self.log.info(f"Using inter-transaction wait of {wait_cycles} clk_src cycles")

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
            await self.wait_clocks('clk_src', 10)
            await self.wait_clocks('clk_dst', 20)

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
            multi_test_passed = await self.drive_multiple_handshakes([0xA5, 0x5A, 0xC3, 0x3C], preset_ready_dst=False)
            if not multi_test_passed:
                self.log.error("Multiple handshakes test failed")
                all_passed = False

            # 2.5 Multiple handshakes test
            self.log.info("2.5 Running multiple handshakes test, preset ready_dst")
            await self.reset_dut()
            multi_test_passed = await self.drive_multiple_handshakes([0xA5, 0x5A, 0xC3, 0x3C], preset_ready_dst=True)
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
        ext_bp_test_passed = await self.drive_multiple_handshakes(data_values, ready_delays, preset_ready_dst=False)
        if not ext_bp_test_passed:
            self.log.error("Extended back-pressure test failed")
            all_passed = False

        # 5.5 Additional advanced tests for full test level
        self.log.info("5.1.5 Running additional tests for full test level, preset ready_dst")

        # Extended back-pressure test with multiple data values and longer delays
        self.log.info("5.1.5 Running extended back-pressure test, preset ready_dst")
        await self.reset_dut()
        data_values = [0x55, 0xAA, 0x33, 0xCC, 0xFF]
        ready_delays = [1, 5, 10, 15, 20]
        ext_bp_test_passed = await self.drive_multiple_handshakes(data_values, ready_delays, preset_ready_dst=True)
        if not ext_bp_test_passed:
            self.log.error("Extended back-pressure test failed with preset ready_dst")
            all_passed = False

        # Stress test with random data
        self.log.info("5.2 Running stress test with random data")
        await self.reset_dut()
        random_data = [random.randint(0, 255) for _ in range(20)]
        stress_test_passed = await self.drive_multiple_handshakes(random_data, preset_ready_dst=False)
        if not stress_test_passed:
            self.log.error("Stress test failed")
            all_passed = False

        # Stress test with random data
        self.log.info("5.2.5 Running stress test with random data, preset ready_dst")
        await self.reset_dut()
        random_data = [random.randint(0, 255) for _ in range(20)]
        stress_test_passed = await self.drive_multiple_handshakes(random_data, preset_ready_dst=True)
        if not stress_test_passed:
            self.log.error("Stress test with preset ready_dst failed")
            all_passed = False

        return all_passed


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = CDCValidReadyS2FTB(dut)

    # Start clocks with configured periods
    await tb.start_clock('clk_src', tb.clk_src_PERIOD_NS, 'ns')
    await tb.start_clock('clk_dst', tb.clk_dst_PERIOD_NS, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


@pytest.mark.parametrize("params", [

    # clk_src slower than clk_dst
    {'clk_src_period_ns':  15, 'clk_dst_period_ns': 10, 'test_level': 'full'}, # 'basic', 'medium', 'full'
    {'clk_src_period_ns':  20, 'clk_dst_period_ns': 10, 'test_level': 'full'},
    {'clk_src_period_ns':  50, 'clk_dst_period_ns': 10, 'test_level': 'full'},
    {'clk_src_period_ns': 100, 'clk_dst_period_ns': 10, 'test_level': 'full'},
    {'clk_src_period_ns': 200, 'clk_dst_period_ns': 10, 'test_level': 'full'},

    # # clk_src faster than clk_dst
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  15, 'test_level': 'full'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  20, 'test_level': 'full'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  50, 'test_level': 'full'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns': 100, 'test_level': 'full'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns': 200, 'test_level': 'full'},

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
    ratio = params['clk_src_period_ns'] / params['clk_dst_period_ns']

    t_clk_src = params['clk_src_period_ns']
    t_clk_dst = params['clk_dst_period_ns']
    t_name = params['test_level']
    test_name_plus_params = f"test_{dut_name}_clk_src{t_clk_src}_clk_dst{t_clk_dst}_{t_name}"
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
        'clk_src_PERIOD_NS': str(params['clk_src_period_ns']),
        'clk_dst_PERIOD_NS': str(params['clk_dst_period_ns'])
    }

    # Calculate timeout based on clock periods
    timeout_factor = max(1.0, t_clk_src / 10, t_clk_dst / 10) * 50
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
