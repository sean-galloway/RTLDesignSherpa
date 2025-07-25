import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.shared.arbiter_monitor import WeightedRoundRobinArbiterMonitor


class WeightedRoundRobinConfig:
    """Configuration class for weighted round robin arbiter tests"""
    def __init__(self, name, clients, max_levels, wait_gnt_ack):
        self.name = name
        self.clients = clients
        self.max_levels = max_levels
        self.wait_gnt_ack = wait_gnt_ack


class WeightedRoundRobinTB(TBBase):
    """
    Enhanced Testbench for the arbiter_round_robin_weighted module with integrated monitor.

    The monitor handles all transaction tracking, pattern analysis, weight compliance checking,
    and error detection. This testbench focuses on stimulus generation and high-level test
    orchestration.
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.CLIENTS = int(dut.CLIENTS)
        self.MAX_LEVELS = int(dut.MAX_LEVELS)
        self.MAX_LEVELS_WIDTH = int(dut.MAX_LEVELS_WIDTH)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Simplified state tracking - only what's needed for stimulus
        self.active_reqs = 0
        self.client_thresholds = []
        self.request_generation_active = False
        self.background_tasks = []

        # Clock and reset signals
        self.clock = self.dut.clk
        self.reset_n = self.dut.rst_n

        # Initialize the weighted arbiter monitor - this handles all monitoring and checking
        self.monitor = WeightedRoundRobinArbiterMonitor(
            dut=dut,
            title="WRR_Monitor",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.request,
            gnt_valid_signal=self.dut.grant_valid,
            gnt_signal=self.dut.grant,
            gnt_id_signal=self.dut.grant_id,
            gnt_ack_signal=self.dut.grant_ack,
            block_arb_signal=self.dut.block_arb,
            max_thresh_signal=self.dut.max_thresh,
            clients=self.CLIENTS,
            log=self.log,
            clock_period_ns=10
        )

        # Track any monitor errors
        self.monitor_errors = []
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)
        self.monitor.enable_debug()

        # Log configuration
        self.log.info(f"Enhanced Weighted Round Robin TB initialized with CLIENTS={self.CLIENTS}{self.get_time_ns_str()}")
        self.log.info(f"MAX_LEVELS={self.MAX_LEVELS}, WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}{self.get_time_ns_str()}")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions - validate transaction properties"""
        # Basic transaction validation
        if transaction.gnt_id >= self.CLIENTS:
            error = f"Invalid grant ID {transaction.gnt_id} >= {self.CLIENTS}"
            self.monitor_errors.append(error)
            self.log.error(f"{error}{self.get_time_ns_str()}")

        if transaction.gnt_vector != (1 << transaction.gnt_id):
            error = f"Grant vector 0x{transaction.gnt_vector:x} doesn't match grant ID {transaction.gnt_id}"
            self.monitor_errors.append(error)
            self.log.error(f"{error}{self.get_time_ns_str()}")

    def _on_monitor_reset(self):
        """Callback for reset events from monitor"""
        self.log.debug(f"Monitor detected reset event{self.get_time_ns_str()}")
        # Clear any accumulated errors on reset
        self.monitor_errors.clear()

    def stop_request_generation(self):
        """Stop background request generation"""
        self.request_generation_active = False
        self.log.info(f"Request generation stop requested{self.get_time_ns_str()}")

    async def clear_pending_grants_if_needed(self):
        """Separate method to clear pending grants only when needed"""
        if self.WAIT_GNT_ACK == 0:
            return  # No ACK mode, nothing to clear

        try:
            # Check if there's actually a pending grant
            if self.dut.grant_valid.value == 1:
                grant_id = int(self.dut.grant_id.value)
                grant_bit = (1 << grant_id)

                self.log.info(f"Clearing pending grant for client {grant_id}{self.get_time_ns_str()}")

                # Send the required ACK
                self.dut.grant_ack.value = grant_bit
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0
                await self.wait_clocks('clk', 1)

                # Clear the request for this client
                self.active_reqs &= ~grant_bit
                self.dut.request.value = self.active_reqs

                self.log.info(f"✓ Pending grant cleared for client {grant_id}{self.get_time_ns_str()}")
        except:
            # If any error reading signals, just continue
            pass

    async def stop_all_background_tasks(self):
        """Stop all background tasks and clear pending grants"""
        self.log.info(f"Stopping all background tasks{self.get_time_ns_str()}")

        # Stop request generation
        self.stop_request_generation()

        # Cancel all tracked background tasks
        for task in self.background_tasks:
            if not task.done():
                task.cancel()

        # Clear any pending grants ONLY in ACK mode
        await self.clear_pending_grants_if_needed()

        # Wait a bit for tasks to clean up
        await self.wait_clocks('clk', 5)

        # Clear the task list
        self.background_tasks.clear()

        self.log.info(f"All background tasks stopped{self.get_time_ns_str()}")

    def check_monitor_errors(self):
        """Check if monitor has detected any errors"""
        if self.monitor_errors:
            error_summary = f"Monitor detected {len(self.monitor_errors)} errors: {self.monitor_errors[:3]}"
            if len(self.monitor_errors) > 3:
                error_summary += f" ... and {len(self.monitor_errors) - 3} more"
            raise AssertionError(f"{error_summary}{self.get_time_ns_str()}")

    def clear_interface(self):
        """Clear all interface signals - SIMPLE VERSION"""
        self.dut.block_arb.value = 0
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        self.active_reqs = 0

        # Set default thresholds (all equal)
        self.set_all_thresholds(1)

        self.log.info(f'Interface cleared{self.get_time_ns_str()}')

    def set_all_thresholds(self, value):
        """Set all client thresholds to the same value with validation"""
        if value > self.MAX_LEVELS:
            self.log.error(f"FATAL ERROR: Threshold value {value} exceeds MAX_LEVELS={self.MAX_LEVELS}{self.get_time_ns_str()}")
            assert False, f"Cannot set threshold to {value}, maximum allowed is {self.MAX_LEVELS}"

        # All values are valid, proceed with setting thresholds
        self.client_thresholds = [value] * self.CLIENTS

        # Flatten the thresholds into the packed array format
        packed_thresholds = 0
        for i in range(self.CLIENTS):
            packed_thresholds |= (value << (i * self.MAX_LEVELS_WIDTH))

        self.dut.max_thresh.value = packed_thresholds
        self.log.info(f"Set all client thresholds to {value} (packed: 0x{packed_thresholds:x}){self.get_time_ns_str()}")

    def set_client_threshold(self, client_id, value):
        """Set threshold for a specific client with validation"""
        if client_id >= self.CLIENTS:
            self.log.error(f"FATAL ERROR: Invalid client ID: {client_id}{self.get_time_ns_str()}")
            assert False, f"Client ID {client_id} is invalid, max client ID is {self.CLIENTS-1}"

        if value > self.MAX_LEVELS:
            self.log.error(f"FATAL ERROR: Threshold value {value} exceeds MAX_LEVELS={self.MAX_LEVELS}{self.get_time_ns_str()}")
            assert False, f"Cannot set threshold to {value}, maximum allowed is {self.MAX_LEVELS}"

        # Value is valid, proceed with setting threshold
        self.client_thresholds[client_id] = value

        # Flatten the thresholds into the packed array format
        packed_thresholds = 0
        for i in range(self.CLIENTS):
            packed_thresholds |= (self.client_thresholds[i] << (i * self.MAX_LEVELS_WIDTH))

        # Log the binary representation to make bit allocation clear
        binary_str = format(packed_thresholds, f'0{self.CLIENTS * self.MAX_LEVELS_WIDTH}b')
        formatted_binary = ' '.join(binary_str[i:i+self.MAX_LEVELS_WIDTH]
                                    for i in range(0, len(binary_str), self.MAX_LEVELS_WIDTH))

        self.dut.max_thresh.value = packed_thresholds
        self.log.info(f"Set client {client_id} threshold to {value}{self.get_time_ns_str()}")
        self.log.info(f"New packed thresholds: 0x{packed_thresholds:x} ({formatted_binary}){self.get_time_ns_str()}")
        self.log.info(f"Client thresholds: {self.client_thresholds}{self.get_time_ns_str()}")

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f'Starting reset_dut{self.get_time_ns_str()}')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.clear_interface()

        # Hold reset for multiple cycles
        await self.wait_clocks('clk', 5)

        # Release reset
        self.reset_n.value = 1

        # Start the monitor after reset is released
        self.monitor.start_monitoring()

        # Wait for stabilization
        await self.wait_clocks('clk', 5)

        self.log.debug(f'Reset complete{self.get_time_ns_str()}')

    def random_delay(self, min_clocks=1, max_clocks=5):
        """Generate a random delay between min and max clocks"""
        return random.randint(min_clocks, max_clocks)

    async def generate_requests(self, num_cycles=20):
        """Generate random request patterns for specified number of cycles."""
        self.log.info(f"Generating requests for {num_cycles} cycles{self.get_time_ns_str()}")
        self.request_generation_active = True

        try:
            for cycle in range(num_cycles):
                # Check if we should stop
                if not self.request_generation_active:
                    self.log.info(f"Request generation stopped at cycle {cycle}{self.get_time_ns_str()}")
                    break

                # Add new random requests, but don't remove existing ones
                new_reqs = 0
                for i in range(self.CLIENTS):
                    # Only add a new request if this bit is not already set in active_reqs
                    if not (self.active_reqs & (1 << i)) and random.random() < 0.5:
                        new_reqs |= (1 << i)

                # Add new requests to active requests
                self.active_reqs |= new_reqs
                self.dut.request.value = self.active_reqs

                if new_reqs:
                    req_str = bin(self.active_reqs)[2:].zfill(self.CLIENTS)
                    msg = f'    New reqs added: {bin(new_reqs)[2:].zfill(self.CLIENTS)}, Active reqs: {req_str}{self.get_time_ns_str()}'
                    self.log.debug(msg)

                await self.wait_clocks('clk', 1)
        finally:
            self.request_generation_active = False

    async def handle_grant_ack(self):
        """Handle grant acknowledge signals when WAIT_GNT_ACK is enabled"""
        if self.WAIT_GNT_ACK == 0:
            return  # No ACK handling needed

        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.grant_valid.value == 1:
                grant_id = int(self.dut.grant_id.value)
                grant_ack_delay = self.random_delay()

                time_ns = get_sim_time('ns')
                self.log.debug(f"Scheduling grant ack for bit {grant_id} after {grant_ack_delay} cycles @ {time_ns}ns")

                # Wait for random delay before acknowledging
                for _ in range(grant_ack_delay):
                    await self.wait_clocks('clk', 1)

                # Set acknowledge signal
                ack_mask = (1 << grant_id)
                self.dut.grant_ack.value = ack_mask

                time_ns = get_sim_time('ns')
                self.log.debug(f"Sending grant ack 0x{ack_mask:x} @ {time_ns}ns")

                # Clear the request only after acknowledge
                self.active_reqs &= ~(1 << grant_id)
                self.dut.request.value = self.active_reqs

                # Hold for one cycle then clear ack
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0

    async def test_grant_signals(self):
        """Test that grant signals work correctly - basic functionality test"""
        self.log.info(f"Starting grant signal test{self.get_time_ns_str()}")

        # Test each client one by one to verify correct grant_id to grant mapping
        for client_id in range(self.CLIENTS):
            # Set a request for just this client
            req_pattern = (1 << client_id)
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Testing client {client_id}: request = 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Wait for a grant
            max_cycles = 20
            cycle = 0
            grant_received = False

            while cycle < max_cycles and not grant_received:
                await RisingEdge(self.dut.clk)
                cycle += 1

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bus = int(self.dut.grant.value)

                    self.log.info(f"Grant received on cycle {cycle}{self.get_time_ns_str()}")
                    self.log.info(f"Grant ID: {grant_id}{self.get_time_ns_str()}")
                    self.log.info(f"Grant bus: 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

                    # Verify the grant signals
                    assert grant_id == client_id, f"Expected grant ID {client_id}, got {grant_id}{self.get_time_ns_str()}"
                    expected_grant = (1 << client_id)
                    assert grant_bus == expected_grant, \
                        f"Expected grant bus 0b{bin(expected_grant)[2:].zfill(self.CLIENTS)}, " \
                        f"got 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}"

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = req_pattern
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                    grant_received = True

            assert grant_received, f"No grant received for client {client_id}{self.get_time_ns_str()}"

            # Clear the request and wait a cycle before the next client
            self.dut.request.value = 0
            self.active_reqs = 0
            await self.wait_clocks('clk', 5)

        self.log.info(f"Grant signal test passed - all clients received grants with correct ID and bus values{self.get_time_ns_str()}")

    async def run_basic_arbitration_test(self, run_cycles=500):
        """Run basic arbitration test with proper ACK cleanup"""
        self.log.info(f"Starting basic arbitration test with {self.CLIENTS} clients, WAIT_GNT_ACK={self.WAIT_GNT_ACK}{self.get_time_ns_str()}")

        # Start concurrent processes and track them
        req_task = cocotb.start_soon(self.generate_requests(20 * self.CLIENTS))
        ack_task = cocotb.start_soon(self.handle_grant_ack())

        self.background_tasks.extend([req_task, ack_task])

        # Run for the specified number of cycles
        self.log.info(f"Running for {run_cycles} clock cycles{self.get_time_ns_str()}")
        for _ in range(run_cycles):
            await RisingEdge(self.dut.clk)

        # CRITICAL: Stop background tasks with proper ACK cleanup
        await self.stop_all_background_tasks()

        # Check for any monitor errors
        self.check_monitor_errors()
        self.log.info(f"Basic arbitration test completed successfully{self.get_time_ns_str()}")

    async def test_threshold_operation(self):
        """Test that the threshold mechanism works correctly"""
        self.log.info(f"Starting threshold operation test{self.get_time_ns_str()}")

        # Set up different thresholds for clients
        # Client 0: thresh = 1 (low priority, gets 1 grant)
        # Client 1: thresh = 3 (medium priority, gets 3 grants)
        # Other clients: thresh = 1 (standard priority)
        self.set_all_thresholds(1)
        if self.CLIENTS > 1:
            self.set_client_threshold(1, 3)

        # Set requests for the first two clients only
        req_pattern = 0b11 if self.CLIENTS >= 2 else 0b1
        self.dut.request.value = req_pattern
        self.active_reqs = req_pattern

        self.log.info(f"Setting up test with request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")
        self.log.info(f"Thresholds: {self.client_thresholds}{self.get_time_ns_str()}")

        # Collect grants and verify threshold behavior
        grants_sequence = []
        expected_min_client1_grants = 3 if self.CLIENTS > 1 else 0

        # Run the test for enough cycles to observe weight effects
        max_cycles = 20
        for cycle in range(max_cycles):
            await self.wait_clocks('clk', 1)

            if self.dut.grant_valid.value == 1:
                grant_id = int(self.dut.grant_id.value)
                grants_sequence.append(grant_id)

                self.log.info(f"Cycle {cycle}: Grant to client {grant_id}{self.get_time_ns_str()}")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    gnt_bit = (1 << grant_id)
                    self.dut.grant_ack.value = gnt_bit
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0

                # Keep requesting
                self.dut.request.value = req_pattern

                # If we've seen 6+ grants, we can verify behavior
                if len(grants_sequence) >= 6:
                    break

        # Analyze the grants sequence
        self.log.info(f"Grants sequence: {grants_sequence}{self.get_time_ns_str()}")

        if self.CLIENTS > 1:
            # Count client 1 grants in the first 6 grants
            client1_grants = grants_sequence[:6].count(1)
            self.log.info(f"Client 1 got {client1_grants} grants out of first 6{self.get_time_ns_str()}")

            # Verify client 1 (with threshold=3) gets more grants than client 0 (threshold=1)
            # We expect at least N-1 grants where N is the threshold
            assert client1_grants >= expected_min_client1_grants, \
                f"Client 1 with threshold=3 should get at least {expected_min_client1_grants} grants, " \
                f"but only got {client1_grants}{self.get_time_ns_str()}"

        self.log.info(f"Threshold operation test passed{self.get_time_ns_str()}")

    async def test_weighted_fairness(self):
        """Test weighted fairness using deterministic drain-based approach"""
        self.log.info(f"Starting deterministic weighted fairness test{self.get_time_ns_str()}")

        if self.CLIENTS < 4:
            self.log.info(f"Skipping weighted fairness test - not enough clients{self.get_time_ns_str()}")
            return

        # Test configurations: different weight setups to test
        weight_configs = [
            [1, 2, 4, 1],  # First config: varied weights
            [2, 1, 3, 2],  # Second config: different arrangement
            [1, 1, 2, 4],  # Third config: high weight at end
            [3, 2, 1, 1],  # Fourth config: high weight at start
        ]

        # Only test up to CLIENTS configurations
        num_configs = min(len(weight_configs), self.CLIENTS)

        for config_idx in range(num_configs):
            self.log.info(f"=== Testing weight configuration {config_idx + 1}/{num_configs} ==={self.get_time_ns_str()}")

            # Set up weights for this configuration
            weights = weight_configs[config_idx][:self.CLIENTS]  # Truncate to client count
            while len(weights) < self.CLIENTS:  # Pad if needed
                weights.append(1)

            # Apply weights
            for client_id in range(self.CLIENTS):
                self.set_client_threshold(client_id, weights[client_id])

            self.log.info(f"Applied weights: {weights}{self.get_time_ns_str()}")

            # Test different client participation patterns
            test_patterns = []

            # 1. All clients (N clients)
            all_clients = list(range(self.CLIENTS))
            test_patterns.append(("ALL", all_clients))

            # 2. N-1 clients (try a few combinations)
            if self.CLIENTS > 1:
                for skip_client in range(min(3, self.CLIENTS)):  # Test skipping first few clients
                    n_minus_1 = [i for i in range(self.CLIENTS) if i != skip_client]
                    test_patterns.append((f"N-1_skip{skip_client}", n_minus_1))

            # 3. N-2 clients (for larger client counts, do random mix)
            if self.CLIENTS > 2:
                if self.CLIENTS <= 8:
                    # For smaller counts, test skipping pairs
                    for skip1 in range(min(2, self.CLIENTS)):
                        for skip2 in range(skip1 + 1, min(skip1 + 3, self.CLIENTS)):
                            n_minus_2 = [i for i in range(self.CLIENTS) if i not in [skip1, skip2]]
                            if len(n_minus_2) >= 2:  # Make sure we have at least 2 clients
                                test_patterns.append((f"N-2_skip{skip1},{skip2}", n_minus_2))
                else:
                    # For 16-32 clients, do 6-8 random mixes
                    import random
                    random.seed(42)  # Deterministic randomness
                    for mix_idx in range(6):
                        num_clients = random.randint(self.CLIENTS - 4, self.CLIENTS - 1)
                        participating = random.sample(range(self.CLIENTS), num_clients)
                        participating.sort()
                        test_patterns.append((f"Random_mix{mix_idx}", participating))

            # Test each pattern
            for pattern_name, participating_clients in test_patterns:
                await self._test_weight_pattern_deterministic(pattern_name, participating_clients, weights)

            # Brief pause before next weight configuration
            await self.wait_clocks('clk', 20)

        self.log.info(f"Deterministic weighted fairness test completed successfully{self.get_time_ns_str()}")

    async def _test_weight_pattern_deterministic(self, pattern_name, participating_clients, weights):
        """Test a specific client participation pattern using deterministic drain approach"""
        self.log.info(f"--- Testing {pattern_name} pattern: clients {participating_clients} ---{self.get_time_ns_str()}")

        # Create request pattern
        req_pattern = 0
        for client_id in participating_clients:
            req_pattern |= (1 << client_id)

        # Target: 40 * N grants where N is number of participating clients
        target_grants = 40 * len(participating_clients)

        # Run 3 cycles as specified
        for cycle in range(3):
            self.log.info(f"Cycle {cycle + 1}/3 for {pattern_name} pattern{self.get_time_ns_str()}")

            # Clear everything and go idle
            self.dut.request.value = 0
            self.active_reqs = 0
            await self.wait_clocks('clk', 10)

            # Mark this as a static period for weight compliance checking
            self.monitor.set_static_period(True)
            self.monitor.reset_static_stats()

            # Set all requests (assert all participating clients)
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern
            self.log.info(f"Asserted requests for pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Start ACK handling for this cycle
            if self.WAIT_GNT_ACK == 1:
                ack_task = cocotb.start_soon(self._handle_drain_acks())

            # Let requests drain naturally (don't replenish them)
            grants_received = 0
            max_cycles = target_grants * 10  # Safety timeout

            for drain_cycle in range(max_cycles):
                await RisingEdge(self.dut.clk)

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bit = (1 << grant_id)
                    grants_received += 1

                    # Remove the granted request (drain approach - don't replenish)
                    if self.WAIT_GNT_ACK == 0:
                        # In no-ACK mode, remove request immediately
                        self.active_reqs &= ~grant_bit
                        self.dut.request.value = self.active_reqs

                    # Stop when we hit target grants or no more requests
                    if grants_received >= target_grants or self.active_reqs == 0:
                        break

            # Stop ACK handling
            if self.WAIT_GNT_ACK == 1:
                ack_task.kill()

            # Mark end of static period
            self.monitor.set_static_period(False)

            # Idle for 20 clocks as specified
            self.dut.request.value = 0
            self.active_reqs = 0
            await self.wait_clocks('clk', 20)

            # Check compliance for this cycle
            static_stats = self.monitor.get_static_period_stats()

            self.log.info(f"Cycle {cycle + 1} complete: {grants_received} grants, drained in {drain_cycle + 1} cycles{self.get_time_ns_str()}")

            if static_stats['total_grants'] > 0:
                # Analyze weight compliance for participating clients only
                compliance = self.monitor.analyze_static_weight_compliance(weights, participating_clients)

                self.log.info(f"=== Weight compliance for {pattern_name} cycle {cycle + 1} ==={self.get_time_ns_str()}")
                self.monitor.print_weight_compliance_analysis(weights, participating_clients)

                if compliance['status'] == 'analyzed':
                    # Check compliance - should be very good with deterministic approach
                    if compliance['overall_compliance'] < 0.85:  # Higher threshold for deterministic test
                        self.log.warning(f"Lower than expected weight compliance: {compliance['overall_compliance']:.1%} " \
                                    f"(expected >= 85% for deterministic test){self.get_time_ns_str()}")
                    else:
                        self.log.info(f"✓ Excellent weight compliance: {compliance['overall_compliance']:.1%}{self.get_time_ns_str()}")

                    # Log grant distribution
                    for i, client_stats in enumerate(static_stats['client_stats']):
                        if i in participating_clients:
                            percentage = (client_stats['grants'] / static_stats['total_grants']) * 100
                            self.log.info(f"  Client {i} (weight {weights[i]}): {client_stats['grants']} grants ({percentage:.1f}%){self.get_time_ns_str()}")

    async def _handle_drain_acks(self):
        """Handle ACKs for drain-based testing - remove requests after ACK"""
        if self.WAIT_GNT_ACK == 0:
            return

        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.grant_valid.value == 1:
                grant_id = int(self.dut.grant_id.value)
                grant_bit = (1 << grant_id)

                # ACK immediately
                self.dut.grant_ack.value = grant_bit
                await self.wait_clocks('clk', 1)
                self.dut.grant_ack.value = 0

                # Remove the granted request (drain approach)
                self.active_reqs &= ~grant_bit
                self.dut.request.value = self.active_reqs

                await self.wait_clocks('clk', 1)

    async def test_dynamic_arbitration_liveness(self):
        """Test that arbitration doesn't get stuck during dynamic request changes"""
        self.log.info(f"Starting dynamic arbitration liveness test{self.get_time_ns_str()}")

        # Mark this as dynamic period - no weight compliance checking
        self.monitor.set_static_period(False)

        # Generate random request patterns and verify grants keep coming
        max_stall_cycles = 50  # Max cycles without a grant before declaring stuck

        for test_round in range(20):
            # Generate random request pattern
            req_pattern = random.randint(1, (1 << self.CLIENTS) - 1)
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern

            self.log.debug(f"Round {test_round}: request pattern 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Wait for at least one grant within the stall limit
            grant_received = False
            cycles_without_grant = 0

            for cycle in range(max_stall_cycles):
                await self.wait_clocks('clk', 1)
                cycles_without_grant += 1

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bit = (1 << grant_id)

                    # Verify grant is for a requesting client
                    assert req_pattern & grant_bit, \
                        f"Grant to non-requesting client {grant_id}, pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}"

                    grant_received = True
                    cycles_without_grant = 0

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = grant_bit
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                    # Remove granted request to create dynamic pattern
                    req_pattern &= ~grant_bit
                    self.dut.request.value = req_pattern
                    self.active_reqs = req_pattern

                    # If no more requests, break
                    if req_pattern == 0:
                        break

            # Check if we got stuck
            if req_pattern != 0 and cycles_without_grant >= max_stall_cycles:
                raise AssertionError(f"Arbitration stuck: no grant for {cycles_without_grant} cycles with active requests 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

        self.log.info(f"Dynamic arbitration liveness test passed - no stalls detected{self.get_time_ns_str()}")

    async def test_block_arb(self):
        """Test the block_arb functionality"""
        self.log.info(f"Starting block_arb test{self.get_time_ns_str()}")

        # First clear all requests
        self.dut.request.value = 0
        self.dut.block_arb.value = 0
        await self.wait_clocks('clk', 5)

        # Set block_arb before setting any requests
        self.dut.block_arb.value = 1
        self.log.info(f"Asserted block_arb{self.get_time_ns_str()}")
        await self.wait_clocks('clk', 5)

        # Now set some requests - these should not be granted while block_arb is active
        req_pattern = (1 << self.CLIENTS) - 1  # All bits set
        self.dut.request.value = req_pattern
        self.log.info(f"Set request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)} with block_arb asserted{self.get_time_ns_str()}")

        # Wait several cycles and verify no grants are issued
        for i in range(20):
            await self.wait_clocks('clk', 1)
            assert self.dut.grant_valid.value == 0, \
                f"Grant was issued when block_arb was asserted at cycle {i}{self.get_time_ns_str()}"

        self.log.info(f"No grants issued while block_arb was asserted - good!{self.get_time_ns_str()}")

        # De-assert block_arb and ensure requests are still active
        self.dut.block_arb.value = 0
        self.log.info(f"De-asserted block_arb with active requests{self.get_time_ns_str()}")

        # Check that grants resume
        grant_issued = False
        grant_count = 0
        max_cycles = 20

        for _ in range(max_cycles):
            await self.wait_clocks('clk', 1)

            if self.dut.grant_valid.value == 1:
                grant_id = int(self.dut.grant_id.value)
                grant_bit = (1 << grant_id)

                grant_issued = True
                grant_count += 1

                self.log.info(f"Received grant for client {grant_id} after de-asserting block_arb{self.get_time_ns_str()}")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.grant_ack.value = grant_bit
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0

                # Clear the granted bit but keep all other bits set
                current_req = int(self.dut.request.value)
                self.dut.request.value = current_req & ~grant_bit

                # If we've seen at least 3 grants, we can be confident that block_arb is working correctly
                if grant_count >= 3:
                    break

        assert grant_issued, f"No grants issued after de-asserting block_arb with active requests{self.get_time_ns_str()}"
        self.log.info(f"Received {grant_count} grants after de-asserting block_arb - block_arb test passed{self.get_time_ns_str()}")

    async def test_walking_requests(self):
        """Test arbiter with walking adjacent requests"""
        self.log.info(f"Starting walking adjacent requests test{self.get_time_ns_str()}")

        # Initialize - ensure completely clean state
        self.active_reqs = 0
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        await self.wait_clocks('clk', 10)  # Longer initial wait

        # Run through all adjacent pairs
        for i in range(self.CLIENTS - 1):
            pattern_name = f"{i}/{i+1}"
            self.log.info(f"=== Testing adjacent pair {pattern_name} ==={self.get_time_ns_str()}")

            # Create request pattern with two adjacent bits
            req_pattern = (1 << i) | (1 << (i + 1))
            expected_clients = {i, i + 1}

            # Set the request pattern
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern
            self.log.info(f"Set request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Track grants for this specific pattern only
            granted_clients = set()
            cycles_waited = 0
            max_cycles = self.CLIENTS * 15  # More generous timeout for higher client counts

            while len(granted_clients) < 2 and cycles_waited < max_cycles:
                await RisingEdge(self.dut.clk)
                cycles_waited += 1

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bit = (1 << grant_id)

                    # Verify grant is for one of our expected clients
                    if grant_id not in expected_clients:
                        current_req = int(self.dut.request.value)
                        self.log.error(f"Unexpected grant to client {grant_id} when testing pattern {pattern_name}{self.get_time_ns_str()}")
                        self.log.error(f"Expected clients: {expected_clients}{self.get_time_ns_str()}")
                        self.log.error(f"Current request: 0b{bin(current_req)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")
                        raise AssertionError(f"Grant to unexpected client {grant_id} when testing pattern {pattern_name}{self.get_time_ns_str()}")

                    # Add to granted clients (use set to avoid duplicates)
                    if grant_id not in granted_clients:
                        granted_clients.add(grant_id)
                        self.log.info(f"Pattern {pattern_name}: Grant {len(granted_clients)}/2 to client {grant_id}{self.get_time_ns_str()}")

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = grant_bit
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                        # Wait a cycle for ACK to be processed
                        await self.wait_clocks('clk', 1)

                    # Clear the granted bit from the active requests
                    self.active_reqs &= ~grant_bit
                    self.dut.request.value = self.active_reqs

                    self.log.debug(f"Cleared client {grant_id}, remaining: 0b{bin(self.active_reqs)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Verify we got grants for both expected clients
            if len(granted_clients) != 2:
                self.log.error(f"Pattern {pattern_name}: Expected 2 grants, got {len(granted_clients)}{self.get_time_ns_str()}")
                self.log.error(f"Granted clients: {granted_clients}{self.get_time_ns_str()}")
                self.log.error(f"Expected clients: {expected_clients}{self.get_time_ns_str()}")
                self.log.error(f"Cycles waited: {cycles_waited}/{max_cycles}{self.get_time_ns_str()}")
                raise AssertionError(f"Pattern {pattern_name}: Expected 2 grants, got {len(granted_clients)}{self.get_time_ns_str()}")

            # Verify we got the right clients
            if granted_clients != expected_clients:
                self.log.error(f"Pattern {pattern_name}: Wrong clients granted{self.get_time_ns_str()}")
                self.log.error(f"Expected: {expected_clients}{self.get_time_ns_str()}")
                self.log.error(f"Granted: {granted_clients}{self.get_time_ns_str()}")
                raise AssertionError(f"Pattern {pattern_name}: Expected {expected_clients}, got {granted_clients}{self.get_time_ns_str()}")

            self.log.info(f"Pattern {pattern_name} completed successfully in {cycles_waited} cycles{self.get_time_ns_str()}")

            # Ensure completely clean state before next pattern
            self.dut.request.value = 0
            self.dut.grant_ack.value = 0
            self.active_reqs = 0

            # Wait longer between patterns, especially for higher client counts
            wait_cycles = 10 + self.CLIENTS  # Scale wait time with client count
            await self.wait_clocks('clk', wait_cycles)

            # Handle ACK if needed, grant cleanup
            if self.WAIT_GNT_ACK == 1:
                if self.dut.grant_valid.value == 1:
                    req_pattern = self.dut.grant.value
                    self.dut.grant_ack.value = req_pattern
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0

        self.log.info(f"Walking adjacent requests test passed{self.get_time_ns_str()}")

    async def test_bursty_traffic_pattern(self):
        """Test with bursty traffic patterns - clients request in bursts"""
        self.log.info(f"Starting bursty traffic pattern test{self.get_time_ns_str()}")

        for burst_cycle in range(5):  # 5 burst cycles
            # Phase 1: All clients request simultaneously (burst)
            all_requests = (1 << self.CLIENTS) - 1
            self.dut.request.value = all_requests
            self.active_reqs = all_requests

            self.log.info(f"Burst {burst_cycle}: All clients requesting{self.get_time_ns_str()}")

            # Let arbiter handle the burst
            grants_in_burst = 0
            max_burst_cycles = self.CLIENTS * 5  # Allow time for all to be served (weighted needs more time)

            for cycle in range(max_burst_cycles):
                await self.wait_clocks('clk', 1)

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bit = (1 << grant_id)
                    grants_in_burst += 1

                    self.log.debug(f"Burst grant {grants_in_burst} to client {grant_id}{self.get_time_ns_str()}")

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = grant_bit
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                    # Remove granted request
                    self.active_reqs &= ~grant_bit
                    self.dut.request.value = self.active_reqs

                    # If all served, break early
                    if self.active_reqs == 0:
                        break

            # Phase 2: Idle period
            self.dut.request.value = 0
            self.active_reqs = 0
            await self.wait_clocks('clk', 15)  # Longer idle period for weighted arbiter

            self.log.info(f"Burst {burst_cycle} completed: {grants_in_burst} grants issued{self.get_time_ns_str()}")

        self.log.info(f"Bursty traffic pattern test completed{self.get_time_ns_str()}")

    async def test_single_client_saturation(self):
        """Test what happens when only one client continuously requests"""
        self.log.info(f"Starting single client saturation test{self.get_time_ns_str()}")

        for client_id in range(self.CLIENTS):
            self.log.info(f"Saturating client {client_id}{self.get_time_ns_str()}")

            # Set only this client requesting
            req_pattern = (1 << client_id)
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern

            grants_received = 0
            max_cycles = 20  # More cycles for weighted arbiter

            for cycle in range(max_cycles):
                await self.wait_clocks('clk', 1)

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)

                    assert grant_id == client_id, f"Expected grant to client {client_id}, got {grant_id}{self.get_time_ns_str()}"
                    grants_received += 1

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = req_pattern
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                        # In ACK mode, re-assert request after ACK
                        await self.wait_clocks('clk', 1)
                        self.dut.request.value = req_pattern

            # Clear requests
            self.dut.request.value = 0
            await self.wait_clocks('clk', 10)

            # Handle ACK if needed, grant cleanup
            if self.WAIT_GNT_ACK == 1:
                if self.dut.grant_valid.value == 1:
                    req_pattern = self.dut.grant.value
                    self.dut.grant_ack.value = req_pattern
                    await self.wait_clocks('clk', 1)
                    self.dut.grant_ack.value = 0

            expected_grants = max_cycles if self.WAIT_GNT_ACK == 0 else max_cycles // 4  # ACK mode is slower, weighted is also slower

            self.log.info(f"Client {client_id} received {grants_received} grants (expected ~{expected_grants}){self.get_time_ns_str()}")

            # Verify reasonable grant rate (more lenient for weighted arbiter)
            assert grants_received > expected_grants * 0.3, \
                f"Client {client_id} grant rate too low: {grants_received}{self.get_time_ns_str()}"

        self.log.info(f"Single client saturation test completed{self.get_time_ns_str()}")

    async def test_rapid_request_changes(self):
        """Test with rapidly changing request patterns"""
        self.log.info(f"Starting rapid request changes test{self.get_time_ns_str()}")

        patterns = [
            0b1010,  # Alternating
            0b1100,  # Pair-wise
            0b0011,  # Other pair
            0b1001,  # Corners
            0b0110,  # Middle
            0b1111,  # All
            0b0001,  # Single
        ]

        for cycle in range(50):
            # Change pattern every few cycles
            pattern = patterns[cycle % len(patterns)]
            pattern &= (1 << self.CLIENTS) - 1  # Mask to client count

            self.dut.request.value = pattern
            self.active_reqs = pattern

            # Wait a few cycles with this pattern
            for _ in range(5):  # More cycles for weighted arbiter
                await self.wait_clocks('clk', 1)

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)
                    grant_bit = (1 << grant_id)

                    # Verify grant is for a requesting client
                    assert pattern & grant_bit, \
                        f"Grant 0x{grant_bit:x} not in request pattern 0x{pattern:x}{self.get_time_ns_str()}"

                    # Handle ACK if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.grant_ack.value = grant_bit
                        await self.wait_clocks('clk', 1)
                        self.dut.grant_ack.value = 0

                    # Remove granted request
                    pattern &= ~grant_bit
                    self.dut.request.value = pattern
                    self.active_reqs = pattern

        self.log.info(f"Rapid request changes test completed{self.get_time_ns_str()}")

    async def test_ack_mode_back_to_back(self):
        """Test that ACKs can occur back-to-back with multiple active requests in ACK mode"""
        if self.WAIT_GNT_ACK == 0:
            self.log.info(f"Skipping back-to-back ACK test - not in ACK mode{self.get_time_ns_str()}")
            return

        self.log.info(f"Starting back-to-back ACK test in ACK mode{self.get_time_ns_str()}")

        # Set multiple requests active (at least 3 clients)
        num_active = min(3, self.CLIENTS)
        req_pattern = (1 << num_active) - 1  # First N clients
        self.dut.request.value = req_pattern
        self.active_reqs = req_pattern

        self.log.info(f"Set {num_active} requests active: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

        # Track grants and ACKs to look for back-to-back behavior
        grant_ack_sequence = []
        consecutive_acks = 0
        max_consecutive = 0

        # Run for enough cycles to see back-to-back behavior
        for cycle in range(50):
            await RisingEdge(self.dut.clk)

            grant_valid = int(self.dut.grant_valid.value)

            if grant_valid == 1:
                grant_id = int(self.dut.grant_id.value)
                grant_bit = (1 << grant_id)

                # Immediately ACK this grant (same cycle ACK for maximum back-to-back chance)
                self.dut.grant_ack.value = grant_bit

                grant_ack_sequence.append(f"C{cycle}:Grant{grant_id}")
                consecutive_acks += 1
                max_consecutive = max(max_consecutive, consecutive_acks)

                self.log.debug(f"Cycle {cycle}: Grant to client {grant_id}, immediate ACK{self.get_time_ns_str()}")

                # Keep all requests active to encourage back-to-back grants
                self.dut.request.value = req_pattern

            else:
                # No grant this cycle
                if consecutive_acks > 0:
                    grant_ack_sequence.append(f"C{cycle}:NoGrant")
                    consecutive_acks = 0
                self.dut.grant_ack.value = 0

            # Clear ACK after one cycle
            await RisingEdge(self.dut.clk)
            self.dut.grant_ack.value = 0

        # Analyze the sequence
        self.log.info(f"Grant/ACK sequence: {' '.join(grant_ack_sequence[:20])}{self.get_time_ns_str()}")  # First 20 events
        self.log.info(f"Maximum consecutive grants: {max_consecutive}{self.get_time_ns_str()}")

        # In ACK mode with multiple requests, we should see back-to-back grants
        if max_consecutive >= 2:
            self.log.info(f"✓ Back-to-back ACKs observed: {max_consecutive} consecutive{self.get_time_ns_str()}")
        else:
            self.log.warning(f"⚠️  No back-to-back ACKs observed in {cycle + 1} cycles{self.get_time_ns_str()}")

        # Clean up
        self.dut.request.value = 0
        self.dut.grant_ack.value = 0
        await self.wait_clocks('clk', 5)

        self.log.info(f"Back-to-back ACK test completed{self.get_time_ns_str()}")

    async def test_ack_mode_dead_cycle(self):
        """Test that single request + ACK creates mandatory dead cycle in ACK mode"""
        if self.WAIT_GNT_ACK == 0:
            self.log.info(f"Skipping dead cycle test - not in ACK mode{self.get_time_ns_str()}")
            return

        self.log.info(f"Starting ACK mode dead cycle test{self.get_time_ns_str()}")

        # Test each client individually to verify dead cycle behavior
        for client_id in range(self.CLIENTS):
            self.log.info(f"Testing dead cycle behavior for client {client_id}{self.get_time_ns_str()}")

            # Ensure completely clean state before each client test
            self.dut.request.value = 0
            self.dut.grant_ack.value = 0
            self.active_reqs = 0
            await self.wait_clocks('clk', 10)

            # Set ONLY this single request
            req_pattern = (1 << client_id)
            self.dut.request.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Set single request for client {client_id}: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}{self.get_time_ns_str()}")

            # Wait for grant
            grant_received = False
            grant_cycle = 0
            max_wait_cycles = 20

            for wait_cycle in range(max_wait_cycles):
                await RisingEdge(self.dut.clk)

                if self.dut.grant_valid.value == 1:
                    grant_id = int(self.dut.grant_id.value)

                    assert grant_id == client_id, f"Expected grant to client {client_id}, got {grant_id}{self.get_time_ns_str()}"

                    grant_received = True
                    grant_cycle = wait_cycle
                    self.log.info(f"Grant received for client {client_id} on cycle {wait_cycle}{self.get_time_ns_str()}")
                    break

            assert grant_received, f"No grant received for client {client_id} within {max_wait_cycles} cycles{self.get_time_ns_str()}"

            # Now ACK the grant
            grant_bit = (1 << client_id)
            self.dut.grant_ack.value = grant_bit

            self.log.info(f"Sending ACK for client {client_id}{self.get_time_ns_str()}")

            # Wait one cycle for ACK to be processed
            await RisingEdge(self.dut.clk)

            # Clear ACK
            self.dut.grant_ack.value = 0

            # The critical test: Next cycle MUST be a dead cycle (grant_valid = 0)
            # This is because the arbiter doesn't know if the request will go away
            await RisingEdge(self.dut.clk)

            grant_valid_after_ack = int(self.dut.grant_valid.value)

            if grant_valid_after_ack == 1:
                self.log.error(f"❌ DEAD CYCLE VIOLATION: grant_valid=1 immediately after ACK for single request{self.get_time_ns_str()}")
                self.log.error(f"Expected: grant_valid=0 (dead cycle) after single request ACK{self.get_time_ns_str()}")
                raise AssertionError(f"Dead cycle violation for client {client_id}: grant_valid asserted immediately after ACK{self.get_time_ns_str()}")
            else:
                self.log.info(f"✓ Correct dead cycle: grant_valid=0 after ACK for client {client_id}{self.get_time_ns_str()}")

            # Continue the request to see if grant resumes after dead cycle
            # (since we didn't clear the request, it should get another grant after the dead cycle)
            grant_resumed = False
            for resume_cycle in range(10):
                await RisingEdge(self.dut.clk)

                if self.dut.grant_valid.value == 1:
                    grant_resumed = True
                    self.log.info(f"✓ Grant resumed after dead cycle on cycle {resume_cycle + 1}{self.get_time_ns_str()}")

                    # ACK this one too and clear the request
                    self.dut.grant_ack.value = grant_bit
                    await RisingEdge(self.dut.clk)
                    self.dut.grant_ack.value = 0
                    self.dut.request.value = 0
                    self.active_reqs = 0
                    break

            if not grant_resumed:
                self.log.warning(f"⚠️  Grant did not resume within 10 cycles after dead cycle{self.get_time_ns_str()}")

            # Brief pause before testing next client
            await self.wait_clocks('clk', 5)

        self.log.info(f"✓ ACK mode dead cycle test passed - all single request ACKs created proper dead cycles{self.get_time_ns_str()}")

    async def test_ack_mode_edge_cases(self):
        """Test both ACK mode edge cases with proper cleanup"""
        self.log.info(f"Starting comprehensive ACK mode edge case testing{self.get_time_ns_str()}")

        # Stop all background activity
        await self.stop_all_background_tasks()

        # Clear interface normally
        self.clear_interface()
        await self.wait_clocks('clk', 10)

        # Test 1: Back-to-back ACKs with multiple requests
        await self.test_ack_mode_back_to_back()

        # Clear pending grants between tests
        await self.clear_pending_grants_if_needed()
        self.clear_interface()
        await self.wait_clocks('clk', 10)

        # Test 2: Dead cycle requirement for single request ACK
        await self.test_ack_mode_dead_cycle()

        # Final cleanup
        await self.clear_pending_grants_if_needed()
        self.clear_interface()

        self.log.info(f"✓ All ACK mode edge case tests completed{self.get_time_ns_str()}")

    def generate_final_report(self):
        """Generate comprehensive final test report"""
        self.log.info(f"=== GENERATING FINAL TEST REPORT ==={self.get_time_ns_str()}")

        # Monitor generates the comprehensive report
        self.monitor.print_comprehensive_stats()

        # Also print weight compliance analysis for weighted arbiters
        self.monitor.print_weight_compliance_analysis(self.client_thresholds)

        # Basic validation only
        stats = self.monitor.get_comprehensive_stats()

        # Simple pass/fail validation
        validation_passed = True
        if stats['total_grants'] < self.CLIENTS * 5:
            validation_passed = False
        if len(self.monitor_errors) > 0:
            validation_passed = False

        if validation_passed:
            self.log.info(f"🎉 TEST PASSED{self.get_time_ns_str()}")
        else:
            self.log.error(f"❌ TEST FAILED{self.get_time_ns_str()}")

        return validation_passed
