import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.arbiter_monitor import WeightedRoundRobinArbiterMonitor


class WeightedRoundRobinConfig:
    """Configuration class for weighted round robin arbiter tests"""
    def __init__(self, name, clients, max_thresh, wait_gnt_ack):
        self.name = name
        self.clients = clients
        self.max_thresh = max_thresh
        self.wait_gnt_ack = wait_gnt_ack


class EnhancedWeightedRoundRobinTB(TBBase):
    """
    Enhanced Testbench for the arbiter_round_robin_weighted module with integrated monitor
    Features:
    - All original weighted test functionality
    - Integrated weighted arbiter monitor for detailed analysis
    - Enhanced weight compliance verification
    - Better credit replenishment analysis
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.CLIENTS = int(dut.CLIENTS)
        self.MAX_THRESH = int(dut.MAX_THRESH)
        self.MAX_THRESH_WIDTH = int(dut.MAX_THRESH_WIDTH)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Initialize state trackers (keep original functionality)
        self.active_reqs = 0
        self.granted_reqs = 0

        # Store client thresholds
        self.client_thresholds = []

        # Initialize credit counters for verification
        self.credit_counters = [0] * self.CLIENTS

        # Clock and reset signals
        self.clock = self.dut.i_clk
        self.reset_n = self.dut.i_rst_n

        # Initialize the enhanced weighted arbiter monitor
        self.monitor = WeightedRoundRobinArbiterMonitor(
            dut=dut,
            title="WRR_Monitor",
            clock=self.dut.i_clk,
            reset_n=self.dut.i_rst_n,
            req_signal=self.dut.i_req,
            gnt_valid_signal=self.dut.ow_gnt_valid,
            gnt_signal=self.dut.ow_gnt,
            gnt_id_signal=self.dut.ow_gnt_id,
            gnt_ack_signal=self.dut.i_gnt_ack,
            block_arb_signal=self.dut.i_block_arb,
            max_thresh_signal=self.dut.i_max_thresh,
            clients=self.CLIENTS,
            log=self.log,
            clock_period_ns=10
        )

        # Add monitor callbacks
        self.monitor.add_transaction_callback(self._on_monitor_transaction)
        self.monitor.add_reset_callback(self._on_monitor_reset)

        # Log configuration
        self.log.info(f"Enhanced Weighted Round Robin TB initialized with CLIENTS={self.CLIENTS}")
        self.log.info(f"MAX_THRESH={self.MAX_THRESH}, WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}")

    def _on_monitor_transaction(self, transaction):
        """Callback for monitor transactions"""
        pass

    def _on_monitor_reset(self):
        """Callback for reset events from monitor"""
        self.log.debug("Monitor detected reset event")

    def clear_interface(self):
        """Clear all interface signals"""
        self.dut.i_block_arb.value = 0
        self.dut.i_req.value = 0
        self.dut.i_gnt_ack.value = 0

        # Set default thresholds (all equal)
        self.set_all_thresholds(1)

        self.log.info('Clearing interface done.')

    def set_all_thresholds(self, value):
        """Set all client thresholds to the same value with validation"""
        if value > self.MAX_THRESH:
            self.log.error(f"FATAL ERROR: Threshold value {value} exceeds MAX_THRESH={self.MAX_THRESH}")
            assert False, f"Cannot set threshold to {value}, maximum allowed is {self.MAX_THRESH}"

        # All values are valid, proceed with setting thresholds
        self.client_thresholds = [value] * self.CLIENTS

        # Flatten the thresholds into the packed array format
        packed_thresholds = 0
        for i in range(self.CLIENTS):
            packed_thresholds |= (value << (i * self.MAX_THRESH_WIDTH))

        self.dut.i_max_thresh.value = packed_thresholds
        self.log.info(f"Set all client thresholds to {value} (packed: 0x{packed_thresholds:x})")

    def set_client_threshold(self, client_id, value):
        """Set threshold for a specific client with validation"""
        if client_id >= self.CLIENTS:
            self.log.error(f"FATAL ERROR: Invalid client ID: {client_id}")
            assert False, f"Client ID {client_id} is invalid, max client ID is {self.CLIENTS-1}"

        if value > self.MAX_THRESH:
            self.log.error(f"FATAL ERROR: Threshold value {value} exceeds MAX_THRESH={self.MAX_THRESH}")
            assert False, f"Cannot set threshold to {value}, maximum allowed is {self.MAX_THRESH}"

        # Value is valid, proceed with setting threshold
        self.client_thresholds[client_id] = value

        # Flatten the thresholds into the packed array format
        packed_thresholds = 0
        for i in range(self.CLIENTS):
            packed_thresholds |= (self.client_thresholds[i] << (i * self.MAX_THRESH_WIDTH))

        # Log the binary representation to make bit allocation clear
        binary_str = format(packed_thresholds, f'0{self.CLIENTS * self.MAX_THRESH_WIDTH}b')
        formatted_binary = ' '.join(binary_str[i:i+self.MAX_THRESH_WIDTH]
                                    for i in range(0, len(binary_str), self.MAX_THRESH_WIDTH))

        self.dut.i_max_thresh.value = packed_thresholds
        self.log.info(f"Set client {client_id} threshold to {value}")
        self.log.info(f"New packed thresholds: 0x{packed_thresholds:x} ({formatted_binary})")
        self.log.info(f"Client thresholds: {self.client_thresholds}")

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.reset_n.value = 0
        self.clear_interface()

        # Hold reset for multiple cycles
        await self.wait_clocks('i_clk', 5)

        # Release reset
        self.reset_n.value = 1

        # Start the monitor after reset is released
        self.monitor.start_monitoring()

        # Wait for stabilization
        await self.wait_clocks('i_clk', 5)

        self.log.debug('Ending reset_dut')

    def random_delay(self, min_clocks=1, max_clocks=5):
        """Generate a random delay between min and max clocks"""
        return random.randint(min_clocks, max_clocks)

    async def generate_requests(self, num_cycles=20):
        """Generate random request patterns for specified number of cycles."""
        self.log.info(f"Generating requests for {num_cycles} cycles")

        for _ in range(num_cycles):
            # Add new random requests, but don't remove existing ones
            new_reqs = 0
            for i in range(self.CLIENTS):
                # Only add a new request if this bit is not already set in active_reqs
                if not (self.active_reqs & (1 << i)) and random.random() < 0.5:
                    new_reqs |= (1 << i)

            # Add new requests to active requests
            self.active_reqs |= new_reqs
            self.dut.i_req.value = self.active_reqs

            if new_reqs:
                req_str = bin(self.active_reqs)[2:].zfill(self.CLIENTS)
                msg = f'    New reqs added: {bin(new_reqs)[2:].zfill(self.CLIENTS)}, Active reqs: {req_str}'
                self.log.debug(msg)

            await self.wait_clocks('i_clk', 1)

    async def check_grants(self):
        """Monitor and verify grant signals (original functionality)"""
        while True:
            # Wait for clock edge before checking grants
            await self.wait_clocks('i_clk', 1)

            # Now check if there's a valid grant
            if self.dut.ow_gnt_valid.value == 1:
                time_ns = get_sim_time('ns')
                grant_id = int(self.dut.ow_gnt_id.value)
                expected_gnt = (1 << grant_id)

                current_req = int(self.dut.i_req.value)
                msg = f'Current req: 0x{current_req:x} @ {time_ns}ns'
                self.log.debug(msg)

                actual_gnt = int(self.dut.ow_gnt.value)

                # Verify grant matches expected pattern
                assert actual_gnt == expected_gnt, \
                    f"Expected grant: 0x{expected_gnt:x}, got: 0x{actual_gnt:x} @ {time_ns}ns"

                # Verify grant corresponds to a request
                assert current_req & actual_gnt, \
                    f"Grant 0x{actual_gnt:x} not in response to request 0x{current_req:x} @ {time_ns}ns"

                # Update credit counter for this client (for verification)
                self.credit_counters[grant_id] += 1
                threshold = self.client_thresholds[grant_id]
                msg = f'Request bit {grant_id} granted (credit {self.credit_counters[grant_id]}/{threshold}) @ {time_ns}ns'
                self.log.debug(msg)

                # Mark this bit as granted so we can remove it from active requests
                self.granted_reqs |= (1 << grant_id)

                # Clear the granted bit from active requests after acknowledge
                if self.WAIT_GNT_ACK == 0:
                    # If no ACK needed, clear immediately
                    self.active_reqs &= ~(1 << grant_id)
                    self.dut.i_req.value = self.active_reqs
                    msg = f'Cleared bit {grant_id} immediately, new req value: 0x{self.active_reqs:x}'
                    self.log.debug(msg)

    async def handle_grant_ack(self):
        """Handle grant acknowledge signals when WAIT_GNT_ACK is enabled"""
        while True:
            await self.wait_clocks('i_clk', 1)

            if self.WAIT_GNT_ACK == 1 and self.dut.ow_gnt_valid.value == 1:
                grant_id = int(self.dut.ow_gnt_id.value)
                grant_ack_delay = self.random_delay()

                time_ns = get_sim_time('ns')
                self.log.debug(f"Scheduling grant ack for bit {grant_id} after {grant_ack_delay} cycles @ {time_ns}ns")

                # Wait for random delay before acknowledging
                for _ in range(grant_ack_delay):
                    await self.wait_clocks('i_clk', 1)

                # Set acknowledge signal
                ack_mask = (1 << grant_id)
                self.dut.i_gnt_ack.value = ack_mask

                time_ns = get_sim_time('ns')
                self.log.debug(f"Sending grant ack 0x{ack_mask:x} @ {time_ns}ns")

                # Clear the request only after acknowledge
                self.active_reqs &= ~(1 << grant_id)
                self.dut.i_req.value = self.active_reqs

                # Hold for one cycle then clear ack
                await self.wait_clocks('i_clk', 1)
                self.dut.i_gnt_ack.value = 0

    async def test_grant_signals(self):
        """Test that grant signals work correctly (original test)"""
        self.log.info("Starting grant signal test")

        # Test each client one by one to verify correct ow_gnt_id to ow_gnt mapping
        for client_id in range(self.CLIENTS):
            # Set a request for just this client
            req_pattern = (1 << client_id)
            self.dut.i_req.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Testing client {client_id}: req = 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

            # Wait for a grant
            max_cycles = 20
            cycle = 0
            grant_received = False

            while cycle < max_cycles and not grant_received:
                await self.wait_clocks('i_clk', 1)
                cycle += 1

                if self.dut.ow_gnt_valid.value == 1:
                    grant_id = int(self.dut.ow_gnt_id.value)
                    grant_bus = int(self.dut.ow_gnt.value)

                    self.log.info(f"Grant received on cycle {cycle}")
                    self.log.info(f"Grant ID: {grant_id}")
                    self.log.info(f"Grant bus: 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}")

                    # Verify the grant signals
                    assert grant_id == client_id, f"Expected grant ID {client_id}, got {grant_id}"
                    expected_grant = (1 << client_id)
                    assert grant_bus == expected_grant, \
                        f"Expected grant bus 0b{bin(expected_grant)[2:].zfill(self.CLIENTS)}, " \
                        f"got 0b{bin(grant_bus)[2:].zfill(self.CLIENTS)}"

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.i_gnt_ack.value = req_pattern
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

                    grant_received = True

            assert grant_received, f"No grant received for client {client_id}"

            # Clear the request and wait a cycle before the next client
            self.dut.i_req.value = 0
            self.active_reqs = 0
            await self.wait_clocks('i_clk', 5)

        self.log.info("Grant signal test passed - all clients received grants with correct ID and bus values")

    async def run_test(self, run_cycles=500):
        """Run the main test sequence (original functionality)"""
        self.log.info(f"Starting arbiter test with {self.CLIENTS} clients, WAIT_GNT_ACK={self.WAIT_GNT_ACK}")

        # Start concurrent processes
        cocotb.start_soon(self.generate_requests(20 * self.CLIENTS))
        cocotb.start_soon(self.check_grants())
        cocotb.start_soon(self.handle_grant_ack())

        # Run for the specified number of cycles
        self.log.info(f"Running for {run_cycles} clock cycles")
        await self.wait_clocks('i_clk', run_cycles)

        self.log.info("Test completed successfully")

    async def test_threshold_operation(self):
        """Test that the threshold mechanism works correctly (original test)"""
        self.log.info("Starting threshold operation test")

        # Reset credit counters for verification
        self.credit_counters = [0] * self.CLIENTS

        # Set up different thresholds for clients
        # Client 0: thresh = 1 (low priority, gets 1 grant)
        # Client 1: thresh = 3 (medium priority, gets 3 grants)
        # Other clients: thresh = 1 (standard priority)
        self.set_all_thresholds(1)
        if self.CLIENTS > 1:
            self.set_client_threshold(1, 3)

        # Set requests for the first two clients only
        req_pattern = 0b11 if self.CLIENTS >= 2 else 0b1
        self.dut.i_req.value = req_pattern
        self.active_reqs = req_pattern

        self.log.info(f"Setting up test with request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")
        self.log.info(f"Thresholds: {self.client_thresholds}")

        # Collect grants and verify threshold behavior
        grants_sequence = []
        expected_min_client1_grants = 3 if self.CLIENTS > 1 else 0

        # Run the test for enough cycles to observe weight effects
        max_cycles = 20
        for cycle in range(max_cycles):
            await self.wait_clocks('i_clk', 1)

            if self.dut.ow_gnt_valid.value == 1:
                grant_id = int(self.dut.ow_gnt_id.value)
                grants_sequence.append(grant_id)

                self.log.info(f"Cycle {cycle}: Grant to client {grant_id}")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    gnt_bit = (1 << grant_id)
                    self.dut.i_gnt_ack.value = gnt_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Keep requesting
                self.dut.i_req.value = req_pattern

                # If we've seen 6+ grants, we can verify behavior
                if len(grants_sequence) >= 6:
                    break

        # Analyze the grants sequence
        self.log.info(f"Grants sequence: {grants_sequence}")

        if self.CLIENTS > 1:
            # Count client 1 grants in the first 6 grants
            client1_grants = grants_sequence[:6].count(1)
            self.log.info(f"Client 1 got {client1_grants} grants out of first 6")

            # Verify client 1 (with threshold=3) gets more grants than client 0 (threshold=1)
            # We expect at least N-1 grants where N is the threshold
            assert client1_grants >= expected_min_client1_grants, \
                f"Client 1 with threshold=3 should get at least {expected_min_client1_grants} grants, " \
                f"but only got {client1_grants}"

        self.log.info("Threshold operation test passed")

    async def run_enhanced_weighted_fairness_test(self):
        """Enhanced weighted fairness test using monitor data"""
        self.log.info("Starting enhanced weighted fairness test with monitor analysis")

        # Set different weights for different clients
        if self.CLIENTS >= 4:
            # Client 0: weight 1 (low priority)
            # Client 1: weight 2 (medium priority)  
            # Client 2: weight 4 (high priority)
            # Client 3+: weight 1 (low priority)
            self.set_all_thresholds(1)
            self.set_client_threshold(1, 2)
            self.set_client_threshold(2, 4)

            self.log.info(f"Set client thresholds: {self.client_thresholds}")
        else:
            self.log.info("Skipping weighted fairness test - not enough clients")
            return

        # Enable monitor debug for detailed analysis
        self.monitor.enable_debug(False)  # Keep logs clean but monitor active

        # Track grants per client
        grant_counts = [0] * self.CLIENTS
        total_cycles = 3000  # Run longer for better statistics

        # Set all requests active
        all_requests = (1 << self.CLIENTS) - 1
        self.dut.i_req.value = all_requests

        self.log.info(f"Initial request pattern: 0b{bin(all_requests)[2:].zfill(self.CLIENTS)}")

        # Monitor grants
        for cycle in range(total_cycles):
            # Wait for falling edge plus delay - sample in middle of clock period
            await self.wait_falling_clocks('i_clk', 1, 100, 'ps')

            # Capture grant signals at a stable point in the clock period
            gnt_valid = int(self.dut.ow_gnt_valid.value)

            if gnt_valid == 1:
                # Read both the grant ID and one-hot signals for verification
                gnt_id = int(self.dut.ow_gnt_id.value)
                gnt_oh = int(self.dut.ow_gnt.value)

                # Verify the ID matches the one-hot encoding
                expected_oh = (1 << gnt_id)
                if gnt_oh != expected_oh:
                    self.log.warning(f"Grant ID {gnt_id} doesn't match one-hot signal 0x{gnt_oh:x}")

                grant_bit = (1 << gnt_id)
                req_value = int(self.dut.i_req.value)

                # Increment count for this client
                grant_counts[gnt_id] += 1

                # Log detailed information periodically
                if cycle < 50 or cycle % 200 == 0:
                    self.log.info(f"Cycle {cycle}: Grant to ID {gnt_id}, counts {grant_counts}")

                # Wait one cycle
                await self.wait_clocks('i_clk', 1)

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.i_gnt_ack.value = grant_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Clear the granted bit but keep all other bits set
                self.dut.i_req.value = (req_value & ~grant_bit) | (all_requests & ~grant_bit)

                # Set all bits again
                self.dut.i_req.value = all_requests

        # Get monitor statistics
        monitor_stats = self.monitor.get_stats_summary()
        monitor_fairness = monitor_stats['fairness_index']

        # Calculate statistics
        total_grants = sum(grant_counts)
        total_weight = sum(self.client_thresholds)

        self.log.info(f"=== Enhanced Weighted Fairness Test Results ===")
        self.log.info(f"Total grants: {total_grants}, Total weight: {total_weight}")
        self.log.info(f"Monitor fairness index: {monitor_fairness:.3f}")
        self.log.info(f"Monitor total transactions: {monitor_stats['total_transactions']}")

        # For each client, calculate expected grants based on weight ratio
        for i, count in enumerate(grant_counts):
            weight = self.client_thresholds[i]
            weight_ratio = weight / total_weight if total_weight > 0 else 0
            expected_grants = total_grants * weight_ratio

            percentage = (count / total_grants) * 100 if total_grants > 0 else 0
            weight_percentage = (weight / total_weight) * 100 if total_weight > 0 else 0

            monitor_count = monitor_stats['client_stats'][i]['grants']

            self.log.info(f"Client {i}: Weight {weight} ({weight_percentage:.1f}%) - "
                         f"Got {count} grants ({percentage:.1f}%) - "
                         f"Expected {expected_grants:.1f} grants - "
                         f"Monitor: {monitor_count} grants")

            # Verify weighted fairness (within 40% of expected) - relaxed for testing
            # Higher tolerance because weighted fairness is more complex
            if expected_grants > 0:
                deviation = abs(count - expected_grants) / expected_grants
                assert deviation < 0.4, \
                    f"Client {i} received grants outside acceptable range: {count} vs expected {expected_grants:.1f} (deviation: {deviation:.1%})"

        # Also verify that higher weight clients get more grants than lower weight ones
        if self.CLIENTS >= 4:
            assert grant_counts[2] > grant_counts[1], \
                "Client 2 (weight 4) should get more grants than client 1 (weight 2)"
            assert grant_counts[1] > grant_counts[0], \
                "Client 1 (weight 2) should get more grants than client 0 (weight 1)"

        # Test monitor's weight compliance analysis
        compliance = self.monitor.analyze_weight_compliance(self.client_thresholds)
        self.log.info(f"Monitor weight compliance analysis: {compliance}")

        if compliance['status'] == 'analyzed':
            assert compliance['is_compliant'], \
                f"Monitor detected weight compliance failure: {compliance['overall_compliance']:.2f}"

        self.log.info("Enhanced weighted fairness test passed")

    async def test_block_arb(self):
        """Test the block_arb functionality (original test)"""
        self.log.info("Starting block_arb test")

        # First clear all requests
        self.dut.i_req.value = 0
        self.dut.i_block_arb.value = 0
        await self.wait_clocks('i_clk', 5)

        # Set block_arb before setting any requests
        self.dut.i_block_arb.value = 1
        self.log.info("Asserted block_arb")
        await self.wait_clocks('i_clk', 5)

        # Now set some requests - these should not be granted while block_arb is active
        req_pattern = (1 << self.CLIENTS) - 1  # All bits set
        self.dut.i_req.value = req_pattern
        self.log.info(f"Set request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)} with block_arb asserted")

        # Wait several cycles and verify no grants are issued
        for i in range(20):
            await self.wait_clocks('i_clk', 1)
            assert self.dut.ow_gnt_valid.value == 0, \
                f"Grant was issued when block_arb was asserted at cycle {i}, time {get_sim_time('ns')}ns"

        self.log.info("No grants issued while block_arb was asserted - good!")

        # De-assert block_arb and ensure requests are still active
        self.dut.i_block_arb.value = 0
        self.log.info("De-asserted block_arb with active requests")

        # Check that grants resume
        grant_issued = False
        grant_count = 0
        max_cycles = 20

        for _ in range(max_cycles):
            await self.wait_clocks('i_clk', 1)

            if self.dut.ow_gnt_valid.value == 1:
                grant_id = int(self.dut.ow_gnt_id.value)
                grant_bit = (1 << grant_id)

                grant_issued = True
                grant_count += 1

                self.log.info(f"Received grant for client {grant_id} after de-asserting block_arb")

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.i_gnt_ack.value = grant_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Clear the granted bit but keep all other bits set
                current_req = int(self.dut.i_req.value)
                self.dut.i_req.value = current_req & ~grant_bit

                # If we've seen at least 3 grants, we can be confident that block_arb is working correctly
                if grant_count >= 3:
                    break

        assert grant_issued, "No grants issued after de-asserting block_arb with active requests"
        self.log.info(f"Received {grant_count} grants after de-asserting block_arb - block_arb test passed")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def arbiter_round_robin_weighted_enhanced_test(dut):
    """Enhanced test for the weighted round robin arbiter with monitor integration"""
    tb = EnhancedWeightedRoundRobinTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Enhanced weighted round robin test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('i_clk', 10, 'ns')

    # Reset the DUT (this also starts the monitor)
    await tb.reset_dut()

    try:
        # Run the original grant signal test first
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting grant signal test @ {time_ns}ns ===")
        await tb.test_grant_signals()

        # Run the threshold operation test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting threshold operation test @ {time_ns}ns ===")
        await tb.test_threshold_operation()

        # Test block_arb functionality
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting block_arb test @ {time_ns}ns ===")
        await tb.test_block_arb()

        # Run the main test with monitoring
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting main arbitration test @ {time_ns}ns ===")
        await tb.run_test(500)

        # Run enhanced weighted fairness test with monitor analysis
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting enhanced weighted fairness test @ {time_ns}ns ===")
        await tb.run_enhanced_weighted_fairness_test()

        # Print final monitor statistics
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Final Monitor Statistics @ {time_ns}ns ===")
        final_stats = tb.monitor.get_stats_summary()
        tb.log.info(f"Total transactions: {final_stats['total_transactions']}")
        tb.log.info(f"Total grants: {final_stats['total_grants']}")
        tb.log.info(f"Average wait time: {final_stats['avg_wait_time']:.2f}ns")
        tb.log.info(f"Fairness index: {final_stats['fairness_index']:.3f}")

        # Analyze weight compliance
        weight_analysis = tb.monitor.analyze_weight_compliance(tb.client_thresholds)
        tb.log.info(f"Weight compliance analysis: {weight_analysis}")

        tb.log.info("All enhanced weighted tests completed successfully")

    except AssertionError as e:
        tb.log.error(f"Enhanced weighted test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('i_clk', 10)


@pytest.mark.parametrize("clients, max_thresh, wait_ack", [
    (6, 8, 0),    # No wait for ack, 6 clients, max threshold 8
    (4, 8, 1),    # Wait for ack, 4 clients, max threshold 8
    (8, 16, 0),   # No wait for ack, 8 clients, max threshold 16
    (8, 16, 1),   # Wait for ack, 8 clients, max threshold 16
])
def test_arbiter_round_robin_weighted_enhanced(request, clients, max_thresh, wait_ack):
    """Run the enhanced weighted round robin test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "arbiter_round_robin_weighted"
    toplevel = dut_name

    # Verilog sources for WEIGHTED ROUND ROBIN arbiter
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    m_str = TBBase.format_dec(max_thresh, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    test_name_plus_params = f"test_{dut_name}_enhanced_c{c_str}_m{m_str}_w{w_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters for WEIGHTED ROUND ROBIN
    parameters = {
        'CLIENTS': clients,
        'MAX_THRESH': max_thresh,
        'MAX_THRESH_WIDTH': (max_thresh-1).bit_length(),  # Calculate log2 for MAX_THRESH_WIDTH
        'WAIT_GNT_ACK': wait_ack
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749)  # Fixed seed for reproducibility
        # 'SEED': str(random.randint(0, 100000))
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
            parameters=parameters,
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
        print(f"Enhanced weighted round robin test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure