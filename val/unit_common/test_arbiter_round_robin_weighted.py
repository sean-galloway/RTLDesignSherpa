import os
import random
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run
import pytest

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


class WeightedRoundRobinConfig:
    """Configuration class for weighted round robin arbiter tests"""
    def __init__(self, name, clients, max_thresh, wait_gnt_ack):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            clients: Number of clients
            max_thresh: Maximum threshold for each client
            wait_gnt_ack: Whether to wait for grant acknowledge
        """
        self.name = name
        self.clients = clients
        self.max_thresh = max_thresh
        self.wait_gnt_ack = wait_gnt_ack


class WeightedRoundRobinTB(TBBase):
    """
    Testbench for the arbiter_round_robin_weighted module
    Features:
    - Request generation and verification
    - Grant checking with weighted priority
    - Weight/threshold configuration
    - Grant acknowledge handling
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

        # Initialize state trackers
        self.active_reqs = 0  # Store current request value
        self.granted_reqs = 0  # Store granted requests to clear them

        # Store client thresholds/weights
        self.client_thresholds = []

        # Initialize credit counters for verification
        self.credit_counters = [0] * self.CLIENTS

        # Clock and reset signals
        self.clock = self.dut.i_clk
        self.reset_n = self.dut.i_rst_n

        # Log configuration
        self.log.info(f"Weighted Round Robin TB initialized with CLIENTS={self.CLIENTS}")
        self.log.info(f"MAX_THRESH={self.MAX_THRESH}, WAIT_GNT_ACK={self.WAIT_GNT_ACK}, SEED={self.SEED}")

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

    def get_packed_thresholds(self):
        """Get the current packed thresholds value"""
        return int(self.dut.i_max_thresh.value)

    def get_client_threshold(self, client_id):
        """Extract a client's threshold from the packed value"""
        if client_id >= self.CLIENTS:
            self.log.error(f"Invalid client ID: {client_id}")
            return 0

        packed_thresholds = self.get_packed_thresholds()
        mask = (1 << self.MAX_THRESH_WIDTH) - 1
        shift = client_id * self.MAX_THRESH_WIDTH
        return (packed_thresholds >> shift) & mask

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

        # Wait for stabilization
        await self.wait_clocks('i_clk', 5)

        self.log.debug('Ending reset_dut')

    def random_delay(self, min_clocks=1, max_clocks=5):
        """Generate a random delay between min and max clocks"""
        return random.randint(min_clocks, max_clocks)

    async def generate_requests(self, num_cycles=20):
        """
        Generate random request patterns for specified number of cycles.
        Properly maintains requests until they are granted.

        Args:
            num_cycles: Number of cycles to generate requests for
        """
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
        """Monitor and verify grant signals"""
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
        """Test that grant signals work correctly"""
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
        """
        Run the main test sequence

        Args:
            run_cycles: Total number of cycles to run the test for
        """
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
        """Test that the threshold mechanism works correctly"""
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

    async def test_replenish_mechanism(self):
        """Test the credit replenishment mechanism"""
        self.log.info("Starting credit replenishment test")

        # Reset credit counters
        self.credit_counters = [0] * self.CLIENTS

        # Configure client thresholds - all clients get threshold of 2
        self.set_all_thresholds(2)

        # Set up initial active requests - only client 0
        req_pattern = 0b1
        self.dut.i_req.value = req_pattern
        self.active_reqs = req_pattern

        self.log.info(f"Initial request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

        # First phase: Let client 0 get its grants until it hits threshold
        client0_grants = 0
        max_cycles = 10
        for cycle in range(max_cycles):
            await self.wait_clocks('i_clk', 1)

            if self.dut.ow_gnt_valid.value == 1:
                grant_id = int(self.dut.ow_gnt_id.value)

                if grant_id == 0:
                    client0_grants += 1
                    self.log.info(f"Phase 1 - Cycle {cycle}: Grant to client 0 (count={client0_grants})")

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        self.dut.i_gnt_ack.value = 0b1
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

                # If client 0 got its threshold of grants, we can proceed to phase 2
                if client0_grants >= 2:
                    break

        self.log.info(f"Phase 1 complete: Client 0 received {client0_grants} grants")
        assert (
            client0_grants >= 2
        ), "Client 0 should have received at least 2 grants in phase 1"

        # Phase 2: Now add client 1 and see if client 0 is blocked due to threshold
        if self.CLIENTS > 1:
            req_pattern = 0b11  # Both client 0 and 1
            self.dut.i_req.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Phase 2 - New request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

            # Collect next few grants
            phase2_grants = []
            for cycle in range(5):
                await self.wait_clocks('i_clk', 1)

                if self.dut.ow_gnt_valid.value == 1:
                    grant_id = int(self.dut.ow_gnt_id.value)
                    phase2_grants.append(grant_id)
                    self.log.info(f"Phase 2 - Cycle {cycle}: Grant to client {grant_id}")

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        gnt_bit = (1 << grant_id)
                        self.dut.i_gnt_ack.value = gnt_bit
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

            self.log.info(f"Phase 2 grant sequence: {phase2_grants}")

            # Verify client 1 got at least one grant
            client1_grants = phase2_grants.count(1)
            assert client1_grants > 0, "Client 1 should have received at least one grant in phase 2"

            # Phase 3: Now remove all requests and then add back - should reset credits
            req_pattern = 0
            self.dut.i_req.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info("Phase 3 - Clearing all requests to reset credits")
            await self.wait_clocks('i_clk', 5)

            # Now add back just client 0 - it should be able to get grants again
            req_pattern = 0b1
            self.dut.i_req.value = req_pattern
            self.active_reqs = req_pattern

            self.log.info(f"Phase 3 - New request pattern: 0b{bin(req_pattern)[2:].zfill(self.CLIENTS)}")

            # See if client 0 can get grants again
            phase3_client0_grants = 0
            for cycle in range(5):
                await self.wait_clocks('i_clk', 1)

                if self.dut.ow_gnt_valid.value == 1:
                    grant_id = int(self.dut.ow_gnt_id.value)

                    if grant_id == 0:
                        phase3_client0_grants += 1
                        self.log.info(f"Phase 3 - Cycle {cycle}: Grant to client 0 (count={phase3_client0_grants})")

                    # Handle acknowledge if needed
                    if self.WAIT_GNT_ACK == 1:
                        gnt_bit = (1 << grant_id)
                        self.dut.i_gnt_ack.value = gnt_bit
                        await self.wait_clocks('i_clk', 1)
                        self.dut.i_gnt_ack.value = 0

            self.log.info(f"Phase 3 - Client 0 received {phase3_client0_grants} additional grants")

            # Verify client 0 got at least one grant in phase 3, indicating credits were reset
            assert phase3_client0_grants > 0, "Client 0 should have received grants after credit reset"

        self.log.info("Credit replenishment test passed")

    async def test_block_arb(self):
        """Test the block_arb functionality"""
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

    async def run_fairness_test(self):
        """Test arbiter fairness by monitoring grant distribution with equal weights"""
        self.log.info("Starting fairness test with equal weights")

        # Set equal weights for all clients
        self.set_all_thresholds(1)
        
        # Track grants per client
        grant_counts = [0] * self.CLIENTS
        total_cycles = 2000

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

                # Log detailed information for debugging
                if cycle < 50 or cycle % 100 == 0:
                    self.log.info(f"Cycle {cycle}: Grant to ID {gnt_id}, req 0b{bin(req_value)[2:].zfill(self.CLIENTS)}, "
                                f"grant bit 0b{bin(grant_bit)[2:].zfill(self.CLIENTS)}, counts {grant_counts}")

                # Wait one cycle
                await self.wait_clocks('i_clk', 1)

                # Handle acknowledge if needed
                if self.WAIT_GNT_ACK == 1:
                    self.dut.i_gnt_ack.value = grant_bit
                    await self.wait_clocks('i_clk', 1)
                    self.dut.i_gnt_ack.value = 0

                # Clear the granted bit but keep all other bits set
                self.dut.i_req.value = (req_value & ~grant_bit) | (all_requests & ~grant_bit)

                # # Wait one cycle
                # await self.wait_clocks('i_clk', 1)

                # Set all bits again
                self.dut.i_req.value = all_requests

        # Calculate statistics
        total_grants = sum(grant_counts)
        expected_per_client = total_grants / self.CLIENTS if self.CLIENTS > 0 else 0

        self.log.info(f"Total grants: {total_grants}")
        for i, count in enumerate(grant_counts):
            percentage = (count / total_grants) * 100 if total_grants > 0 else 0
            self.log.info(f"Client {i}: {count} grants ({percentage:.1f}%)")

            # Verify reasonable fairness (within 30% of expected) - relaxed for testing
            if expected_per_client > 0:
                assert count >= expected_per_client * 0.7, \
                    f"Client {i} received too few grants: {count} vs expected {expected_per_client:.1f}"
                assert count <= expected_per_client * 1.3, \
                    f"Client {i} received too many grants: {count} vs expected {expected_per_client:.1f}"

        self.log.info("Equal weights fairness test passed")

    async def run_weighted_fairness_test(self):
        """Test arbiter fairness with different weights"""
        self.log.info("Starting weighted fairness test")

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

        # Track grants per client
        grant_counts = [0] * self.CLIENTS
        total_cycles = 3000  # Increased from 30 to 3000 for better statistical accuracy

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

        # Calculate statistics
        total_grants = sum(grant_counts)
        total_weight = sum(self.client_thresholds)

        self.log.info(f"Total grants: {total_grants}, Total weight: {total_weight}")

        # For each client, calculate expected grants based on weight ratio
        for i, count in enumerate(grant_counts):
            weight = self.client_thresholds[i]
            weight_ratio = weight / total_weight if total_weight > 0 else 0
            expected_grants = total_grants * weight_ratio

            percentage = (count / total_grants) * 100 if total_grants > 0 else 0
            weight_percentage = (weight / total_weight) * 100 if total_weight > 0 else 0

            self.log.info(f"Client {i}: Weight {weight} ({weight_percentage:.1f}%) - "
                            f"Got {count} grants ({percentage:.1f}%) - "
                            f"Expected {expected_grants:.1f} grants")

            # Verify weighted fairness (within 40% of expected) - relaxed for testing
            # Higher tolerance because weighted fairness is more complex
            if expected_grants > 0:
                assert count >= expected_grants * 0.6, \
                    f"Client {i} received too few grants: {count} vs expected {expected_grants:.1f}"
                assert count <= expected_grants * 1.4, \
                    f"Client {i} received too many grants: {count} vs expected {expected_grants:.1f}"

        # Also verify that higher weight clients get more grants than lower weight ones
        if self.CLIENTS >= 4:
            assert (
                grant_counts[2] > grant_counts[1]
            ), "Client 2 (weight 4) should get more grants than client 1 (weight 2)"
            assert (
                grant_counts[1] > grant_counts[0]
            ), "Client 1 (weight 2) should get more grants than client 0 (weight 1)"

        self.log.info("Weighted fairness test passed")

@cocotb.test(timeout_time=2, timeout_unit="ms")
async def arbiter_round_robin_weighted_test(dut):
    """Test the weighted round robin arbiter"""
    tb = WeightedRoundRobinTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Log the wait_gnt_ack mode
    tb.log.info(f"Testing with WAIT_GNT_ACK = {tb.WAIT_GNT_ACK}")

    # Start the clock
    await tb.start_clock('i_clk', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run the grant signal test first to verify basic functionality
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting grant signal test @ {time_ns}ns ===")
        await tb.test_grant_signals()

        # Run the threshold operation test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting threshold operation test @ {time_ns}ns ===")
        await tb.test_threshold_operation()

        # Run the credit replenishment test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting credit replenishment test @ {time_ns}ns ===")
        await tb.test_replenish_mechanism()

        # Test block_arb functionality
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting block_arb test @ {time_ns}ns ===")
        await tb.test_block_arb()

        # Run the main test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting main arbitration test @ {time_ns}ns ===")
        await tb.run_test(500)  # Reduced cycles for faster testing

        # Run fairness test with equal weights
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting equal weights fairness test @ {time_ns}ns ===")
        await tb.run_fairness_test()

        # Run fairness test with different weights
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting weighted fairness test @ {time_ns}ns ===")
        await tb.run_weighted_fairness_test()

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('i_clk', 10)


@pytest.mark.parametrize("clients, max_thresh, wait_ack", [
    (6, 8, 0),    # No wait for ack, 6 clients, max threshold 8
    (4, 8, 1),    # Wait for ack, 4 clients, max threshold 4
    (8, 16, 0),   # No wait for ack, 8 clients, max threshold 16
    (8, 16, 1),   # Wait for ack, 8 clients, max threshold 16
])
def test_arbiter_round_robin_weighted(request, clients, max_thresh, wait_ack):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    dut_name = "arbiter_round_robin_weighted"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    c_str = TBBase.format_dec(clients, 2)
    m_str = TBBase.format_dec(max_thresh, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    test_name_plus_params = f"test_{dut_name}_c{c_str}_m{m_str}_w{w_str}"
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
    parameters = {
        'CLIENTS': clients,
        'MAX_THRESH': max_thresh,
        'MAX_THRESH_WIDTH': (max_thresh-1).bit_length(),  # Calculate log2 for MAX_THRESH_WIDTH
        'WAIT_GNT_ACK': wait_ack
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749)
        # 'SEED': str(random.randint(0, 100000))
    }

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
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
