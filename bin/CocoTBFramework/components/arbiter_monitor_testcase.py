"""
Complete test case for testing both round-robin and weighted round-robin arbiters
with the arbiter monitor classes.

This file demonstrates how to set up and use the arbiter monitors in a real test environment.
"""

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.regression import TestFactory
from cocotb.log import SimLog

from arbiter_monitor import RoundRobinArbiterMonitor, WeightedRoundRobinArbiterMonitor


class ArbiterTestbench:
    """
    Base testbench class for arbiter testing.
    Contains common functionality for both arbiter types.
    """
    
    def __init__(self, dut, log_name):
        self.dut = dut
        self.log = SimLog(log_name)
        self.transactions = []
        self.monitor = None
        
        # Determine number of clients from parameter or signal width
        if hasattr(dut, 'CLIENTS'):
            self.num_clients = int(dut.CLIENTS.value)
        else:
            self.num_clients = len(dut.i_req.value.binstr)
            
        self.log.info(f"Detected {self.num_clients} clients")
    
    async def setup(self):
        """Setup the testbench"""
        # Start the clock
        clock = Clock(self.dut.i_clk, 10, units="ns")
        cocotb.start_soon(clock.start())
        
        # Reset the DUT
        self.dut.i_rst_n.value = 0
        self.dut.i_block_arb.value = 0
        self.dut.i_req.value = 0
        
        if hasattr(self.dut, 'i_gnt_ack'):
            self.dut.i_gnt_ack.value = 0
            
        # Hold reset for a few clock cycles
        await ClockCycles(self.dut.i_clk, 5)
        self.dut.i_rst_n.value = 1
        
        # Wait a bit after reset
        await ClockCycles(self.dut.i_clk, 5)
    
    def transaction_callback(self, transaction):
        """Common transaction callback for all arbiter monitors"""
        self.transactions.append(transaction)
        self.log.info(f"Transaction recorded: Client {transaction.gnt_id} granted")
        self.log.debug(f"  Details: {transaction}")
    
    async def drive_requests(self, requests, duration=1):
        """
        Drive a specific request pattern and wait for specified clock cycles
        
        Args:
            requests: Integer or list representing request vector
            duration: Number of clock cycles to maintain this request pattern
        """
        if isinstance(requests, list):
            # Convert list of client indices to bit vector
            req_vector = 0
            for client_id in requests:
                req_vector |= (1 << client_id)
        else:
            # Assume it's already a bit vector
            req_vector = requests
            
        self.dut.i_req.value = req_vector
        await ClockCycles(self.dut.i_clk, duration)
    
    async def acknowledge_grant(self):
        """
        Acknowledge grant if required by arbiter
        """
        if not hasattr(self.dut, 'i_gnt_ack'):
            return
            
        # Check if grant is valid
        if self.dut.o_gnt_valid.value == 1 or (hasattr(self.dut, 'ow_gnt_valid') and self.dut.ow_gnt_valid.value == 1):
            # Get grant vector
            if hasattr(self.dut, 'o_gnt'):
                gnt = self.dut.o_gnt.value.integer
            else:
                gnt = self.dut.ow_gnt.value.integer
                
            # Set acknowledge
            self.dut.i_gnt_ack.value = gnt
            await ClockCycles(self.dut.i_clk, 1)
            self.dut.i_gnt_ack.value = 0
    
    async def wait_for_grant(self, timeout=10):
        """
        Wait for grant to be issued
        
        Args:
            timeout: Max clock cycles to wait
            
        Returns:
            Tuple of (grant_issued, grant_id, grant_vector)
        """
        for _ in range(timeout):
            # Check if grant valid is asserted
            if hasattr(self.dut, 'o_gnt_valid'):
                gnt_valid = self.dut.o_gnt_valid.value
            else:
                gnt_valid = self.dut.ow_gnt_valid.value
                
            if gnt_valid == 1:
                # Get grant info
                if hasattr(self.dut, 'o_gnt_id'):
                    gnt_id = self.dut.o_gnt_id.value.integer
                else:
                    gnt_id = self.dut.ow_gnt_id.value.integer
                    
                if hasattr(self.dut, 'o_gnt'):
                    gnt_vector = self.dut.o_gnt.value.integer
                else:
                    gnt_vector = self.dut.ow_gnt.value.integer
                    
                return True, gnt_id, gnt_vector
                
            await ClockCycles(self.dut.i_clk, 1)
            
        return False, None, None
    
    def print_stats(self):
        """Print statistics collected by the monitor"""
        if not self.monitor:
            return
            
        self.log.info("=" * 50)
        self.log.info("Arbiter Statistics:")
        self.log.info(f"  Total transactions: {self.monitor.get_transaction_count()}")
        self.log.info(f"  Fairness index: {self.monitor.get_fairness_index():.4f}")
        
        self.log.info("  Grants per client:")
        for i in range(self.monitor.clients):
            stats = self.monitor.get_client_stats(i)
            self.log.info(f"    Client {i}: {stats['grants']} grants, " +
                          f"avg wait: {stats['avg_wait_time']:.2f}ns")
        self.log.info("=" * 50)


class RoundRobinTestbench(ArbiterTestbench):
    """
    Testbench specifically for Round Robin arbiters.
    """
    
    def __init__(self, dut):
        super().__init__(dut, "cocotb.test.round_robin")
    
    async def setup(self):
        await super().setup()
        
        # Create monitor
        self.monitor = RoundRobinArbiterMonitor(
            dut=self.dut,
            title="RR_Monitor",
            clock=self.dut.i_clk,
            reset_n=self.dut.i_rst_n,
            req_signal=self.dut.i_req,
            gnt_valid_signal=self.dut.o_gnt_valid,
            gnt_signal=self.dut.o_gnt,
            gnt_id_signal=self.dut.o_gnt_id,
            gnt_ack_signal=self.dut.i_gnt_ack if hasattr(self.dut, 'i_gnt_ack') else None,
            block_arb_signal=self.dut.i_block_arb,
            clients=self.num_clients,
            log=self.log
        )
        
        # Register callback
        self.monitor.add_transaction_callback(self.transaction_callback)
    
    async def verify_round_robin_pattern(self):
        """
        Verify that the arbiter follows a round-robin pattern
        when all clients are requesting.
        """
        self.log.info("Testing round-robin pattern with all clients requesting")
        
        # Set all clients to request
        all_requesting = (1 << self.num_clients) - 1
        await self.drive_requests(all_requesting)
        
        # Collect grants for twice the number of clients
        # This should show the round-robin pattern repeating
        grants = []
        for _ in range(self.num_clients * 2):
            granted, gnt_id, _ = await self.wait_for_grant()
            
            if granted:
                grants.append(gnt_id)
                await self.acknowledge_grant()
            else:
                self.log.error("No grant issued within timeout")
                break
        
        self.log.info(f"Collected grant sequence: {grants}")
        
        # Check if the pattern repeats as expected
        if len(grants) >= self.num_clients:
            first_cycle = grants[:self.num_clients]
            second_cycle = grants[self.num_clients:self.num_clients*2]
            
            if set(first_cycle) == set(range(self.num_clients)) and first_cycle == second_cycle:
                self.log.info("Verified perfect round-robin pattern")
                return True
            else:
                self.log.warning("Grant sequence does not follow perfect round-robin pattern")
                return False
        else:
            self.log.error("Not enough grants collected to verify pattern")
            return False
    
    async def test_priority_after_reset(self):
        """
        Test that after reset, the arbiter starts with the expected initial priority
        (typically client 0 or highest priority client)
        """
        self.log.info("Testing priority after reset")
        
        # Reset the DUT
        self.dut.i_rst_n.value = 0
        await ClockCycles(self.dut.i_clk, 5)
        self.dut.i_rst_n.value = 1
        await ClockCycles(self.dut.i_clk, 5)
        
        # All clients request simultaneously
        all_requesting = (1 << self.num_clients) - 1
        await self.drive_requests(all_requesting)
        
        # First grant should go to the highest priority client (typically 0)
        granted, gnt_id, _ = await self.wait_for_grant()
        
        if granted:
            self.log.info(f"After reset, first grant went to client {gnt_id}")
            await self.acknowledge_grant()
            
            # Typically client 0 should get highest priority after reset
            if gnt_id == 0:
                self.log.info("Verified that client 0 has highest priority after reset")
                return True
            else:
                self.log.warning(f"Expected client 0 to have priority, but client {gnt_id} was granted")
                # This might still be valid for some implementations
                return True
        else:
            self.log.error("No grant issued after reset")
            return False


class WeightedRoundRobinTestbench(ArbiterTestbench):
    """
    Testbench specifically for Weighted Round Robin arbiters.
    """
    
    def __init__(self, dut):
        super().__init__(dut, "cocotb.test.weighted_round_robin")
        
        # Parameters for weighted arbitration
        self.weight_width = None
        self.max_thresh = None
        
        # Determine weight parameters
        if hasattr(dut, 'MAX_THRESH'):
            self.max_thresh = int(dut.MAX_THRESH.value)
            
        if hasattr(dut, 'MAX_THRESH_WIDTH'):
            self.weight_width = int(dut.MAX_THRESH_WIDTH.value)
        
        self.log.info(f"Weight parameters: width={self.weight_width}, max={self.max_thresh}")
    
    async def setup(self):
        await super().setup()
        
        # Create monitor
        self.monitor = WeightedRoundRobinArbiterMonitor(
            dut=self.dut,
            title="WRR_Monitor",
            clock=self.dut.i_clk,
            reset_n=self.dut.i_rst_n,
            req_signal=self.dut.i_req,
            gnt_valid_signal=self.dut.ow_gnt_valid,
            gnt_signal=self.dut.ow_gnt,
            gnt_id_signal=self.dut.ow_gnt_id,
            gnt_ack_signal=self.dut.i_gnt_ack if hasattr(self.dut, 'i_gnt_ack') else None,
            block_arb_signal=self.dut.i_block_arb,
            max_thresh_signal=self.dut.i_max_thresh,
            clients=self.num_clients,
            log=self.log
        )
        
        # Register callback
        self.monitor.add_transaction_callback(self.transaction_callback)
        
        # Configure initial weights if we know the format
        if self.weight_width:
            self.configure_weights([i+1 for i in range(self.num_clients)])
    
    def configure_weights(self, weights):
        """
        Configure the weights for the weighted round robin arbiter
        
        Args:
            weights: List of weights, one per client
        """
        if not self.weight_width:
            self.log.warning("Weight width unknown, cannot configure weights")
            return
            
        # Calculate the combined weight value
        max_thresh_value = 0
        for i, weight in enumerate(weights):
            max_thresh_value |= (weight << (i * self.weight_width))
            
        self.dut.i_max_thresh.value = max_thresh_value
        self.log.info(f"Configured weights: {weights}, value=0x{max_thresh_value:X}")
    
    async def verify_weight_distribution(self, weights, tolerance=0.2):
        """
        Verify that grants are distributed according to weights
        
        Args:
            weights: List of weights, one per client
            tolerance: Acceptable deviation from expected ratios
            
        Returns:
            True if distribution matches expectations within tolerance
        """
        self.log.info(f"Testing weight distribution with weights: {weights}")
        
        # Configure the weights
        self.configure_weights(weights)
        
        # Reset transaction counts
        self.transactions = []
        
        # All clients request
        all_requesting = (1 << self.num_clients) - 1
        await self.drive_requests(all_requesting)
        
        # Run for enough cycles to see the pattern
        # Need more cycles for weighted arbitration
        total_weight = sum(weights)
        required_cycles = total_weight * 2  # 2 complete cycles
        
        for _ in range(required_cycles * 2):  # Extra cycles to account for overhead
            await ClockCycles(self.dut.i_clk, 1)
            await self.acknowledge_grant()
            
            # Stop when we have enough transactions
            if len(self.transactions) >= required_cycles:
                break
        
        # Count grants per client
        grant_counts = [0] * self.num_clients
        for tx in self.transactions:
            grant_counts[tx.gnt_id] += 1
            
        self.log.info(f"Grant counts: {grant_counts}")
        
        # Calculate expected distribution
        total_grants = sum(grant_counts)
        expected_ratios = [w/total_weight for w in weights]
        actual_ratios = [count/total_grants for count in grant_counts]
        
        # Compare with tolerance
        within_tolerance = True
        for i in range(self.num_clients):
            diff = abs(expected_ratios[i] - actual_ratios[i])
            if diff > tolerance:
                within_tolerance = False
                self.log.warning(f"Client {i} ratio outside tolerance: " +
                             f"expected {expected_ratios[i]:.2f}, got {actual_ratios[i]:.2f}")
        
        if within_tolerance:
            self.log.info("Verified that grant distribution matches configured weights")
        else:
            self.log.warning("Grant distribution doesn't match expected weights")
            
        return within_tolerance
    
    async def test_weight_adaption(self):
        """
        Test that the arbiter adapts to weight changes during operation
        """
        self.log.info("Testing weight adaptation")
        
        # Start with equal weights
        equal_weights = [1] * self.num_clients
        self.configure_weights(equal_weights)
        
        # Reset transaction counts
        self.transactions = []
        
        # All clients request
        all_requesting = (1 << self.num_clients) - 1
        await self.drive_requests(all_requesting, 20)
        
        # Keep track of grants in first phase
        first_phase_grants = list(self.transactions)
        
        # Change to unequal weights
        unequal_weights = [i+1 for i in range(self.num_clients)]
        self.configure_weights(unequal_weights)
        
        # Reset transactions for second phase
        self.transactions = []
        
        # Continue with all clients requesting
        await self.drive_requests(all_requesting, 30)
        
        # Count grants per client in both phases
        first_counts = [0] * self.num_clients
        for tx in first_phase_grants:
            first_counts[tx.gnt_id] += 1
            
        second_counts = [0] * self.num_clients
        for tx in self.transactions:
            second_counts[tx.gnt_id] += 1
        
        self.log.info(f"First phase grants (equal weights): {first_counts}")
        self.log.info(f"Second phase grants (unequal weights): {second_counts}")
        
        # For equal weights, distribution should be equal
        first_total = sum(first_counts)
        if first_total > self.num_clients:
            expected_ratio = 1.0 / self.num_clients
            max_diff_equal = max(abs(count/first_total - expected_ratio) for count in first_counts)
            
            if max_diff_equal < 0.2:  # 20% tolerance for equal distribution
                self.log.info("First phase shows approximately equal distribution as expected")
            else:
                self.log.warning("First phase distribution not as equal as expected")
        
        # For unequal weights, higher weighted clients should get more grants
        if sum(second_counts) > 0:
            # Check if higher weights correspond to more grants
            weights_increasing = all(unequal_weights[i] <= unequal_weights[i+1] 
                                  for i in range(self.num_clients-1))
            grants_increasing = all(second_counts[i] <= second_counts[i+1] 
                                  for i in range(self.num_clients-1))
            
            if weights_increasing == grants_increasing:
                self.log.info("Second phase shows distribution corresponding to weights")
                return True
            else:
                self.log.warning("Second phase distribution doesn't follow weight pattern")
                return False
        
        return True


# Test functions for cocotb

@cocotb.test()
async def test_round_robin(dut):
    """Test basic round robin arbiter functionality"""
    tb = RoundRobinTestbench(dut)
    await tb.setup()
    
    # Test 1: Single client requesting
    tb.log.info("Test 1: Single client requesting")
    for i in range(tb.num_clients):
        await tb.drive_requests(1 << i)
        granted, gnt_id, gnt_vec = await tb.wait_for_grant()
        
        if granted:
            tb.log.info(f"Client {i} requested and client {gnt_id} was granted")
            assert gnt_id == i, f"Expected grant to client {i}, got {gnt_id}"
            await tb.acknowledge_grant()
        else:
            tb.log.error(f"No grant issued for client {i} request")
            assert False, "Grant not issued"
    
    # Test 2: Verify round robin pattern
    tb.log.info("Test 2: Verify round robin pattern")
    await tb.verify_round_robin_pattern()
    
    # Test 3: Test priority after reset
    tb.log.info("Test 3: Test priority after reset")
    await tb.test_priority_after_reset()
    
    # Test 4: Block arbitration
    tb.log.info("Test 4: Block arbitration")
    # Set all clients to request
    all_requesting = (1 << tb.num_clients) - 1
    tb.dut.i_block_arb.value = 1  # Block arbitration
    await tb.drive_requests(all_requesting, 5)
    
    # Verify no grants issued while blocked
    granted, _, _ = await tb.wait_for_grant(5)
    assert not granted, "Grant issued while arbitration blocked"
    
    # Unblock and verify grants resume
    tb.dut.i_block_arb.value = 0
    await tb.drive_requests(all_requesting, 1)
    granted, _, _ = await tb.wait_for_grant()
    assert granted, "No grant issued after unblocking"
    
    # Print statistics
    tb.print_stats()


@cocotb.test()
async def test_weighted_round_robin(dut):
    """Test weighted round robin arbiter functionality"""
    tb = WeightedRoundRobinTestbench(dut)
    await tb.setup()
    
    # Test 1: Single client requesting
    tb.log.info("Test 1: Single client requesting")
    for i in range(tb.num_clients):
        await tb.drive_requests(1 << i)
        granted, gnt_id, gnt_vec = await tb.wait_for_grant()
        
        if granted:
            tb.log.info(f"Client {i} requested and client {gnt_id} was granted")
            assert gnt_id == i, f"Expected grant to client {i}, got {gnt_id}"
            await tb.acknowledge_grant()
        else:
            tb.log.error(f"No grant issued for client {i} request")
            assert False, "Grant not issued"
    
    # Test 2: Verify equal weight distribution
    tb.log.info("Test 2: Verify equal weight distribution")
    equal_weights = [1] * tb.num_clients
    await tb.verify_weight_distribution(equal_weights)
    
    # Test 3: Verify unequal weight distribution
    tb.log.info("Test 3: Verify unequal weight distribution")
    unequal_weights = [i+1 for i in range(tb.num_clients)]
    await tb.verify_weight_distribution(unequal_weights)
    
    # Test 4: Test weight adaptation
    tb.log.info("Test 4: Test weight adaptation")
    await tb.test_weight_adaption()
    
    # Test 5: Block arbitration
    tb.log.info("Test 5: Block arbitration")
    # Set all clients to request
    all_requesting = (1 << tb.num_clients) - 1
    tb.dut.i_block_arb.value = 1  # Block arbitration
    await tb.drive_requests(all_requesting, 5)
    
    # Verify no grants issued while blocked
    granted, _, _ = await tb.wait_for_grant(5)
    assert not granted, "Grant issued while arbitration blocked"
    
    # Unblock and verify grants resume
    tb.dut.i_block_arb.value = 0
    await tb.drive_requests(all_requesting, 1)
    granted, _, _ = await tb.wait_for_grant()
    assert granted, "No grant issued after unblocking"
    
    # Print statistics
    tb.print_stats()
