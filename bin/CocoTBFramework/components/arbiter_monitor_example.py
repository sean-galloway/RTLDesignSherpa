"""
Example usage of ArbiterMonitor for round-robin and weighted round-robin arbiters.
This demonstrates how to instantiate and use the monitors with cocotb tests.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.log import SimLog

from arbiter_monitor import RoundRobinArbiterMonitor, WeightedRoundRobinArbiterMonitor


@cocotb.test()
async def test_round_robin_arbiter(dut):
    """Test for the round-robin arbiter with basic functionality checks"""
    log = SimLog("cocotb.test.round_robin")
    
    # Initialize clock
    clock = dut.i_clk
    clock_period = 10  # ns
    clock.value = 0
    cocotb.start_soon(clock_generator(clock, clock_period))
    
    # Reset the DUT
    dut.i_rst_n.value = 0
    await ClockCycles(dut.i_clk, 5)
    dut.i_rst_n.value = 1
    
    # Initialize all input signals
    dut.i_block_arb.value = 0
    dut.i_req.value = 0
    
    if hasattr(dut, 'i_gnt_ack'):
        dut.i_gnt_ack.value = 0
    
    # Create the arbiter monitor
    monitor = RoundRobinArbiterMonitor(
        dut=dut,
        title="RoundRobinArbMonitor",
        clock=dut.i_clk,
        reset_n=dut.i_rst_n,
        req_signal=dut.i_req,
        gnt_valid_signal=dut.o_gnt_valid,
        gnt_signal=dut.o_gnt,
        gnt_id_signal=dut.o_gnt_id,
        gnt_ack_signal=dut.i_gnt_ack if hasattr(dut, 'i_gnt_ack') else None,
        block_arb_signal=dut.i_block_arb,
        log=log
    )
    
    # Register callbacks if needed
    monitor.add_transaction_callback(transaction_callback)
    
    # Wait a few cycles before starting tests
    await ClockCycles(dut.i_clk, 5)
    
    # Test case 1: Single request
    log.info("Test Case 1: Single Request")
    dut.i_req.value = 0b0001  # Request from client 0
    await ClockCycles(dut.i_clk, 1)
    
    # Wait for the grant
    for _ in range(10):  # Maximum wait time
        if dut.o_gnt_valid.value == 1:
            break
        await ClockCycles(dut.i_clk, 1)
    
    # Check the results
    assert dut.o_gnt_valid.value == 1, "Grant valid not asserted"
    assert dut.o_gnt.value.integer == 0b0001, f"Expected grant to client 0, got {bin(dut.o_gnt.value.integer)}"
    assert dut.o_gnt_id.value.integer == 0, f"Expected grant ID 0, got {dut.o_gnt_id.value.integer}"
    
    # Acknowledge the grant if needed
    if hasattr(dut, 'i_gnt_ack'):
        dut.i_gnt_ack.value = 0b0001
        await ClockCycles(dut.i_clk, 1)
        dut.i_gnt_ack.value = 0
    
    # Clear the request
    dut.i_req.value = 0
    await ClockCycles(dut.i_clk, 5)
    
    # Test case 2: Multiple requests
    log.info("Test Case 2: Multiple Requests")
    dut.i_req.value = 0b1011  # Requests from clients 0, 1, and 3
    
    # Run for enough cycles to observe all grants
    for _ in range(20):
        await ClockCycles(dut.i_clk, 1)
        
        # Acknowledge the grant if needed and if a grant was issued
        if hasattr(dut, 'i_gnt_ack') and dut.o_gnt_valid.value == 1:
            dut.i_gnt_ack.value = dut.o_gnt.value.integer
            await ClockCycles(dut.i_clk, 1)
            dut.i_gnt_ack.value = 0
    
    # Clear the request
    dut.i_req.value = 0
    await ClockCycles(dut.i_clk, 5)
    
    # Test case 3: Block arbitration
    log.info("Test Case 3: Block Arbitration")
    dut.i_req.value = 0b1111  # All clients requesting
    dut.i_block_arb.value = 1  # Block arbitration
    await ClockCycles(dut.i_clk, 5)
    
    # Check that no grants are issued
    assert dut.o_gnt_valid.value == 0, "Grant was issued while blocked"
    
    # Unblock and observe grants
    dut.i_block_arb.value = 0
    await ClockCycles(dut.i_clk, 20)
    
    # Display monitor statistics
    log.info(f"Total transactions: {monitor.get_transaction_count()}")
    log.info(f"Fairness index: {monitor.get_fairness_index():.2f}")
    
    for i in range(monitor.clients):
        stats = monitor.get_client_stats(i)
        log.info(f"Client {i} stats: Grants: {stats['grants']}, Avg wait: {stats['avg_wait_time']:.2f}ns")
    
    log.info(f"Priority changes: {monitor.get_priority_changes()}")


@cocotb.test()
async def test_weighted_round_robin_arbiter(dut):
    """Test for the weighted round-robin arbiter with basic functionality checks"""
    log = SimLog("cocotb.test.weighted_round_robin")
    
    # Initialize clock
    clock = dut.i_clk
    clock_period = 10  # ns
    clock.value = 0
    cocotb.start_soon(clock_generator(clock, clock_period))
    
    # Reset the DUT
    dut.i_rst_n.value = 0
    await ClockCycles(dut.i_clk, 5)
    dut.i_rst_n.value = 1
    
    # Initialize all input signals
    dut.i_block_arb.value = 0
    dut.i_req.value = 0
    
    # Set weights (assuming 4 clients with 4-bit threshold each)
    # Client 0: Weight 1
    # Client 1: Weight 2
    # Client 2: Weight 3
    # Client 3: Weight 4
    weights = 0
    for i in range(4):
        weight = i + 1
        weights |= (weight << (i * 4))
    dut.i_max_thresh.value = weights
    
    if hasattr(dut, 'i_gnt_ack'):
        dut.i_gnt_ack.value = 0
    
    # Create the arbiter monitor
    monitor = WeightedRoundRobinArbiterMonitor(
        dut=dut,
        title="WeightedRRMonitor",
        clock=dut.i_clk,
        reset_n=dut.i_rst_n,
        req_signal=dut.i_req,
        gnt_valid_signal=dut.ow_gnt_valid,
        gnt_signal=dut.ow_gnt,
        gnt_id_signal=dut.ow_gnt_id,
        gnt_ack_signal=dut.i_gnt_ack if hasattr(dut, 'i_gnt_ack') else None,
        block_arb_signal=dut.i_block_arb,
        max_thresh_signal=dut.i_max_thresh,
        log=log
    )
    
    # Register callbacks if needed
    monitor.add_transaction_callback(transaction_callback)
    
    # Wait a few cycles before starting tests
    await ClockCycles(dut.i_clk, 5)
    
    # Test case 1: All clients requesting
    log.info("Test Case 1: All Clients Requesting")
    dut.i_req.value = 0b1111  # All clients requesting
    
    # Run for enough cycles to observe the weighted behavior
    for _ in range(50):
        await ClockCycles(dut.i_clk, 1)
        
        # Acknowledge the grant if needed and if a grant was issued
        if hasattr(dut, 'i_gnt_ack') and dut.ow_gnt_valid.value == 1:
            dut.i_gnt_ack.value = dut.ow_gnt.value.integer
            await ClockCycles(dut.i_clk, 1)
            dut.i_gnt_ack.value = 0
    
    # Clear the request
    dut.i_req.value = 0
    await ClockCycles(dut.i_clk, 5)
    
    # Test case 2: Change weights during operation
    log.info("Test Case 2: Change Weights During Operation")
    
    # Set new weights
    # Client 0: Weight 4
    # Client 1: Weight 3
    # Client 2: Weight 2
    # Client 3: Weight 1
    new_weights = 0
    for i in range(4):
        weight = 4 - i
        new_weights |= (weight << (i * 4))
    
    # Start with all clients requesting
    dut.i_req.value = 0b1111
    await ClockCycles(dut.i_clk, 10)
    
    # Change weights
    dut.i_max_thresh.value = new_weights
    await ClockCycles(dut.i_clk, 30)
    
    # Clear the request
    dut.i_req.value = 0
    await ClockCycles(dut.i_clk, 5)
    
    # Display monitor statistics
    log.info(f"Total transactions: {monitor.get_transaction_count()}")
    log.info(f"Fairness index: {monitor.get_fairness_index():.2f}")
    
    for i in range(monitor.clients):
        stats = monitor.get_client_stats(i)
        log.info(f"Client {i} stats: Grants: {stats['grants']}, Avg wait: {stats['avg_wait_time']:.2f}ns")
    
    log.info(f"Inferred weights: {monitor.get_inferred_weights()}")
    log.info(f"Weight distribution: {monitor.get_weight_distribution()}")


def transaction_callback(transaction):
    """Callback function for new arbiter transactions"""
    log = SimLog("cocotb.callback")
    log.info(f"New transaction: Client {transaction.gnt_id} granted after {transaction.cycle_count} cycles")
    log.info(f"  Request vector: {bin(transaction.req_vector)}")
    log.info(f"  Grant vector: {bin(transaction.gnt_vector)}")
    
    if transaction.metadata:
        log.info(f"  Metadata: {transaction.metadata}")


async def clock_generator(clock, period):
    """Generate a clock with the specified period"""
    while True:
        clock.value = 0
        await Timer(period/2, units='ns')
        clock.value = 1
        await Timer(period/2, units='ns')