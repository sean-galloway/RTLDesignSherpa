import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
import os
import random

async def reset_dut(dut):
    """Reset the DUT."""
    dut.i_rst_n.value = 0
    dut.i_block_arb.value = 0
    dut.i_req.value = 0
    await RisingEdge(dut.i_clk)
    await Timer(10, units='ns')
    dut.i_rst_n.value = 1
    await RisingEdge(dut.i_clk)

class RequestAgent:
    """A simple agent for handling request signals."""

    def __init__(self, dut, index):
        self.dut = dut
        self.index = index
        self.queue = []

    async def drive_request(self):
        while True:
            await FallingEdge(self.dut.i_clk)

            if self.queue:
                next_val = self.queue.pop()
                self.dut.i_req[self.index].value = next_val
            elif random.random() < 0.75:
                self.dut.i_req[self.index].value = 1
                stay_asserted = [1] * random.randint(1, 4)
                self.queue.extend(stay_asserted if random.random() > 0.5 else [0])
            else:
                self.dut.i_req[self.index].value = 0

async def do_arbitration_and_check(dut, num_arbitrations):
    """Perform arbitrations and check results."""
    for _ in range(num_arbitrations):
        await RisingEdge(dut.i_clk)
        granted = dut.ow_grant.value.integer
        requested = dut.i_req.value.integer

        if granted & requested != granted:
            raise cocotb.result.TestFailure(
                f"Granted client(s) {bin(granted)} not in requested client(s) {bin(requested)}"
            )

async def drive_reqs_to_zero_and_wait(dut, num_cycles):
    """Drive all req signals to 0 and wait for a specified number of cycles."""
    dut.i_req.value = 0
    for _ in range(num_cycles):
        await FallingEdge(dut.i_clk)

@cocotb.test()
async def weighted_round_robin_test(dut):
    """Test for weighted_round_robin_wrapper."""
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    await reset_dut(dut)

    clients = len(dut.i_req)
    agents = [RequestAgent(dut, i) for i in range(clients)]

    for agent in agents:
        cocotb.start_soon(agent.drive_request())

    # Set thresholds to all 1s
    dut.i_max_thresh.value = int('0001' * clients, 2)
    await do_arbitration_and_check(dut, 20)

    await Timer(100, units='ns')  # Wait for 100ns between stages

    # Set thresholds to all 15s
    dut.i_max_thresh.value = int('1111' * clients, 2)
    await do_arbitration_and_check(dut, 300)

    for _ in range(50):  # Repeating the process 50 times
        # Drive all req signals to 0 and wait for 50 cycles
        await drive_reqs_to_zero_and_wait(dut, 50)

        # Set to a new set of random thresholds
        random_thresholds = ''.join([format(random.randint(0, 15), '04b') for _ in range(clients)])
        dut.i_max_thresh.value = int(random_thresholds, 2)
        
        # Wait for 10 cycles
        await drive_reqs_to_zero_and_wait(dut, 10)

        # Resume random req signals
        for agent in agents:
            cocotb.start_soon(agent.drive_request())

        await do_arbitration_and_check(dut, 300)

        await Timer(100, units='ns')  # Wait for 100ns between random threshold stages

from cocotb.regression import TestFactory
tf = TestFactory(weighted_round_robin_test)
tf.generate_tests()