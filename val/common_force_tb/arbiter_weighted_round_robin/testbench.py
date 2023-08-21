import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.result import TestFailure
from collections import deque
from cocotb.clock import Clock

import random

@cocotb.coroutine
def reset_dut(dut):
    """Reset the DUT."""
    dut.i_rst_n.value = 0
    dut.i_block_arb.value = 0
    dut.i_req.value = 0
    yield RisingEdge(dut.i_clk)
    yield Timer(10, units='ns')
    dut.i_rst_n.value = 1
    yield RisingEdge(dut.i_clk)

class RequestAgent:
    """A simple agent for handling request signals."""

    def __init__(self, dut, index):
        self.dut = dut
        self.index = index
        self.queue = deque()

    @cocotb.coroutine
    def drive_request(self):
        while True:
            yield FallingEdge(self.dut.i_clk)
            
            if self.queue:
                next_val = self.queue.popleft()
                self.dut.i_req[self.index].value = next_val
            else:
                if random.random() < 0.75:  # 75% chance to drive a request
                    self.dut.i_req[self.index].value = 1
                    # Sometimes keep request asserted after being granted, or not
                    stay_asserted = [1] * random.randint(1, 4)
                    self.queue.extend(stay_asserted if random.random() > 0.5 else [0])
                else:  # 25% chance to not drive request
                    self.dut.i_req[self.index].value = 0


@cocotb.coroutine
def do_arbitration_and_check(dut, num_arbitrations):
    """Perform arbitrations and check results."""
    for _ in range(num_arbitrations):
        yield RisingEdge(dut.i_clk)
        granted = dut.ow_grant.value.integer
        requested = dut.i_req.value.integer

        if granted & requested != granted:
            raise TestFailure("Granted client(s) %s not in requested client(s) %s" % (bin(granted), bin(requested)))

@cocotb.coroutine
def drive_reqs_to_zero_and_wait(dut, num_cycles):
    """Drive all req signals to 0 and wait for a specified number of cycles."""
    dut.i_req.value = 0
    for _ in range(num_cycles):
        yield FallingEdge(dut.i_clk)

@cocotb.test()
def weighted_round_robin_test(dut):
    """Test for weighted_round_robin_wrapper."""
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    yield reset_dut(dut)

    # Start agents for each request line
    agents = [RequestAgent(dut, i) for i in range(5)]  # Assuming 5 clients

    # Fire off the agents to start driving values on their respective lines
    for agent in agents:
        cocotb.fork(agent.drive_request())

    # Set thresholds to all 1s
    dut.i_max_thresh.value = 0b00010001000100010001
    yield do_arbitration_and_check(dut, 20)

    yield Timer(100, units='ns')  # Wait for 100ns between stages

    # Set thresholds to all 15s
    dut.i_max_thresh.value = 0b11111111111111111111
    yield do_arbitration_and_check(dut, 300)

    for _ in range(50):  # Repeating the process 50 times
        # Drive all req signals to 0 and wait for 50 cycles
        yield drive_reqs_to_zero_and_wait(dut, 50)

        # Set to a new set of random thresholds
        random_thresholds = ''.join([format(random.randint(0, 15), '04b') for _ in range(5)])
        dut.i_max_thresh.value = int(random_thresholds, 2)
        
        # Wait for 10 cycles
        yield drive_reqs_to_zero_and_wait(dut, 10)

        # Resume random req signals
        for agent in agents:
            cocotb.fork(agent.drive_request())

        yield do_arbitration_and_check(dut, 300)

        yield Timer(100, units='ns')  # Wait for 100ns between random threshold stages
