# sort_tb.py

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import random


NUM_VALS = 10
SIZE = 16

@cocotb.test()
async def sort_test(dut):
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    dut._log.info("Running test...")

    dut.i_data.value = 0
    dut.i_rst_n.value = 0
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1

    for _ in range(1000):
        # Generating random data
        data_in = [random.randint(0, 2**SIZE-1) for _ in range(NUM_VALS)]
        dut._log.info(f"Random input data: {data_in}")

        # Setting input
        flattened_data = "".join(
            [format(val, f'0{SIZE}b') for val in reversed(data_in)]
        )
    
        await FallingEdge(dut.i_clk)
        dut.i_data.value = BinaryValue(flattened_data)   # drive on the falling edge

        # Wait for one clock cycle
        await FallingEdge(dut.i_clk)

        # Reading and checking output
        sorted_data_out = [int(dut.o_data.value.get_binstr()[i*SIZE:(i+1)*SIZE], 2) for i in reversed(range(NUM_VALS))]
        dut._log.info(f"Sorted output data: {sorted_data_out}")

        # Check if the data is correctly sorted
        assert sorted_data_out == sorted(data_in, reverse=True), "Mismatch! Expected {} but got {}".format(sorted(data_in, reverse=True), sorted_data_out)

    dut._log.info("All tests passed!")

tf = TestFactory(sort_test)
tf.generate_tests()