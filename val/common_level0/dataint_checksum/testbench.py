import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import subprocess
import random

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_dataint_checksum')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_dataint_checksum.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def checksum_test(dut):
    """Test the checksum module with random data bursts."""
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    WIDTH = int(dut.WIDTH.value)
    mask = (1 << WIDTH)-1
    max_value = 2**WIDTH - 1
    log.info(f'{max_value=} {mask=}')
    
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())  # Start the clock
    # Reset the module
    dut.i_rst_n.value = 0
    dut.i_reset.value = 0
    dut.i_valid.value = 0
    dut.i_data.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    for _ in range(10):  # Perform 10 sets of checks
        # Generate a random burst length between 8 and 24
        burst_length = random.randint(8, 24)
        total = 0
        total_list = []

        # Drive the burst of data
        for _ in range(burst_length):
            data = random.randint(0, max_value)
            total += data
            total_list.append(data)
            
            dut.i_data.value = data
            dut.i_valid.value = 1
            await FallingEdge(dut.i_clk)

        # Check the checksum
        dut.i_valid.value = 0  # Deassert i_valid after the burst
        dut.i_data.value = 0
        await FallingEdge(dut.i_clk)  # Wait for one more clock cycle for the last addition
        actual_chksum = int(dut.o_chksum.value)
        expected_chksum = total & mask
        log.info(f'{total=:x} {actual_chksum=:x} {expected_chksum=:x}')
        hex_values = ' '.join(f"{num:x}" for num in total_list)
        log.info(f'{hex_values=}')
        assert actual_chksum == expected_chksum, f"Checksum mismatch: expected {expected_chksum}, got {actual_chksum}"

        # Assert i_reset for two clocks while i_valid is 0
        dut.i_reset.value = 1
        await FallingEdge(dut.i_clk)
        await FallingEdge(dut.i_clk)
        dut.i_reset.value = 0
        await FallingEdge(dut.i_clk)

        # Allow some time between bursts
        for _ in range(10):
            await FallingEdge(dut.i_clk)

tf = TestFactory(checksum_test)
tf.generate_tests()