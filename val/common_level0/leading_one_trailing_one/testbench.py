
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_leading_one_trailing_one')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_leading_one_trailing_one.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_fifo(dut):

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")

    dut.i_data.value = 0xFFFF
    await Timer(20, units="ns")

    await Timer(200, units="ns")

    hex_val = 0xFFFF
    # Walk 0's, low to high
    for i in range(16, -1, -1):
        hex_val &= ~(1<<i)
        log.info(f'Part 1: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")
    
    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x0000
    # Walk 1's, low to high
    for i in range(15, -1, -1):
        hex_val |= (1<<i)
        log.info(f'Part 2: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")
    
    hex_val = 0xFFFF
    # Walk single 0, low to high
    for i in range(16):
        hex_val &= ~(1<<i)
        log.info(f'Part 3: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x1
    # Walk single 1, low to high
    for i in range(16):
        log.info(f'Part 4: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")
        hex_val = hex_val * 2

    await Timer(200, units="ns")



from cocotb.regression import TestFactory
tf = TestFactory(test_fifo)
tf.generate_tests()