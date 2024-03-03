import cocotb
from cocotb.triggers import Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_clock_pulse')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_clock_pulse.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


async def reset_dut(rst_n, duration, clk_period):
    rst_n.value = 0
    await Timer(duration * clk_period)
    rst_n.value = 1

@cocotb.test()
async def test_clock_divider(dut):
    clk_period = 10  # ns for 100MHz

    # Start the clock
    clock = Clock(dut.i_clk, clk_period, units='ns')
    cocotb.start_soon(clock.start())

    # Reset the DUT
    cocotb.start_soon(reset_dut(dut.i_rst_n, 20, clk_period))

    # Calculate the period of o_divided_clk[3] and wait for 4 toggles
    # Assuming you know the toggle rate, for example, if it toggles every 400ns
    toggle_period = 1200  # Replace with the correct period in ns
    await Timer(4 * toggle_period, units='ns')

tf = TestFactory(test_clock_divider)
tf.generate_tests()