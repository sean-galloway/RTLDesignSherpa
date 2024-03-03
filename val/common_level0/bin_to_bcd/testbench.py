import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.clock import Clock
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_bin_to_bcd')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_bin_to_bcd.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


# Function to convert binary to BCD for verification
def binary_to_bcd(decimal_val, digit_count):
    # Format the decimal value as a BCD string
    bcd_str = ''.join(f'{int(digit):04b}' for digit in f'{decimal_val:0{digit_count//4}d}')
    return int(bcd_str, 2)

@cocotb.test()
async def bin_to_bcd_test(dut):
    # Start a clock
    clock = Clock(dut.i_clk, 10, units="ns")  # Adjust the timing as necessary
    cocotb.start_soon(clock.start())

    # Reset the DUT
    dut.i_start.value = 0
    dut.i_binary.value = 0
    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1

    # Parameters from DUT
    WIDTH = dut.WIDTH.value
    DIGITS = dut.DIGITS.value

    # Test all binary values
    for i in range(2**WIDTH):
        # print(f'Loop #{i}')
        # Drive the input signals
        await FallingEdge(dut.i_clk)
        dut.i_start.value = 1
        dut.i_binary.value = i
        await FallingEdge(dut.i_clk)
        dut.i_start.value = 0

        # Wait for the module to complete processing
        await RisingEdge(dut.o_done)
        await FallingEdge(dut.i_clk)
        
        # Verify the output
        expected_bcd = binary_to_bcd(i, DIGITS*4)
        if int(dut.o_bcd.value) != expected_bcd:
            error_message = f"Error: Binary={bin(i)}, Expected BCD={expected_bcd}, Module BCD={int(dut.o_bcd.value)}"
            dut._log.error(error_message)
            raise ValueError(error_message)

        # Wait a clock cycle before the next test iteration
        await RisingEdge(dut.i_clk)

tf = TestFactory(bin_to_bcd_test)
tf.generate_tests()