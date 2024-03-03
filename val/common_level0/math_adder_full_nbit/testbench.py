import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
from cocotb.result import TestFailure
import os
import subprocess
import random

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_full_nbit')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_full_nbit.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)



@cocotb.coroutine
def adder_test(dut, a, b, c_in):
    """Test for specific input values a and b with carry c_in"""
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = c_in

    yield Timer(2, units='ns')

    sum_result = a + b + c_in
    if dut.ow_sum.value.integer != (sum_result & 0xF): # 4-bit result
        raise TestFailure(
            f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected sum={sum_result & 15}, Got={dut.ow_sum.value}"
        )
    if dut.ow_carry.value.integer != ((sum_result >> 4) & 0x1): # Carry result
        raise TestFailure(
            f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected carry={sum_result >> 4 & 1}, Got={dut.ow_carry.value}"
        )

@cocotb.coroutine
def run_test(dut):
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    N=4**2
    for a, b, c_in in itertools.product(range(N), range(N), range(2)):
        yield adder_test(dut, a, b, c_in)

tf = TestFactory(run_test)
tf.generate_tests()
