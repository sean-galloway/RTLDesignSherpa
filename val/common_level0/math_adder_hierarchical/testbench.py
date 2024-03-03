import cocotb
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
import os
import subprocess
import random

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_hierarchical')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_hierarchical.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


N = 16
C = 6

@cocotb.coroutine
def adder_test(dut):
    """ Test math_adder_hierarchical with random values """
    for idx in range(1000):  # Repeat 1000 times
        # Create and drive random numbers
        # input_data = [random.randint(1, 500) for _ in range(C)]
        input_data = [ idx+1 for _ in range(C)]
        for i, val in enumerate(input_data):
            dut.i_numbers[i].value = val
        
        # Calculate expected sum
        expected_sum = sum(input_data)

        max_value_N = 2**N
        expected_sum = (expected_sum % max_value_N)

        # Wait for 10 ns (or adjust this based on your design's needs)
        yield Timer(10, units="ns")

        # Check the result
        if int(dut.ow_sum) != expected_sum:
            raise cocotb.result.TestFailure(f"Mismatch detected: Expected {expected_sum}, got {int(dut.ow_sum)}")

@cocotb.test()
def run_test(dut):
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    yield adder_test(dut)

tf = TestFactory(run_test)
tf.generate_tests()