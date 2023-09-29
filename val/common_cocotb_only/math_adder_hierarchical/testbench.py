import cocotb
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
import os
seed = int(os.environ.get('SEED'))

import random
random.seed(seed)
print(f'seed changed to {seed}')






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
    yield adder_test(dut)
