import cocotb
import itertools
from cocotb.regression import TestFactory
from cocotb.result import TestFailure
import os
import random

@cocotb.coroutine
def run_test(dut):
    """Run test for 4-bit subtraction with borrow-in"""
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    N=2**4
    for i, j in itertools.product(range(N), range(N)):
        for b_in in [0, 1]:  # Test both cases of i_b_in: 0 and 1
            dut._log.info(f"Testing subtraction: {i} - {j} with borrow-in {b_in}")

            dut.i_a <= i
            dut.i_b <= j
            dut.i_b_in <= b_in

            yield cocotb.triggers.Timer(1)  # Wait a very short time for the combinatorial logic to settle

            # Expected result considering the borrow-in
            expected_result = (i - j - b_in) & 0xF  # Keep only the 4 least-significant bits

            # Expected borrow-out
            expected_borrow = 1 if (i - b_in) < j else 0

            if dut.ow_d.value != expected_result:
                raise TestFailure(f"For inputs {i}, {j} and borrow-in {b_in}, expected output was {expected_result} but got {dut.ow_d.value}")

            if dut.ow_b.value != expected_borrow:
                raise TestFailure(f"For inputs {i}, {j} and borrow-in {b_in}, expected borrow-out was {expected_borrow} but got {dut.ow_b.value}")

# Create the test
factory = TestFactory(run_test)
factory.generate_tests()
