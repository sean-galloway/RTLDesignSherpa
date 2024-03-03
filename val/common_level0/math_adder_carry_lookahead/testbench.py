import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_carry_lookahead')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_carry_lookahead.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_cla_4bit(dut):
    """ Test the 4-bit carry lookahead adder for all possible input combinations """

    N = 4
    for i_a, i_b in itertools.product(range(2**N), range(2**N)):
        for i_c in [0, 1]:
            # Apply inputs
            dut.i_a.value = i_a
            dut.i_b.value = i_b
            dut.i_c.value = i_c

            await Timer(1, units='ns')  # wait for the combinatorial logic to settle

            # Expected sum and carry out
            expected_sum = i_a + i_b + i_c
            expected_carry = 1 if expected_sum >= (2**N) else 0

            # Mask to get only N-bits for the sum
            expected_sum &= (2**N) - 1

            if int(dut.ow_sum) != expected_sum or int(dut.ow_carry) != expected_carry:
                raise TestFailure(
                    f"For i_a={i_a}, i_b={i_b}, and i_c={i_c}, expected sum was {expected_sum} and carry out was {expected_carry} but got sum={(dut.ow_sum.value)} and carry out={dut.ow_carry.value}")

tf = TestFactory(test_cla_4bit)
tf.generate_tests()