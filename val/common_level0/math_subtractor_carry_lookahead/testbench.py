import cocotb
from cocotb.triggers import Timer
from cocotb.result import TestFailure
from cocotb.regression import TestFactory
import itertools

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_subtractor_carry_lookahead')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_subtractor_carry_lookahead.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_subtractor(dut):
    """ Test for 4-bit carry lookahead subtractor """
    N = 4
    width_mask = (1 << N) - 1

    for i_a, i_b in itertools.product(range(2**N), repeat=2):
        for i_borrow_in in range(2):
            dut.i_a.value = i_a
            dut.i_b.value = i_b
            dut.i_borrow_in.value = i_borrow_in

            await Timer(1, units='ns')

            expected_difference = (i_a - i_b - i_borrow_in) & width_mask
            expected_carry_out = 1 if (i_a - i_b - i_borrow_in) < 0 else 0

            if int(dut.ow_difference.value) != expected_difference or int(dut.ow_carry_out.value) != expected_carry_out:
                raise TestFailure(f"For i_a={i_a}, i_b={i_b}, i_borrow_in={i_borrow_in}, expected difference was {expected_difference} and carry out was {expected_carry_out} but got difference={dut.ow_difference.value} and carry out={dut.ow_carry_out.value}")


tf = TestFactory(test_subtractor)
tf.generate_tests()