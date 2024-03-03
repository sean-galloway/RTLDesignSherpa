import cocotb
from cocotb.triggers import Timer
from cocotb.result import TestFailure

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_subtractor_full')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_subtractor_full.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_full_subtractor(dut):
    """ Test for full subtractor """

    for i_a in [0, 1]:
        for i_b in [0, 1]:
            for i_b_in in [0, 1]:
                dut.i_a.value = i_a
                dut.i_b.value = i_b
                dut.i_b_in.value = i_b_in

                await Timer(1, units='ns')

                expected_difference = (i_a - i_b - i_b_in) % 2
                expected_borrow = 1 if i_a < (i_b + i_b_in) else 0

                if int(dut.ow_d.value) != expected_difference or int(dut.ow_b.value) != expected_borrow:
                    raise TestFailure(f"For i_a={i_a}, i_b={i_b}, i_b_in={i_b_in}, expected ow_d was {expected_difference} and ow_b was {expected_borrow} but got ow_d={(dut.ow_d.value)} and ow_b={dut.ow_b.value}")

from cocotb.regression import TestFactory
tf = TestFactory(test_full_subtractor)
tf.generate_tests()