import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_full')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_full.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
def full_adder_test(dut):
    """Test for full adder."""
    
    for i, j, k in itertools.product(range(2), range(2), range(2)):
        dut.i_a.value = i
        dut.i_b.value = j
        dut.i_c.value = k

        yield Timer(1, units="ns")

        sum_result = int(dut.ow_sum.value)
        expected_sum = i ^ j ^ k

        carry_result = int(dut.ow_carry.value)
        expected_carry = (i & j) | (i & k) | (j & k)

        if sum_result != expected_sum:
            raise TestFailure(
                f"Mismatch detected! Inputs: {i} {j} {k}. Expected sum: {expected_sum}, Got: {sum_result}"
            )

        if carry_result != expected_carry:
            raise TestFailure(
                f"Mismatch detected! Inputs: {i} {j} {k}. Expected carry: {expected_carry}, Got: {carry_result}"
            )

    yield Timer(1, units="ns")
    log.info("All tests passed!")


from cocotb.regression import TestFactory
tf = TestFactory(full_adder_test)
tf.generate_tests()