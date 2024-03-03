import cocotb
import itertools
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_carry_save')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_carry_save.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def basic_test(dut):
    """Test for single-bit math_adder_carry_save"""

    # Iterate over all possible values
    for a, b, c in itertools.product(range(2), range(2), range(2)):
        dut.i_a.value = a
        dut.i_b.value = b
        dut.i_c.value = c

        await cocotb.triggers.Timer(1, units="ns")

        # Python-based reference computation
        sum_ab = a + b
        sum_abc = sum_ab + c

        expected_sum = sum_abc % 2
        expected_carry = sum_abc // 2

        assert dut.ow_sum.value == expected_sum, f"Expected {expected_sum}, but got {dut.ow_sum.value}"
        assert dut.ow_carry.value == expected_carry, f"Expected {expected_carry}, but got {dut.ow_carry.value}"

tf = TestFactory(basic_test)
tf.generate_tests()
