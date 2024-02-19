import cocotb
import itertools
from cocotb.regression import TestFactory
from cocotb.triggers import Timer

@cocotb.test()
async def exhaustive_test(dut):
    """Test for N-bit math_adder_kogge_stone"""

    # Detect N dynamically
    N = len(dut.i_a)

    # Iterate over all possible values for i_a and i_b
    for a, b in itertools.product(range(2**N), range(2**N)):
        dut.i_a.value = a
        dut.i_b.value = b

        await Timer(1, units="ns")

        # Python-based reference computation for sum and carry
        expected_sum = a + b
        expected_carry_out = 1 if expected_sum >= 2**N else 0

        # Use modulo to wrap around sum for N bits
        expected_sum = expected_sum % (2**N)

        # Ensure the sum is correct
        assert dut.ow_sum.value == expected_sum

        # Ensure the final carry is correct
        assert dut.ow_carry.value == expected_carry_out


tf = TestFactory(exhaustive_test)
tf.generate_tests()
