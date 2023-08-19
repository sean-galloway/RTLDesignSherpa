import cocotb
from cocotb.regression import TestFactory
from cocotb.triggers import RisingEdge
from cocotb.binary import BinaryValue

@cocotb.test()
async def basic_test(dut):
    """Test for n-bit math_adder_carry_save"""

    N = len(dut.i_a)  # get the width
    max_val = 2**N

    # Iterate over all possible values
    for a in range(max_val):
        for b in range(max_val):
            for c in range(2):  # carry in is only 0 or 1
                dut.i_a.value = a
                dut.i_b.value = b
                dut.i_c.value = c

                # Wait for a simulation time to ensure values propagate
                yield cocotb.triggers.Timer(10)

                # Python-based reference computation
                sum_ab = a + b
                sum_abc = sum_ab + c

                expected_sum = sum_abc % max_val
                expected_carry = sum_abc // max_val

                assert dut.ow_sum.value == expected_sum, f"Expected {expected_sum}, but got {dut.ow_sum.value}"
                assert dut.ow_c.value == expected_carry, f"Expected {expected_carry}, but got {dut.ow_c.value}"

tf = TestFactory(basic_test)
tf.generate_tests()
