import cocotb
from cocotb.regression import TestFactory
from cocotb.triggers import Timer

@cocotb.test()
async def exhaustive_test(dut):
    """Test for N-bit math_adder_carry_save_nbit"""

    # Detect N dynamically
    N = len(dut.i_a)

    # Iterate over all possible values for i_a, i_b, and i_c
    for a in range(2**N):
        for b in range(2**N):
            for c in range(2**N):
                dut.i_a.value = a
                dut.i_b.value = b
                dut.i_c.value = c

                await Timer(1, units="ns")

                # Python-based reference computation for sum and carry
                expected_sum = [0]*N
                expected_carry = [0]*N

                for i in range(N):
                    a_bit = (a >> i) & 1
                    b_bit = (b >> i) & 1
                    c_bit = (c >> i) & 1
                    expected_sum[i] = a_bit ^ b_bit ^ c_bit
                    expected_carry[i] = (a_bit & b_bit) | (a_bit & c_bit) | (b_bit & c_bit)

                assert dut.ow_sum.value == int("".join(str(bit) for bit in reversed(expected_sum)), 2)
                assert dut.ow_carry.value == int("".join(str(bit) for bit in reversed(expected_carry)), 2)

tf = TestFactory(exhaustive_test)
tf.generate_tests()
