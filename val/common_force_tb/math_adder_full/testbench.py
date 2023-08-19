import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure

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

        carry_result = int(dut.ow_c.value)
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
    print("All tests passed!")

