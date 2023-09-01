import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure

@cocotb.test()
async def test_cla_4bit(dut):
    """ Test the 4-bit ripple carry adder for all possible input combinations """

    N = 4
    for i_a, i_b in itertools.product(range(2**N), range(2**N)):
        for i_c in [0, 1]:
            # Apply inputs
            dut.i_a.value = i_a
            dut.i_b.value = i_b
            dut.i_c.value = i_c

            await Timer(1, units='ns')  # wait for the combinational logic to settle

            # Expected sum and carry out
            expected_sum = i_a + i_b + i_c
            expected_carry = 1 if expected_sum >= (2**N) else 0

            # Mask to get only N-bits for the sum
            expected_sum &= (2**N) - 1

            if int(dut.ow_sum) != expected_sum or int(dut.ow_carry) != expected_carry:
                raise TestFailure(
                    f"For i_a={i_a}, i_b={i_b}, and i_c={i_c}, expected sum was {expected_sum} and carry out was {expected_carry} but got sum={(dut.ow_sum.value)} and carry out={dut.ow_carry.value}")
