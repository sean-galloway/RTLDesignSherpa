import cocotb
from cocotb.triggers import Timer
from cocotb.result import TestFailure

@cocotb.test()
async def test_half_subtractor(dut):
    """ Test for half subtractor """

    for i_a in [0, 1]:
        for i_b in [0, 1]:
            dut.i_a.value = i_a
            dut.i_b.value = i_b

            await Timer(1, units='ns')

            expected_difference = i_a ^ i_b
            expected_borrow = 1 if i_a < i_b else 0

            if int(dut.o_d.value) != expected_difference or int(dut.o_b.value) != expected_borrow:
                raise TestFailure(f"For i_a={i_a}, i_b={i_b}, expected o_d was {expected_difference} and o_b was {expected_borrow} but got o_d={dut.o_d.value} and o_b={dut.o_b.value}")
