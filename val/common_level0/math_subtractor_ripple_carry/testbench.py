import cocotb
from cocotb.triggers import Timer
from cocotb.result import TestFailure
from cocotb.regression import TestFactory
import itertools

@cocotb.test()
async def test_subtractor(dut):
    """ Test for 4-bit ripple carry subtractor """
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