import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
from cocotb.result import TestFailure
import random

@cocotb.coroutine
def adder_test(dut, a, b, c_in):
    """Test for specific input values a and b with carry c_in"""
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = c_in

    yield Timer(2, units='ns')

    sum_result = a + b + c_in
    if dut.ow_sum.value.integer != (sum_result & 0xF): # 4-bit result
        raise TestFailure(
            f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected sum={sum_result & 15}, Got={dut.ow_sum.value}"
        )
    if dut.ow_carry.value.integer != ((sum_result >> 4) & 0x1): # Carry result
        raise TestFailure(
            f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected carry={sum_result >> 4 & 1}, Got={dut.ow_carry.value}"
        )

@cocotb.coroutine
def run_test(dut):
    N=4**2
    for a, b, c_in in itertools.product(range(N), range(N), range(2)):
        yield adder_test(dut, a, b, c_in)

tf = TestFactory(run_test)
tf.generate_tests()
