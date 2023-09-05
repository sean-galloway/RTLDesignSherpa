import cocotb
import itertools
import random
from cocotb.regression import TestFactory
from cocotb.triggers import Timer

@cocotb.coroutine
def run_test(dut, a, b, c_in):
    width = len(dut.i_a)
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = c_in
    yield Timer(1)  # Adjust the delay if necessary
    ow_sum = int(dut.ow_sum.value)
    ow_carry = int(dut.ow_carry.value)
    expected_sum = (a + b + c_in) & ((1 << width) - 1)
    expected_carry = int(a + b + c_in > ((1 << width) - 1))
    
    if ow_sum != expected_sum or ow_carry != expected_carry:
        raise cocotb.result.TestFailure(f"Input: a={a}, b={b}, c_in={c_in}\n"
                                       f"Expected: sum={expected_sum}, carry={expected_carry}\n"
                                       f"Got: sum={ow_sum}, carry={ow_carry}")

@cocotb.coroutine
def run_tb(dut):
    bit_width = len(dut.i_a)
    N = 2 ** bit_width
    for _ in range(10000):
        a = random.randint(0, N - 1)
        b = random.randint(0, N - 1)
        c_in = random.randint(0, 1)
        yield run_test(dut, a, b, c_in)

@cocotb.coroutine
def run_simulation(dut):
    yield run_tb(dut)

factory = TestFactory(run_simulation)
factory.generate_tests()
