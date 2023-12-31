import cocotb
import itertools
from cocotb.regression import TestFactory
from cocotb.triggers import Timer

@cocotb.coroutine
def run_test(dut, a, b, c_in):
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = c_in
    yield Timer(1)  # Adjust the delay if necessary
    ow_sum = int(dut.ow_sum.value)
    ow_carry = int(dut.ow_carry.value)
    expected_sum = (a + b + c_in) & 0xFF
    expected_carry = int(a + b + c_in > 0xFF)
    
    if ow_sum != expected_sum or ow_carry != expected_carry:
        raise cocotb.result.TestFailure(f"Input: a={a}, b={b}, c_in={c_in}\n"
                                       f"Expected: sum={expected_sum}, carry={expected_carry}\n"
                                       f"Got: sum={ow_sum}, carry={ow_carry}")

@cocotb.coroutine
def run_tb(dut):
    N = 2**8
    for a, b, c_in in itertools.product(range(N), range(N), range(2)):
        yield run_test(dut, a, b, c_in)

@cocotb.coroutine
def run_simulation(dut):
    yield run_tb(dut)

factory = TestFactory(run_simulation)
factory.generate_tests()
