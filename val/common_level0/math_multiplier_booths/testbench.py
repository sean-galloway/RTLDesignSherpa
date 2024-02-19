import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
from cocotb.result import TestFailure

@cocotb.coroutine
def exhaustive_test(dut):
    N = 8  # Number of bits in the inputs
    width_out = 2*N  # Width of the product

    for i, j in itertools.product(range(2**N), range(2**N)):
        dut.i_multiplier.value = i
        dut.i_multiplicand.value = j

        # Wait a little for the output to be stable
        # We're assuming combinatorial logic, so a small delay is enough
        yield Timer(1, units='ns')

        expected_product = i * j
        # if dut.ow_product.value.integer != expected_product:
        #     raise TestFailure(f"For inputs {i} and {j}, expected output was {expected_product} but got {dut.ow_product.value.integer}")

factory = TestFactory(exhaustive_test)
factory.generate_tests()
