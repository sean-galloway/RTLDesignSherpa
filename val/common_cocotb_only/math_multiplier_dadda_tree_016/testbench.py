import cocotb
import itertools
from cocotb.regression import TestFactory
from cocotb.triggers import RisingEdge
from cocotb.clock import Clock
from cocotb.triggers import Timer
import os
seed = int(os.environ.get('SEED'))

import random
random.seed(seed)
print(f'seed changed to {seed}')







def binary_to_hex(binary_str):
    return hex(int(binary_str, 2))[2:]


@cocotb.coroutine
def init_test(dut):
    dut.i_multiplier.value = 0
    dut.i_multiplicand.value = 0
    yield Timer(1, units='ns')

@cocotb.test()
def multiplier_dadda_tree_016_test(dut): 

    yield init_test(dut)

    N = 16
    max_val = 2**N
    for _ in range(10000):
    # for a, b in itertools.product(range(max_val), range(max_val)):
        a = random.randint(0, max_val-1)
        b = random.randint(0, max_val-1)
        dut.i_multiplier.value = a
        dut.i_multiplicand.value = b

        yield Timer(10, units='ns')
        multiplier_hex = binary_to_hex(dut.i_multiplier.value.binstr)
        multiplicand_hex = binary_to_hex(dut.i_multiplicand.value.binstr)
        product_hex = binary_to_hex(dut.ow_product.value.binstr)
        print(f"Multiplier: {multiplier_hex}, Multiplicand: {multiplicand_hex}, Product: {product_hex}")

        result = dut.ow_product.value.integer
        expected_result = a * b
        assert result == expected_result, f"Multiplication of {a} and {b} yielded {result}, expected {expected_result}"

tf = TestFactory(multiplier_dadda_tree_016_test)
tf.generate_tests()
