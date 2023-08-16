import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure

@cocotb.coroutine
def addsub_dut_test(dut, a, b, cin, max_val):
    """Test logic for a specific set of input values."""
    
    # Apply test inputs
    dut.i_a.value = a
    dut.i_b.value = b
    dut.i_c.value = cin

    # Wait for a simulation time to ensure values propagate
    yield cocotb.triggers.Timer(10)

    # Check if the operation is addition or subtraction
    if cin == 0:
        expected_sum = a + b
        expected_c = 1 if expected_sum >= (max_val) else 0
        expected_sum = expected_sum % (max_val)
    else:
        expected_sum = a - b
        if expected_sum < 0:
            expected_sum += (max_val)
            expected_c = 0
        else:
            expected_c = 1

    # Check results
    if dut.ow_sum.value.integer != expected_sum:
        raise TestFailure(f"For inputs {a} and {b} with carry-in {cin}, expected sum was {expected_sum} but got {dut.ow_sum.value.integer}")
    if dut.ow_c.value != expected_c:
        raise TestFailure(f"For inputs {a} and {b} with carry-in {cin}, expected carry/borrow was {expected_c} but got {dut.ow_c.value}")


@cocotb.test()
def run_test(dut):
    """Testbench entry point."""
    
    # Initialize the DUT inputs
    dut.i_a.value = 0
    dut.i_b.value = 0
    dut.i_c.value = 0
    # Wait for a simulation time to ensure values propagate
    yield cocotb.triggers.Timer(10)
    N=8
    max_val = 2**N
    # Test the adder/subtractor
    for cin in [0, 1]:
        for i, j in itertools.product(range(max_val), range(max_val)):
            yield addsub_dut_test(dut, i, j, cin, max_val)
