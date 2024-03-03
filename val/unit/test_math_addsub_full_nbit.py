import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure
from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_addsub_full_nbit')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_addsub_full_nbit.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


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
    if dut.ow_carry.value != expected_c:
        raise TestFailure(f"For inputs {a} and {b} with carry-in {cin}, expected carry/borrow was {expected_c} but got {dut.ow_carry.value}")


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

tf = TestFactory(run_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [(8,)])
def test_math_addsub_full_nbit(request, n):
    dut = "math_addsub_full_nbit"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_addsub_full_nbit"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_full.sv"),
        os.path.join(rtl_dir, "math_addsub_full_nbit.sv"),

    ]
    parameters = {'N':n, }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join('regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join('local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    run(
        python_search=[tests_dir],  # where to search for all the python test files
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )
