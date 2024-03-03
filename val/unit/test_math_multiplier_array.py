import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
from cocotb.result import TestFailure
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_multiplier_array')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_multiplier_array.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


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
        if dut.ow_product.value.integer != expected_product:
            raise TestFailure(f"For inputs {i} and {j}, expected output was {expected_product} but got {dut.ow_product.value.integer}")

factory = TestFactory(exhaustive_test)
factory.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [(8,)])
def test_math_multiplier_array(request, n):
    dut = "math_multiplier_array"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_multiplier_array"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_half.sv"),
        os.path.join(rtl_dir, "math_adder_full.sv"),
        os.path.join(rtl_dir, "math_adder_full_nbit.sv"),
        os.path.join(rtl_dir, "math_multiplier_array.sv"),

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
