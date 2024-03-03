import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
from cocotb.result import TestFailure
import os
import subprocess
import random
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_full_nbit')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_full_nbit.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)



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
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    N=4**2
    for a, b, c_in in itertools.product(range(N), range(N), range(2)):
        yield adder_test(dut, a, b, c_in)

tf = TestFactory(run_test)
tf.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4])
def test_math_adder_full_nbit(request, n):
    dut = "math_adder_full_nbit"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_full_nbit"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_full.sv"),
        os.path.join(rtl_dir, "math_adder_full_nbit.sv"),

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
