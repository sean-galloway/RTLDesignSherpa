import cocotb
from cocotb.regression import TestFactory
from cocotb.triggers import Timer
import itertools
import os
import subprocess
import random
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_brent_kung_032')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_brent_kung_032.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


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
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    yield run_tb(dut)

factory = TestFactory(run_simulation)
factory.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_adder_brent_kung_032(request, ):
    dut = "math_adder_brent_kung_032"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_brent_kung_032"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_brent_kung_pg.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_black.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_gray.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_bitwisepg.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_grouppg_032.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_sum.sv"),
        os.path.join(rtl_dir, "math_adder_brent_kung_032.sv"),

    ]
    parameters = { }

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
