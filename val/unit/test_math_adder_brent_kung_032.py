import cocotb
# from cocotb.regression import TestFactory
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

def configure_logging(dut_name, log_file_path):
    log = logging.getLogger(f'cocotb_log_{dut_name}')
    log.setLevel(logging.DEBUG)
    fh = logging.FileHandler(log_file_path)
    fh.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    log.addHandler(fh)
    return log


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
    
    assert (ow_sum == expected_sum) and (ow_carry == expected_carry), f"Input: a={a}, b={b}, c_in={c_in}\nExpected: sum={expected_sum}, carry={expected_carry}\nGot: sum={ow_sum}, carry={ow_carry}"


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
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    yield run_tb(dut)

# factory = TestFactory(run_simulation)
# factory.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_adder_brent_kung_032(request, ):
    dut_name = "math_adder_brent_kung_032"
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
        sim_build = os.path.join(repo_root, 'val', 'unit', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

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
