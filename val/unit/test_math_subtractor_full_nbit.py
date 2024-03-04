import cocotb
import itertools
from cocotb.regression import TestFactory

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
def run_test(dut):
    """Run test for 4-bit subtraction with borrow-in"""
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    N = int(os.environ.get('PARAM_N', '0'))
    max_val = 2**N
    mask = max_val - 1
    if N == 4:
        i_list = range(max_val)
        j_list = range(max_val)
    else:
        count = 128
        i_list = [random.randint(0, max_val-1) for _ in range(count)]
        j_list = [random.randint(0, max_val-1) for _ in range(count)]

    for i, j in zip(i_list, j_list):
        for b_in in [0, 1]:  # Test both cases of i_b_in: 0 and 1
            dut._log.info(f"Testing subtraction: {i} - {j} with borrow-in {b_in}")

            dut.i_a.value = i
            dut.i_b.value = j
            dut.i_b_in.value = b_in

            yield cocotb.triggers.Timer(1)  # Wait a very short time for the combinatorial logic to settle

            # Expected result considering the borrow-in
            expected_result = (i - j - b_in) & mask  # Keep only the 4 least-significant bits

            # Expected borrow-out
            expected_borrow = 1 if (i - b_in) < j else 0

            assert dut.ow_d.value == expected_result,\
                f"For inputs {i}, {j} and borrow-in {b_in}, expected output was {expected_result} but got {dut.ow_d.value}"

            assert dut.ow_b.value == expected_borrow,\
                f"For inputs {i}, {j} and borrow-in {b_in}, expected borrow-out was {expected_borrow} but got {dut.ow_b.value}"

# Create the test
factory = TestFactory(run_test)
factory.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4,8])
def test_math_subtractor_full_nbit(request, n):
    dut_name = "math_subtractor_full_nbit"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_subtractor_full_nbit"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_subtractor_full.sv"),
        os.path.join(rtl_dir, "math_subtractor_full_nbit.sv"),

    ]
    parameters = {'N':n, }

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
