import cocotb
import itertools
from cocotb.triggers import Timer
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

@cocotb.test()
async def adder_test(dut):
    """Test for specific input values a and b with carry c_in"""
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    N = int(os.environ.get('PARAM_N', '0'))
    max_val = 2**N
    mask = (2**N)-1
    # Iterate over all possible values for i_a, i_b, and i_c
    for a, b, c_in in itertools.product(range(max_val), range(max_val), range(2)):
        dut.i_a.value = a
        dut.i_b.value = b
        dut.i_c.value = c_in

        await Timer(2, units='ns')

        sum_result = a + b + c_in
        expected = sum_result & mask
        found = dut.ow_sum.value
        pass_or_fail = True
        if dut.ow_sum.value.integer != (sum_result & mask):
            pass_or_fail = False
        log.info(f'{max_val=} {mask=} {a=} {b=} {c_in=} {expected=} {found=} {pass_or_fail=}')

        if dut.ow_sum.value.integer != (sum_result & mask):
            raise TestFailure(
                f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected sum={sum_result & mask}, Got={dut.ow_sum.value}"
            )
        if dut.ow_carry.value.integer != ((sum_result >> N) & 0x1): # Carry result
            raise TestFailure(
                f"Mismatch detected! i_a={dut.i_a}, i_b={dut.i_b}, c_in={c_in}, Expected carry={sum_result >> 4 & 1}, Got={dut.ow_carry.value}"
            )

tf = TestFactory(adder_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4, 8])
def test_math_adder_full_nbit(request, n):
    dut_name = "math_adder_full_nbit"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_full_nbit"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_full.sv"),
        os.path.join(rtl_dir, "math_adder_full_nbit.sv"),

    ]
    parameters = {'N':n, }
    print(f'N:{parameters["N"]}')

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
