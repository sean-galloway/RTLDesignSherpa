import cocotb
from cocotb.triggers import Timer

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
async def full_subtractor_test(dut):
    """ Test for full subtractor """

    for i_a in [0, 1]:
        for i_b in [0, 1]:
            for i_b_in in [0, 1]:
                dut.i_a.value = i_a
                dut.i_b.value = i_b
                dut.i_b_in.value = i_b_in

                await Timer(1, units='ns')

                expected_difference = (i_a - i_b - i_b_in) % 2
                expected_borrow = 1 if i_a < (i_b + i_b_in) else 0

                if int(dut.ow_d.value) != expected_difference or int(dut.ow_b.value) != expected_borrow:
                    raise TestFailure(f"For i_a={i_a}, i_b={i_b}, i_b_in={i_b_in}, expected ow_d was {expected_difference} and ow_b was {expected_borrow} but got ow_d={(dut.ow_d.value)} and ow_b={dut.ow_b.value}")

from cocotb.regression import TestFactory
tf = TestFactory(full_subtractor_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_subtractor_full(request, ):
    dut_name = "math_subtractor_full"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_subtractor_full"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_subtractor_full.sv"),

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
