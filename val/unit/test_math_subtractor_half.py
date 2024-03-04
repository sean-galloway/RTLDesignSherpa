import cocotb
from cocotb.triggers import Timer

from cocotb.regression import TestFactory
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
async def half_subtractor_test(dut):
    """ Test for half subtractor """
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    for i_a in [0, 1]:
        for i_b in [0, 1]:
            dut.i_a.value = i_a
            dut.i_b.value = i_b

            await Timer(1, units='ns')

            expected_difference = i_a ^ i_b
            expected_borrow = 1 if i_a < i_b else 0

            assert int(dut.o_d.value) == expected_difference and int(dut.o_b.value) == expected_borrow,\
                f"For i_a={i_a}, i_b={i_b}, expected o_d was {expected_difference} and o_b was {expected_borrow} but got o_d={dut.o_d.value} and o_b={dut.o_b.value}"

tf = TestFactory(half_subtractor_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_subtractor_half(request, ):
    dut_name = "math_subtractor_half"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_subtractor_half"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_subtractor_half.sv"),

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
