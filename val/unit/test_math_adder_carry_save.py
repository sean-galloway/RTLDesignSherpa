import cocotb
import itertools
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
async def basic_test(dut):
    """Test for single-bit math_adder_carry_save"""
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    
    # Iterate over all possible values
    for a, b, c in itertools.product(range(2), range(2), range(2)):
        dut.i_a.value = a
        dut.i_b.value = b
        dut.i_c.value = c

        await cocotb.triggers.Timer(1, units="ns")

        # Python-based reference computation
        sum_ab = a + b
        sum_abc = sum_ab + c

        expected_sum = sum_abc % 2
        expected_carry = sum_abc // 2

        assert dut.ow_sum.value == expected_sum, f"Expected {expected_sum}, but got {dut.ow_sum.value}"
        assert dut.ow_carry.value == expected_carry, f"Expected {expected_carry}, but got {dut.ow_carry.value}"

tf = TestFactory(basic_test)
tf.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_adder_carry_save(request, ):
    dut_name = "math_adder_carry_save"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_carry_save"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_carry_save.sv"),

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
