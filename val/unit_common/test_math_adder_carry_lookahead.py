import cocotb
import itertools
from cocotb.triggers import Timer
# from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from adder_testing import AdderTB
from cocotb_test.simulator import run
import random


@cocotb.test()
async def adder_test(dut):
    """ Test the adder fairly completely"""
    tb = AdderTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.main_loop()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4, 6, 8, 12, 16])
def test_math_adder_carry_lookahead(request, n):
    dut_name = "math_adder_carry_lookahead"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_carry_lookahead"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_carry_lookahead.sv"),

    ]
    parameters = {'N':n, }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_common', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit_common', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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
