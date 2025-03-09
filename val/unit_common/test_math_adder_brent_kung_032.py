import cocotb
import itertools
# from cocotb.regression import TestFactory
from cocotb.triggers import Timer
import os
import subprocess
import pytest
from adder_testing import AdderTB
from cocotb_test.simulator import run
import random


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def adder_test(dut):
    """ Test the adder fairly completely"""
    tb = AdderTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    tb.print_settings()
    tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.main_loop()


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
    includes = []
    parameters = {'N':32}

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    sim_build = os.path.join(repo_root, 'val', 'unit_common', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],  # where to search for all the python test files
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )
