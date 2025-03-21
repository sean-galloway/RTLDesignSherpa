import os
import random
import subprocess
import pytest
import cocotb
from CocoTBFramework.tbclasses.adder_testing import AdderTB
from cocotb_test.simulator import run


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
    dut.i_a = 0
    dut.i_b = 0
    await tb.wait_time(1, 'ns')
    await tb.half_adder_test()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_adder_half(request, ):
    dut_name = "math_adder_half"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_half"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_half.sv"),

    ]
    includes = []
    parameters = {'N':1}

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
