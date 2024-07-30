import cocotb
from cocotb.triggers import RisingEdge, Timer

from cocotb.clock import Clock
import os
import subprocess
import random

import pytest
from axi_skid_buffer import AXISkidBufferTB
from cocotb_test.simulator import run


@cocotb.test()
async def fifo_test(dut):
    '''Test the Skid Buffer as thoroughly as possible'''
    tb = AXISkidBufferTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    await tb.start_clock('i_axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_axi_aclk', 5)
    tb.log.info("Starting test...")
    await tb.simple_incremental_loops(20)
    await tb.main_loop(1000, 20)


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("data_width, depth", [(8,2),(8,4),(8,6),(8,8)])
def test_skid_buffer(request, data_width, depth):
    dut_name = "axi_skid_buffer"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_axi_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {"DATA_WIDTH":data_width, "SKID_DEPTH": depth}

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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
