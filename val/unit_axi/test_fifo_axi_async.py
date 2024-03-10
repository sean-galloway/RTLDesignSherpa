import cocotb
from cocotb.triggers import RisingEdge, Timer

from cocotb.clock import Clock
import os
import subprocess
import random

import pytest
from fifo_axi_async_testing import FIFOAXIASyncTB
from cocotb_test.simulator import run


@cocotb.test()
async def fifo_test(dut):
    '''Test the FIFO as thoroughly as possible'''
    tb = FIFOAXIASyncTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    await tb.start_clock('i_wr_clk', 10, 'ns')
    await tb.start_clock('i_rd_clk', 15, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_rd_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_rd_clk', 5)
    tb.log.info("Starting test...")
    await tb.main_loop(100, 200)


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi')) #path to hdl folder where .v files are placed

# @pytest.mark.parametrize("data_width, depth", [(8, 4), (8,6), (8,8), (8,10), (8, 12)])
@pytest.mark.parametrize("depth, data_width, almost_wr_margin, almost_rd_margin", [(10, 8, 2, 2),(4, 8, 2, 2),(6, 8, 2, 2),(14, 8, 2, 2),])
def test_fifo_axi_async(request, depth, data_width, almost_wr_margin, almost_rd_margin):
    dut_name = "fifo_axi_async"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "find_first_set.sv"),
        os.path.join(rtl_dir, "find_last_set.sv"),
        os.path.join(rtl_dir, "leading_one_trailing_one.sv"),
        os.path.join(rtl_dir, "counter_bin.sv"),
        os.path.join(rtl_dir, "counter_johnson.sv"),
        os.path.join(rtl_dir, "grayj2bin.sv"),
        os.path.join(rtl_dir, "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(rtl_axi_dir, f"{dut_name}.sv"),

    ]
    parameters = {'DEPTH':depth,'DATA_WIDTH':data_width,'ALMOST_WR_MARGIN':almost_wr_margin,'ALMOST_RD_MARGIN':almost_rd_margin, }
    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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
