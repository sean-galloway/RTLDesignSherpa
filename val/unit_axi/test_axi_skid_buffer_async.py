import cocotb
from cocotb.triggers import RisingEdge, Timer

from cocotb.clock import Clock
import os
import subprocess
import random

import pytest
from axi_skid_buffer_async import AXISkidBufferAsyncTB
from cocotb_test.simulator import run


@cocotb.test()
async def fifo_test(dut):
    '''Test the Skid Buffer as thoroughly as possible'''
    tb = AXISkidBufferAsyncTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    await tb.start_clock('i_axi_wr_aclk', 10, 'ns')
    await tb.start_clock('i_axi_rd_aclk', 15, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 6)
    await tb.deassert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 6)
    tb.log.info("Starting test...")
    await tb.main_loop(100, 20)


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("data_width", [(8)])
def test_skid_buffer_async(request, data_width):
    dut_name = "axi_skid_buffer_async"
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
        os.path.join(rtl_axi_dir, "axi_fifo_async.sv"),
        os.path.join(rtl_axi_dir, "axi_skid_buffer.sv"),
        os.path.join(rtl_axi_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {"DATA_WIDTH":data_width}

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
