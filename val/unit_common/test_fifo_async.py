import os
import subprocess
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from CocoTBFramework.tbclasses.fifo_async_testing import FIFOASyncTB
from cocotb_test.simulator import run


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def fifo_test(dut):
    '''Test the FIFO as thoroughly as possible'''
    tb = FIFOASyncTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    await tb.start_clock('i_wr_clk', 10, 'ns')
    await tb.start_clock('i_rd_clk', 15, 'ns')
    tb.assert_reset()
    await tb.wait_clocks('i_rd_clk', 10)
    tb.deassert_reset()
    await tb.wait_clocks('i_rd_clk', 10)
    tb.log.info("Starting test...")
    await tb.main_loop(100, 200)


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("depth, data_width", [(4, 8), (8, 8), (16, 8)])
def test_fifo_async(request, depth, data_width):
    dut_name = "fifo_async"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "counter_bingray.sv"),
        os.path.join(rtl_dir, "gray2bin.sv"),
        os.path.join(rtl_dir, "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {'DEPTH':depth,'DATA_WIDTH':data_width}

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
