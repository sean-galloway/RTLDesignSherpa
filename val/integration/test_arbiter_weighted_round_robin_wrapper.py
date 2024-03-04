
import queue
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, Timer
import itertools
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_subtractor_carry_lookahead')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_subtractor_carry_lookahead.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)

@cocotb.test()
async def test_fifo(dut):

    dut.i_write_A.value = 0
    dut.i_wr_data_A.value = 0
    dut.i_write_B.value = 0
    dut.i_wr_data_B.value = 0
    dut.i_write_C.value = 0
    dut.i_wr_data_C.value = 0
    dut.i_write_D.value = 0
    dut.i_wr_data_D.value = 0
    dut.start_pwm.value = 0

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)

    await FallingEdge(dut.i_clk)

    dut.start_pwm.value = 1
    await FallingEdge(dut.i_clk)
    # dut.start_pwm.value = 0

    for i in range(40):
        dut.i_write_A.value = 0
        while dut.o_wr_full_A.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_A.value = 1
        dut.i_wr_data_A.value = 160+i
        await FallingEdge(dut.i_clk)
    dut.i_write_A.value = 0

    for i in range(24):
        dut.i_write_B.value = 0
        while dut.o_wr_full_B.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_B.value = 1
        dut.i_wr_data_B.value = 176+i
        await FallingEdge(dut.i_clk)
    dut.i_write_B.value = 0

    for i in range(12):
        dut.i_write_C.value = 0
        while dut.o_wr_full_C.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_C.value = 1
        dut.i_wr_data_C.value = 192+i
        await FallingEdge(dut.i_clk)
    dut.i_write_C.value = 0


    for i in range(6):
        dut.i_write_D.value = 0
        while dut.o_wr_full_D.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_D.value = 1
        dut.i_wr_data_D.value = 208+i
        await FallingEdge(dut.i_clk)
    dut.i_write_D.value = 0

    for _ in range(200):
        await FallingEdge(dut.i_clk)


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_int_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'integration')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [(4,)])
def test_arbiter_weighted_round_robin_wrapper(request, n):
    dut = "weighted_round_robin_wrapper"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "weighted_round_robin_wrapper"   

    verilog_sources = [
        os.path.join(rtl_dir, "counter_bin.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(rtl_dir, "fifo_sync.sv"),
        os.path.join(rtl_dir, "arbiter_fixed_priority.sv"),
        os.path.join(rtl_dir, "arbiter_round_robin_subinst.sv"),
        os.path.join(rtl_dir, "arbiter_weighted_round_robin.sv"),
        os.path.join(rtl_dir, "pwm.sv"),
        os.path.join(rtl_int_dir, "weighted_round_robin_wrapper.sv"),

    ]
    parameters = {'N':n, }

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
