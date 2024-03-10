import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.clock import Clock
import random
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
import random
from buffer_blocking_reorder_testing import BufferBlockingReorderTB


@cocotb.test()
async def basic_test(dut):
    '''Test the ROB as thoroughly as possible'''
    tb = BufferBlockingReorderTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    # TB Setup and reset sequence
    tb.print_settings()
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    tb.log.info("Starting test...")

    tb.check_empty()   # should start off empty
    tb.check_not_full() # should not be full either

    # Start the randomize_ready method in parallel without waiting for it to complete
    cocotb.start_soon(tb.randomize_ready(duration_ns=100000))

    for _ in range(tb.DEPTH):
        await tb.add_rnd_pkt()
    interval = random.randint(10, 100)
    await tb.wait_clocks('i_clk', interval)
    await tb.add_rnd_pkt_after_full_clears()
    tb.log.info("Test completed successfully.")

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("tag_width, addr_width, data_width, count_width, timer_width, depth", [(8, 16, 16, 3, 4, 16)])
def test_reorder_buffer(request, tag_width, addr_width, data_width, count_width, timer_width, depth):
    dut_name = "buffer_blocking_reorder"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name  

    verilog_sources = [
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]

    parameters = {'TAG_WIDTH':tag_width, 'ADDR_WIDTH':addr_width, 'DATA_WIDTH':data_width, 
                    'COUNT_WIDTH':count_width, 'TIMER_WIDTH':timer_width, 'DEPTH':depth}

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
