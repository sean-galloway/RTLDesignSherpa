import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
# from cocotb.regression import TestFactory
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
async def ring_counter_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Pass the width parameter from the Makefile to the test
    width = int(os.getenv("PARAM_WIDTH"))
    log.info(f"Testing with WIDTH={width}")
    cocotb.fork(Clock(dut.i_clk, 10, units='ns').start())

    # Reset the counter
    dut.i_rst_n.value = 0
    dut.i_enable.value = 0
    await RisingEdge(dut.i_clk)

    dut.i_rst_n.value = 1
    await RisingEdge(dut.i_clk)

    # Activate the counter
    dut.i_enable.value = 1
    await RisingEdge(dut.i_clk)

    # Iterate over each bit position starting from MSB to LSB
    for i in range(width):
        await RisingEdge(dut.i_clk)
        actual_state = int(dut.o_ring_out.value)
        # Expected '1' should move right with each iteration
        expected_state = 1 << (width - 1 - i)
        assert actual_state == expected_state, f"Counter state mismatch at {i} expected: {expected_state:0{width}b} got: {actual_state:0{width}b}"

    # After a complete cycle, check if the counter wraps correctly
    await RisingEdge(dut.i_clk)
    # At this point, the '1' should have rotated back to the MSB
    assert int(dut.o_ring_out.value) == 1 << (width - 1), "Counter did not wrap correctly to the initial state."


# tf = TestFactory(ring_counter_test)
# tf.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [4, 8, 16, 32])
def test_counter_ring(request, width):
    dut_name = "counter_ring"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "counter_ring"   

    verilog_sources = [
        os.path.join(rtl_dir, "counter_ring.sv"),
    ]
    parameters = {'WIDTH':width, }

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
