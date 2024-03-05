import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer
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


@cocotb.coroutine
async def reset_dut(dut):
    """Reset the DUT"""
    dut.i_block_arb.value = 0
    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)

@cocotb.coroutine
async def run_test(dut):
    """Run the test on the DUT"""
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    num_clients = len(dut.i_req)
    log.info(f"Detected {num_clients} clients based on the i_req width.")

    # Reset the DUT
    await reset_dut(dut)

    # Basic tests
    for i in range(num_clients):
        dut.i_req.value = (1 << i)
        await FallingEdge(dut.i_clk)
        assert dut.o_gnt.value.integer == (1 << i), f"Expected o_gnt[{i}] to be high"

    # Test when multiple requests are made
    for i in range(num_clients - 1):
        dut.i_req.value = (1 << i) | (1 << (i + 1))
        await FallingEdge(dut.i_clk)
        assert dut.o_gnt.value.integer in [
            1 << i,
            1 << (i + 1),
        ], f"Expected either o_gnt[{i}] or o_gnt[{i + 1}] to be high"

    # Test with all clients requesting
    dut.i_req <= (1 << num_clients) - 1  # All bits set
    await FallingEdge(dut.i_clk)

    # Here, one of the requests should be granted, but we're not specific about which. It will depend on the internal logic of your arbiter and the state it's currently in.

@cocotb.test()
async def arbiter_round_robin_test(dut):
    """Test the round-robin arbiter"""

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())  # Start the clock

    await run_test(dut)

# tf = TestFactory(arbiter_round_robin_test)
# tf.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("clients", [(6,)])
def test_arbiter_round_robin(request, clients):
    dut_name = "arbiter_round_robin"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "arbiter_round_robin"   

    verilog_sources = [
        os.path.join(rtl_dir, "find_first_set.sv"),
        os.path.join(rtl_dir, "find_last_set.sv"),
        os.path.join(rtl_dir, "leading_one_trailing_one.sv"),
        os.path.join(rtl_dir, "arbiter_round_robin.sv"),

    ]
    parameters = {'CLIENTS':clients, }

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
