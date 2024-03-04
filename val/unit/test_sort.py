# sort_tb.py

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import subprocess
import random

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



NUM_VALS = 10
SIZE = 16

@cocotb.test()
async def sort_test(dut):
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    dut._log.info("Running test...")

    dut.i_data.value = 0
    dut.i_rst_n.value = 0
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1

    for _ in range(1000):
        # Generating random data
        data_in = [random.randint(0, 2**SIZE-1) for _ in range(NUM_VALS)]
        dut._log.info(f"Random input data: {data_in}")

        # Setting input
        flattened_data = "".join(
            [format(val, f'0{SIZE}b') for val in reversed(data_in)]
        )
    
        await FallingEdge(dut.i_clk)
        dut.i_data.value = BinaryValue(flattened_data)   # drive on the falling edge

        # Wait for one clock cycle
        await FallingEdge(dut.i_clk)

        # Reading and checking output
        sorted_data_out = [int(dut.o_data.value.get_binstr()[i*SIZE:(i+1)*SIZE], 2) for i in reversed(range(NUM_VALS))]
        dut._log.info(f"Sorted output data: {sorted_data_out}")

        # Check if the data is correctly sorted
        assert sorted_data_out == sorted(data_in, reverse=True), "Mismatch! Expected {} but got {}".format(sorted(data_in, reverse=True), sorted_data_out)

    dut._log.info("All tests passed!")

tf = TestFactory(sort_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("num_vals, size", [(10, 16)])
def test_sort(request, num_vals, size):
    dut_name = "sort"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "sort"   

    verilog_sources = [
        os.path.join(rtl_dir, "sort.sv"),

    ]
    parameters = {'NUM_VALS':num_vals,'SIZE':size, }

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
