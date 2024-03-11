import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.clock import Clock
# from cocotb.regression import TestFactory
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


@cocotb.test()
async def checksum_test(dut):
    """Test the checksum module with random data bursts."""
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    WIDTH = int(dut.WIDTH.value)
    mask = (1 << WIDTH)-1
    max_value = 2**WIDTH - 1
    log.info(f'{max_value=} {mask=}')
    
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())  # Start the clock
    # Reset the module
    dut.i_rst_n.value = 0
    dut.i_reset.value = 0
    dut.i_valid.value = 0
    dut.i_data.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    for _ in range(10):  # Perform 10 sets of checks
        # Generate a random burst length between 8 and 24
        burst_length = random.randint(8, 24)
        total = 0
        total_list = []

        # Drive the burst of data
        for _ in range(burst_length):
            data = random.randint(0, max_value)
            total += data
            total_list.append(data)
            
            dut.i_data.value = data
            dut.i_valid.value = 1
            await FallingEdge(dut.i_clk)

        # Check the checksum
        dut.i_valid.value = 0  # Deassert i_valid after the burst
        dut.i_data.value = 0
        await FallingEdge(dut.i_clk)  # Wait for one more clock cycle for the last addition
        actual_chksum = int(dut.o_chksum.value)
        expected_chksum = total & mask
        log.info(f'{total=:x} {actual_chksum=:x} {expected_chksum=:x}')
        hex_values = ' '.join(f"{num:x}" for num in total_list)
        log.info(f'{hex_values=}')
        assert actual_chksum == expected_chksum, f"Checksum mismatch: expected {expected_chksum}, got {actual_chksum}"

        # Assert i_reset for two clocks while i_valid is 0
        dut.i_reset.value = 1
        await FallingEdge(dut.i_clk)
        await FallingEdge(dut.i_clk)
        dut.i_reset.value = 0
        await FallingEdge(dut.i_clk)

        # Allow some time between bursts
        for _ in range(10):
            await FallingEdge(dut.i_clk)

# tf = TestFactory(checksum_test)
# tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_dataint_checksum(request, width):
    dut_name = "dataint_checksum"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_checksum"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_checksum.sv"),

    ]
    parameters = {'WIDTH':width, }

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
