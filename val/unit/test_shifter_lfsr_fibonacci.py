import cocotb
from cocotb.triggers import FallingEdge, Timer
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



# Utility function to run an LFSR test with given parameters
async def run_lfsr_test(dut, seed_value, taps, N, log):
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.i_rst_n.value = 0
    dut.i_enable.value = 0
    dut.i_seed_load.value = 0
    dut.i_seed_data.value = 0
    dut.i_taps.value = 0
    await Timer(10, units="ns")
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    # Load the seed and configure the taps
    dut.i_seed_load.value = 1
    dut.i_seed_data.value = seed_value
    dut.i_taps.value = taps
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_seed_load.value = 0
    dut.i_enable.value = 1

    # Monitor the LFSR output
    cycle_count = 0
    while int(dut.o_lfsr_out.value) != seed_value:
        await FallingEdge(dut.i_clk)
        cycle_count += 1
        # Limit to prevent infinite loops, adjust as necessary
        if cycle_count > 2**N:  
            log.info("Failed to loop back to the initial seed within a reasonable number of cycles.")
            break

    dut.i_enable.value = 0  # Disable LFSR
    
    # Reporting
    log.info(f"For seed={seed_value:0{N}b} and taps={taps}, it took {cycle_count} cycles to repeat.")

# Master function to generate and schedule tests based on parameters
async def schedule_tests(dut, log):
    N = len(dut.i_seed_data)
    # Define your tests here, for example:
    bin_str = ''.join(format(num, '012b') for num in (8, 6, 5, 4))
    # print(f'{bin_str=}')
    seeds_and_taps = [
        (random.getrandbits(N), int(bin_str,2))
    ]

    for seed, taps in seeds_and_taps:
        await run_lfsr_test(dut, seed, taps, N, log)

# Entry point for the cocotb test
@cocotb.test()
async def dynamic_lfsr_tests(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')
    await schedule_tests(dut, log)

tf = TestFactory(dynamic_lfsr_tests)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_shifter_lfsr_fibonacci(request, width):
    dut_name = "shifter_lfsr_fibonacci"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "shifter_lfsr_fibonacci"   

    verilog_sources = [
        os.path.join(rtl_dir, "shifter_lfsr_fibonacci.sv"),

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
