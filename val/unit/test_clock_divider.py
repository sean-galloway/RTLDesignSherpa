import cocotb
from cocotb.triggers import Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory
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


async def reset_dut(rst_n, duration, clk_period):
    rst_n.value = 0
    await Timer(duration * clk_period)
    rst_n.value = 1

@cocotb.test()
async def clock_divider_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    clk_period = 10  # ns for 100MHz
    pickoff_points = 0x08060402

    # Start the clock
    clock = Clock(dut.i_clk, clk_period, units='ns')
    cocotb.start_soon(clock.start())

    # Reset the DUT
    cocotb.start_soon(reset_dut(dut.i_rst_n, 20, clk_period))

    # Set i_pickoff_points
    dut.i_pickoff_points.value = pickoff_points

    # Calculate the period of o_divided_clk[3] and wait for 4 toggles
    # Assuming you know the toggle rate, for example, if it toggles every 400ns
    toggle_period = 1200  # Replace with the correct period in ns
    await Timer(4 * toggle_period, units='ns')

    dut._log.info("Waited for sufficient time for 4 toggles of o_divided_clk[3].")

tf = TestFactory(clock_divider_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_clock_divider(request, width):
    dut_name = "clock_divider"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "clock_divider"   

    verilog_sources = [
        os.path.join(rtl_dir, "clock_divider.sv"),

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
