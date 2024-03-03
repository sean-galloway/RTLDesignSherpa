import cocotb
from cocotb.triggers import Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_clock_pulse')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_clock_pulse.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


async def reset_dut(rst_n, duration, clk_period):
    rst_n.value = 0
    await Timer(duration * clk_period)
    rst_n.value = 1

@cocotb.test()
async def clock_divider_test(dut):
    clk_period = 10  # ns for 100MHz

    # Start the clock
    clock = Clock(dut.i_clk, clk_period, units='ns')
    cocotb.start_soon(clock.start())

    # Reset the DUT
    cocotb.start_soon(reset_dut(dut.i_rst_n, 20, clk_period))

    # Calculate the period of o_divided_clk[3] and wait for 4 toggles
    # Assuming you know the toggle rate, for example, if it toggles every 400ns
    toggle_period = 1200  # Replace with the correct period in ns
    await Timer(4 * toggle_period, units='ns')

tf = TestFactory(clock_divider_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_clock_pulse(request, width):
    dut = "clock_pulse"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "clock_pulse"   

    verilog_sources = [
        os.path.join(rtl_dir, "clock_pulse.sv"),

    ]
    parameters = {'WIDTH':width, }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join('regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join('local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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
