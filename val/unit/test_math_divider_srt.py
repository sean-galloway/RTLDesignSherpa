import cocotb
import itertools
from cocotb.triggers import RisingEdge, ReadOnly, Timer, NextTimeStep
from cocotb.regression import TestFactory
from cocotb.decorators import coroutine
from cocotb.clock import Clock
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
async def divider_test(dut, dividend, divisor, log):
    """ Test the divider with specific dividend and divisor values. """

    # Reset
    dut.i_rst_b <= 0
    dut.i_start <= 0
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())
    await cocotb.triggers.Timer(5, units='ns')
    dut.i_rst_b <= 1
    await cocotb.triggers.Timer(40, units='ns')

    # Check for divide by zero
    dbz = (divisor == 0)

    # Start the division
    dut.i_dividend <= dividend
    dut.i_divisor <= divisor
    dut.i_start <= 1
    await cocotb.triggers.Timer(10, units='ns')
    dut.i_start <= 0
    loop_counter = 0

    # Wait for division to complete using a while loop
    while True:
        # await ReadOnly()  # Wait for read-only phase to read signal values
        # await NextTimeStep()  # Move to the next time step where writes are allowed
        loop_counter += 1
        if loop_counter > 500:
            log.info("Reached 500 iterations, ending simulation")
            cocotb.simulator.finish()  # End the simulation
        if dut.o_done.value:
            break
        #print(f'{dut.o_busy} {dut.o_done} {dut.o_valid} {dut.o_dbz}')
        await Timer(10, units='ns')  # Wait for a specified time
    # print('Done...')

    # Check results
    if not dbz:
        assert dut.o_valid.value, "Result is not valid"
        expected_quotient = dividend // divisor
        expected_remainder = dividend % divisor
        assert dut.o_quotient.value == expected_quotient, f"Incorrect quotient: {dut.o_quotient.value} != {expected_quotient}"
        assert dut.o_remainder.value == expected_remainder, f"Incorrect remainder: {dut.o_remainder.value} != {expected_remainder}"
    else:
        assert dut.o_dbz.value, "Divide by zero not detected"

@cocotb.coroutine
async def run_test(dut):
    """ Run tests with different dividend and divisor pairs. """
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    DATA_WIDTH = len(dut.i_dividend)
    max_value = 2**DATA_WIDTH - 1

    for dividend, divisor in itertools.product(range(max_value + 1), range(max_value + 1)):
        await divider_test(dut, dividend, divisor, log)
        if divisor % 5 == 0:
            log.info(f'{dividend=} {divisor=}')


factory = TestFactory(run_test)
factory.generate_tests()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("data_width", [4])
def test_math_divider_srt(request, data_width):
    dut_name = "math_divider_srt"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_divider_srt"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_divider_srt.sv"),

    ]
    parameters = {'DATA_WIDTH':data_width, }

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
