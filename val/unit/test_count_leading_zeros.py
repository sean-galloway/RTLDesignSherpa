import cocotb
from cocotb.triggers import Timer
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


@cocotb.test()
async def count_leading_zeros_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    width = len(dut.i_data)
    dut._log.info(f"Testing with WIDTH={width}")

    # Start with all zeros
    dut.i_data.value = 0
    # dut.i_enable.value = 0
    await Timer(100, units='ns')
    # dut.i_enable.value = 1
    await Timer(10, units='ns')
    assert dut.ow_count_leading_zeros.value == width, f"Expected {width} leading zeros, got {dut.ow_leading_zeros_count.value}"

    # Walk a '1' through the entire width
    for i in range(width):
        dut.i_data.value = 1 << (width - 1 - i)
        await Timer(10, units='ns')
        expected_leading_zeros = width - 1 - i
        assert dut.ow_count_leading_zeros.value == expected_leading_zeros, f"Expected {expected_leading_zeros} leading zeros, got {dut.ow_leading_zeros_count.value}"

    # End with all zeros again
    dut.i_data.value = 0
    await Timer(10, units='ns')
    assert dut.ow_count_leading_zeros.value == width, f"Expected {width} leading zeros, got {dut.ow_leading_zeros_count.value}"

    dut._log.info("Test completed successfully")

tf = TestFactory(count_leading_zeros_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(16,)])
def test_count_leading_zeros(request, width):
    dut_name = "count_leading_zeros"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "count_leading_zeros"   

    verilog_sources = [
        os.path.join(rtl_dir, "count_leading_zeros.sv"),

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
