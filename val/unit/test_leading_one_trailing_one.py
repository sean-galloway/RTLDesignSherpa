
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb
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
async def loto_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")

    dut.i_data.value = 0xFFFF
    await Timer(20, units="ns")

    await Timer(200, units="ns")

    hex_val = 0xFFFF
    # Walk 0's, low to high
    for i in range(16, -1, -1):
        hex_val &= ~(1<<i)
        log.info(f'Part 1: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")
    
    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x0000
    # Walk 1's, low to high
    for i in range(15, -1, -1):
        hex_val |= (1<<i)
        log.info(f'Part 2: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")
    
    hex_val = 0xFFFF
    # Walk single 0, low to high
    for i in range(16):
        hex_val &= ~(1<<i)
        log.info(f'Part 3: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")

    dut.i_data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x1
    # Walk single 1, low to high
    for i in range(16):
        log.info(f'Part 4: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.i_data.value = dec_val
        await Timer(20, units="ns")
        hex_val = hex_val * 2

    await Timer(200, units="ns")



from cocotb.regression import TestFactory
tf = TestFactory(loto_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [16])
def test_leading_one_trailing_one(request, width):
    dut_name = "leading_one_trailing_one"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "leading_one_trailing_one"   

    verilog_sources = [
        os.path.join(rtl_dir, "find_first_set.sv"),
        os.path.join(rtl_dir, "find_last_set.sv"),
        os.path.join(rtl_dir, "leading_one_trailing_one.sv"),

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
