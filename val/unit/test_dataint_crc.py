import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import subprocess
import random
from crc_testing import CRCTesting, crc_parameters
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


def find_highest_byte_enable(data_width):
    # Calculate the number of bytes - 1 to find the highest byte position
    highest_byte_position = (data_width // 8) - 1
    return 1 << highest_byte_position

@cocotb.test()
async def crc_basic_test(dut):
    """ Test the CRC calculation for a basic input """
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    clock = Clock(dut.i_clk, 10, units="ns")  # Create a 100MHz clock
    cocotb.start_soon(clock.start())  # Start the clock

    crctest = CRCTesting(dut, 100)
    crctest.print_settings()
    crctest.generate_test_data()
    
    ##########################################################################
    # Reset
    dut.i_rst_n.value = 0
    # Initialize inputs
    dut.i_load_crc_start.value = 0
    dut.i_load_from_cascade.value = 0
    dut.i_cascade_sel.value = 0
    dut.i_data.value = 0
    for _ in range(5):
        await RisingEdge(dut.i_clk) 
        await Timer(100, units='ps')  # Adding a 100 ps delay   
    dut.i_rst_n.value = 1
    for _ in range(5):
        await RisingEdge(dut.i_clk)  
        await Timer(100, units='ps')  # Adding a 100 ps delay

    for data, expected_crc in crctest.test_data:
        # Test 1: Load initial CRC value and check
        dut.i_load_crc_start.value = 1
        await RisingEdge(dut.i_clk)
        await Timer(100, units='ps')  # Adding a 100 ps delay
        dut.i_load_crc_start.value = 0
        assert dut.o_crc.value == crctest.crc_poly_initial, "CRC initial value incorrect"

        # Test 2: Load data and validate CRC calculation
        # This step depends on having a known input-output pair for validation
        dut.i_data.value = data
        dut.i_load_from_cascade.value = 1
        dut.i_cascade_sel.value = find_highest_byte_enable(crctest.data_width)
        await RisingEdge(dut.i_clk)
        await Timer(100, units='ps')  # Adding a 100 ps delay
        dut.i_data.value = 0
        dut.i_load_from_cascade.value = 0
        dut.i_cascade_sel.value = 0
        await RisingEdge(dut.i_clk)
        await Timer(100, units='ps')  # Adding a 100 ps delay

        # Verify the CRC output matches the expected value
        # Note: You may need to adjust this depending on when the CRC output is valid
        actual_crc = dut.o_crc.value
        log.info(f'test_data=0x{hex(data)[2:].zfill(crctest.d_nybbles)}   expected_crc=0x{hex(expected_crc)[2:].zfill(crctest.nybbles)}  actual_crc=0x{hex(actual_crc)[2:].zfill(crctest.nybbles)}')
        assert hex(actual_crc) == hex(expected_crc), f"Unexpected CRC result: data=0x{hex(data)[2:].zfill(crctest.d_nybbles)}  expected {hex(expected_crc)} --> found {hex(dut.o_crc.value)}"

tf = TestFactory(crc_basic_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("algo_name, data_width, crc_width, poly, poly_init, refin, refout, xorout", crc_parameters)
def test_dataint_crc(request, algo_name, data_width, crc_width, poly, poly_init, refin, refout, xorout):
    dut_name = "dataint_crc"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_crc"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_crc_xor_shift.sv"),
        os.path.join(rtl_dir, "dataint_crc_xor_shift_cascade.sv"),
        os.path.join(rtl_dir, "dataint_crc.sv"),

    ]
    parameters = {'ALGO_NAME':algo_name,'DATA_WIDTH':data_width,'CRC_WIDTH':crc_width,'POLY':poly,'POLY_INIT':poly_init,'REFIN':refin,'REFOUT':refout,'XOROUT':xorout, }

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
