import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.clock import Clock
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


# Function to convert binary to BCD for verification
def binary_to_bcd(decimal_val, digit_count):
    # Format the decimal value as a BCD string
    bcd_str = ''.join(f'{int(digit):04b}' for digit in f'{decimal_val:0{digit_count//4}d}')
    return int(bcd_str, 2)

@cocotb.test()
async def bin_to_bcd_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    # Start a clock
    clock = Clock(dut.i_clk, 10, units="ns")  # Adjust the timing as necessary
    cocotb.start_soon(clock.start())

    # Reset the DUT
    dut.i_start.value = 0
    dut.i_binary.value = 0
    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1

    # Parameters from DUT
    WIDTH = dut.WIDTH.value
    DIGITS = dut.DIGITS.value

    # Test all binary values
    for i in range(2**WIDTH):
        # print(f'Loop #{i}')
        # Drive the input signals
        await FallingEdge(dut.i_clk)
        dut.i_start.value = 1
        dut.i_binary.value = i
        await FallingEdge(dut.i_clk)
        dut.i_start.value = 0

        # Wait for the module to complete processing
        await RisingEdge(dut.o_done)
        await FallingEdge(dut.i_clk)
        
        # Verify the output
        expected_bcd = binary_to_bcd(i, DIGITS*4)
        msg = f"Error: Binary={bin(i)}, Expected BCD={expected_bcd}, Module BCD={int(dut.o_bcd.value)}"
        assert int(dut.o_bcd.value) == expected_bcd, msg
        if int(dut.o_bcd.value) != expected_bcd:
            log.error(msg)

        # Wait a clock cycle before the next test iteration
        await RisingEdge(dut.i_clk)

# tf = TestFactory(bin_to_bcd_test)
# tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_bin_to_bcd(request, width):
    dut_name = "bin_to_bcd"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "bin_to_bcd"   

    verilog_sources = [
        os.path.join(rtl_dir, "bin_to_bcd.sv"),

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
