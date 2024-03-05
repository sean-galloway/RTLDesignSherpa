import cocotb
import itertools
from cocotb.triggers import Timer
# from cocotb.regression import TestFactory
import itertools
import os
import random
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
from pathlib import Path


def configure_logging(dut_name, log_file_path):
    log = logging.getLogger(f'cocotb_log_{dut_name}')
    log.setLevel(logging.DEBUG)
    fh = logging.FileHandler(log_file_path)
    fh.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    log.addHandler(fh)
    return log

# Function to calculate the expected output with correct sign extension
def calculate_expected_output(booth_group, multiplicand, N):
    mask = (2**(N+1) - 1)
    msb = (multiplicand >> (N - 1)) & 1  # Extract the MSB for sign extension

    if booth_group in [0b000, 0b111]:
        return 0
    elif booth_group in [0b001, 0b010]:
        return (multiplicand & mask) | (msb << N)
    elif booth_group == 0b011:
        return ((multiplicand << 1) & mask) | (msb << N)
    elif booth_group == 0b100:
        return ((~(multiplicand << 1)) + 1) & mask
    elif booth_group in [0b101, 0b110]:
        return ((~(multiplicand | (msb << N))) + 1) & mask
    else:
        return 0  # Should not reach here

@cocotb.test()
async def exhaustive_test(dut):
    """ Test the Booth encoder with all possible input combinations for a given N. """
    N = int(os.environ.get('PARAM_N', '8'))  # Default to 8 if not set
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    max_val = 2**N
    for booth_group, multiplicand in itertools.product(range(8), range(max_val)):
        # Set the inputs
        dut.i_booth_group.value = booth_group
        dut.i_multiplicand.value = multiplicand
        log.info(f'{booth_group=}   {hex(multiplicand)}')

        # Wait for combinational logic to settle
        await Timer(1, units='ns')

        # Calculate the expected output
        expected = calculate_expected_output(booth_group, multiplicand, N)

        # Check the output
        found = int(dut.ow_booth_out.value)
        assert found == expected, f"Failed: booth_group={booth_group} multiplicand={hex(multiplicand)} expected={hex(expected)} got={hex(found)}"
# factory = TestFactory(exhaustive_test)
# factory.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4, 8])
def test_math_multiplier_booth_radix_4_encoder(request, n):
    dut_name = "math_multiplier_booth_radix_4_encoder"   
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_multiplier_booth_radix_4_encoder"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_multiplier_booth_radix_4_encoder.sv"),
    ]
    parameters = {'N':n, }

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
