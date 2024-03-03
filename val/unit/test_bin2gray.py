import cocotb
from cocotb.triggers import Timer
from cocotb.binary import BinaryValue
from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_bin2gray')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_bin2gray.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


def binary_to_gray(bin_val):
    """Convert a binary value to its Gray code equivalent."""
    return bin_val ^ (bin_val >> 1)

@cocotb.test()
async def bin2gray_test(dut):
    width = len(dut.i_binary)
    last_gray = 0

    for i in range(2**width):
        dut.i_binary <= i
        await Timer(10, units='ns')
        current_gray = dut.ow_gray.value.integer

        # Check if Gray code conversion is correct
        expected_gray = binary_to_gray(i)
        assert current_gray == expected_gray, f"Error at {i}: Expected Gray code {expected_gray}, got {current_gray}"

        # Function to check if only one bit has changed
        def count_bit_changes(a, b):
            return bin(a ^ b).count('1')

        if i > 0:  # Skip the first comparison
            num_changes = count_bit_changes(last_gray, current_gray)
            assert num_changes == 1, f"Error at {i}: more than one bit changed from {bin(last_gray)} to {bin(current_gray)}"

        last_gray = current_gray

tf = TestFactory(bin2gray_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_bin2gray(request, width):
    dut = "bin2gray"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "bin2gray"   

    verilog_sources = [
        os.path.join(rtl_dir, "bin2gray.sv"),

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
