import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.binary import BinaryValue
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


async def check_parity(dut, WIDTH, CHUNKS, CHUNK_SIZE, EXTRA_BITS, LAST_CHUNK_SIZE, data, parity, parity_type):
    """
    Apply data, parity, and parity type to the DUT,
    then check if the calculated parity and error detection are correct.
    """
    # Drive the DUT inputs
    dut.i_data.value = data
    dut.i_parity.value = parity
    dut.i_parity_type.value = parity_type

    # Wait for the DUT to process the inputs
    await Timer(5, units='ns')

    # Calculate expected values for ow_parity and ow_error
    expected_parity = BinaryValue(0, n_bits=CHUNKS, bigEndian=False)
    expected_error = BinaryValue(0, n_bits=CHUNKS, bigEndian=False)

    for i in range(CHUNKS):
        chunk_start = i * CHUNK_SIZE
        chunk_end = WIDTH-1 if (i == CHUNKS-1) else chunk_start + CHUNK_SIZE - 1
        chunk_data = data[chunk_end:chunk_start]
        calculated_chunk_parity = bin(chunk_data.value).count('1') % 2 # Count the number of '1's and mod by 2
        if parity_type.value == 1:  # Even parity
            expected_parity[i] = calculated_chunk_parity
        else:  # Odd parity
            expected_parity[i] = not calculated_chunk_parity
        expected_error[i] = (expected_parity[i] != parity[i])

    # Compare expected and actual outputs
    if dut.ow_parity.value != expected_parity or dut.ow_error.value != expected_error:
        raise AssertionError(f"Parity or error mismatch! "
                                f"Data: {data}, Parity: {parity}, Parity Type: {parity_type}, "
                                f"Expected ow_parity: {expected_parity}, Actual ow_parity: {dut.ow_parity.value}, "
                                f"Expected ow_error: {expected_error}, Actual ow_error: {dut.ow_error.value}")
    else:
        cocotb.log.info(f"Test passed for Data: {data}, Parity: {parity}, Parity Type: {parity_type}")

@cocotb.test()
async def parity_master_test(dut):
    """
    Master function that retrieves WIDTH and CHUNKS from the DUT,
    and exhaustively tests the parity generation and error detection.
    """
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    WIDTH = len(dut.i_data)
    CHUNKS = len(dut.i_parity)
    CHUNK_SIZE, EXTRA_BITS = divmod(WIDTH, CHUNKS)
    LAST_CHUNK_SIZE = EXTRA_BITS if EXTRA_BITS > 0 else CHUNK_SIZE

    for i in range(CHUNKS):
        chunk_start = i * CHUNK_SIZE
        chunk_end = WIDTH-1 if (i == CHUNKS-1) else chunk_start + CHUNK_SIZE - 1
        log.info(f'Chunk {i} --> {chunk_end}:{chunk_start}')

    # Start the clock (if necessary for your DUT)
    # cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    # Example test values, adjust as necessary for exhaustive testing
    # For exhaustive testing, iterate over all possible data and parity combinations
    for data_val, parity_val in itertools.product(range(1 << WIDTH), range(1 << CHUNKS)):
        for parity_type_val in [0, 1]:
            # Convert integers to binary values with proper bit lengths
            data = BinaryValue(data_val, n_bits=WIDTH, bigEndian=False)
            parity = BinaryValue(parity_val, n_bits=CHUNKS, bigEndian=False)
            parity_type = BinaryValue(parity_type_val, n_bits=1, bigEndian=False)

            # Call the sub-function to perform the test with the current set of values
            await check_parity(dut, WIDTH, CHUNKS, CHUNK_SIZE, EXTRA_BITS, LAST_CHUNK_SIZE, data, parity, parity_type)

# tf = TestFactory(parity_master_test)
# tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("chunks, width", [(3, 10)])
def test_dataint_parity(request, chunks, width):
    dut_name = "dataint_parity"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_parity"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_parity.sv"),

    ]
    parameters = {'CHUNKS':chunks,'WIDTH':width, }

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
