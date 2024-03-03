import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.binary import BinaryValue
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_dataint_parity')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_dataint_parity.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


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

tf = TestFactory(parity_master_test)
tf.generate_tests()