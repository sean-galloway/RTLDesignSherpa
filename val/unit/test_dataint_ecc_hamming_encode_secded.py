import cocotb
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
import os
import subprocess
import random

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_dataint_ecc_hamming_encode_secded')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_dataint_ecc_hamming_encode_secded.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


def hamming_encode_secded(data_width, parity_bits, total_width, data):
    # Calculate the position for the SECDED bit, which is the last bit
    secded_pos = total_width - 1

    # Function to calculate the bit position for data insertion
    def bit_position(k):
        pos = k + 1  # Start at k+1 to account for the parity bit at position 0
        for j in range(parity_bits):
            if pos >= (2**j):
                pos += 1
        return pos - 1  # Convert back to 0-based index

    # Function to get a bit mask for the bits covered by a given parity bit
    def get_covered_bits(parity_bit):
        return [i for i in range(total_width-1) if (i+1) & (1 << parity_bit)]

    def get_covered_bits_list(covered_bits, total_width):
        # Initialize a list of zeros with length equal to total_width
        bits_list = [0] * total_width
        # Set positions specified in covered_bits to 1
        for index in covered_bits:
            if index < total_width:  # Ensure index is within the range
                bits_list[index] = 1
        return bits_list

    dpmap = ['d'] * total_width
    for i in range(parity_bits):
        dpmap[(2**i)-1] = 'P'
    dpmap[-1] = 'O'
    dpmap_str = ''.join(reversed(dpmap))
    log.info(f'----------------------------------> dpmap_str: {dpmap_str}')

    # Encode the data with parity bits
    encoded_data = [0] * total_width
    for i, bit in enumerate(data):
        encoded_data[bit_position(i)] = bit
    
    # print the encoded_data
    encoded_data_str = ''.join(str(bit) for bit in reversed(encoded_data))
    # print(f'-------hds-----------------> encoded_data_str: {encoded_data_str} pre-parity')

    # Calculate parity bits for the encoded data
    for i in range(parity_bits):
        covered_bits = get_covered_bits(i)
        # print(f'{covered_bits=}')
        covered_bits_vec = get_covered_bits_list(covered_bits, total_width)
        covered_bits_str = ''.join(str(bit) for bit in reversed(covered_bits_vec))
        log.info(f'-------hds------------> covered_bits_str: {i} is {covered_bits_str}')        
        encoded_data[(2**i)-1] = sum(encoded_data[pos] for pos in covered_bits) % 2

    # Calculate the SECDED bit (overall parity bit)
    encoded_data[secded_pos] = sum(encoded_data[:-1]) % 2

    # print the encoded_data
    encoded_data_str = ''.join(str(bit) for bit in reversed(encoded_data))
    log.info(f'-------hds-----------------> encoded_data_str: {encoded_data_str}')
    return encoded_data_str


@cocotb.test()
async def hamming_encode_test(dut):
    """Test the Hamming code encoder with exhaustive or random inputs."""
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    log.info(f'seed changed to {seed}')

    data_width = int(os.environ.get('WIDTH', '0'))
    parity_bits = int(dut.ParityBits)
    total_width = int(dut.TotalWidth)
    log.info("-------------------------------------------")
    log.info(f"Data Width   {data_width}")
    log.info(f"Parity Bits  {parity_bits}")
    log.info(f"Total Width  {total_width}")
    log.info("-------------------------------------------")
    
    max_value = 2**data_width
    if max_value < 2049:
        test_data = range(max_value)
    else:
        test_data = [random.randint(0, max_value-1) for _ in range(2049)]
    for data_value in test_data:
        # Apply the test case to the DUT inputs
        dut.i_data.value = data_value
        data_value_bin = format(data_value, f'0{data_width}b')
        data_list = [int(bit) for bit in reversed(data_value_bin)]
        log.info(f'i_data={data_value_bin} <----------------------------------')

        # Wait for the combinatorial logic to settle
        await Timer(5, units='ns')
        
        # Convert the DUT ECC output to a list of integers for easy comparison
        ow_encoded_data = dut.ow_encoded_data.value.integer
        output_data_bin = format(ow_encoded_data, f'0{total_width}b')

        log.info(f'{output_data_bin=} {len(output_data_bin)=}<----------------------------------')

        # Check encoded data
        expected_data_str = hamming_encode_secded(data_width, parity_bits, total_width, data_list)
        
        # Verify the ECC bits match the expected values
        assert output_data_bin == expected_data_str, f"Mismatch for data value {output_data_bin} expected {expected_data_str}"

tf = TestFactory(hamming_encode_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(8,)])
def test_dataint_ecc_hamming_encode_secded(request, width):
    dut = "dataint_ecc_hamming_encode_secded"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_ecc_hamming_encode_secded"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_ecc_hamming_encode_secded.sv"),

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
