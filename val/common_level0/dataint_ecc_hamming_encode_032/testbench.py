import cocotb
from cocotb.triggers import Timer
from cocotb.binary import BinaryValue
import os
import random

def calculate_ecc_32(data):
    """Calculate the expected ECC bits for given 32-bit data."""
    ecc = [0] * 6
    ecc[5] = data[31] ^ data[30] ^ data[28] ^ data[27] ^ data[25] ^ data[23] ^ data[21] ^ data[20] ^ data[18] ^ data[16] ^ data[14] ^ data[12] ^ data[10] ^ data[8] ^ data[6] ^ data[5] ^ data[3] ^ data[1]
    ecc[4] = data[31] ^ data[29] ^ data[28] ^ data[26] ^ data[25] ^ data[22] ^ data[21] ^ data[19] ^ data[18] ^ data[15] ^ data[14] ^ data[11] ^ data[10] ^ data[7] ^ data[6] ^ data[4] ^ data[3] ^ data[0]
    ecc[3] = data[30] ^ data[29] ^ data[28] ^ data[24] ^ data[23] ^ data[22] ^ data[21] ^ data[17] ^ data[16] ^ data[15] ^ data[14] ^ data[9] ^ data[8] ^ data[7] ^ data[6] ^ data[2] ^ data[1] ^ data[0]
    ecc[2] = data[27] ^ data[26] ^ data[25] ^ data[24] ^ data[23] ^ data[22] ^ data[21] ^ data[13] ^ data[12] ^ data[11] ^ data[10] ^ data[9] ^ data[8] ^ data[7] ^ data[6]
    ecc[1] = data[20] ^ data[19] ^ data[18] ^ data[17] ^ data[16] ^ data[15] ^ data[14] ^ data[13] ^ data[12] ^ data[11] ^ data[10] ^ data[9] ^ data[8] ^ data[7] ^ data[6]
    ecc[0] = data[5] ^ data[4] ^ data[3] ^ data[2] ^ data[1] ^ data[0]

    return ecc

@cocotb.test()
async def hamming_encode_32_test(dut):
    """Test the 32-bit Hamming code encoder with a subset of inputs."""
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')
    length = 32
    # Generate some data
    walk_1_through_0s = [1 << i for i in range(length)]
    all_ones = 0xFFFFFFFF  # This is 2^32 - 1, or 4294967295, with all bits set
    walk_0_through_1s_int = [all_ones ^ (1 << i) for i in range(32)]
    # Generating 1000 random integers from 0 to 2^32 - 1
    random_integers = [random.randint(0, 0xFFFFFFFF) for _ in range(1000)]
    test_list = walk_1_through_0s + walk_0_through_1s_int + random_integers

    for data_value in test_list:
        data_bin = format(data_value, '032b')
        data_list = [int(bit) for bit in data_bin[::-1]]  # LSB first as per usual digital logic convention

        # Apply the test case to the DUT inputs
        dut.i_data.value = data_value

        # Wait for the combinational logic to settle
        await Timer(5, units='ns')
        
        # Calculate expected ECC bits
        expected_ecc = calculate_ecc_32(data_list)
        
        # Convert the DUT ECC output to a list for easy comparison
        actual_ecc = [int(dut.o_ecc[i].value) for i in range(6)]
        
        # Verify the ECC bits match the expected values using an assertion
        assert actual_ecc == expected_ecc, f"ECC mismatch for data {data_bin}: expected {expected_ecc}, got {actual_ecc}"
