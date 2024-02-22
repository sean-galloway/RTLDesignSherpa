import cocotb
from cocotb.triggers import Timer
import os
import random

def check_hamming_encoded_data(encoded_data):
    # Calculate the number of parity bits
    parity_bits = len([bit for bit in encoded_data if bit == '1'])
    data_length = len(encoded_data) - parity_bits

    # Function to calculate parity for a given set of positions
    def calculate_parity(bits, positions):
        return sum(bits[pos] for pos in positions if pos < len(bits)) % 2

    # Determine the positions of the parity bits
    parity_positions = [2**i for i in range(parity_bits)]

    # Check the parity for each parity bit
    error_detected = False
    error_list = []
    for parity_pos in parity_positions:
        # Calculate the parity for the current group
        group_positions = [i for i in range(len(encoded_data)) if (i+1) & parity_pos]
        parity = calculate_parity(encoded_data, group_positions)

        # If parity does not match, add the bit to the error list
        if parity != encoded_data[parity_pos - 1]:
            error_detected = True
            error_list.append(parity_pos)

    # Determine if there is an error and its type
    if error_detected:
        return (False, encoded_data, f"Error detected in parity bit {error_list}")
    else:
        return (True, encoded_data, "No error detected")


@cocotb.test()
async def hamming_encode_test(dut):
    """Test the Hamming code encoder with exhaustive or random inputs."""
    width = int(os.environ.get('WIDTH', '0'))
    parity_bits = dut.ParityBits
    total_width = dut.TotalWidth
    max_value = 2**width
    if max_value < 2049:
        test_data = range(max_value)
    else:
        test_data = [random.randint(0, max_value-1) for _ in range(2049)]
    for data_value in test_data:
        # Apply the test case to the DUT inputs
        dut.i_data.value = data_value
        data_value_bin = format(data_value, f'0{width}b')
        print(f'i_data={data_value_bin} <----------------------------------')

        # Wait for the combinatorial logic to settle
        await Timer(5, units='ns')
        
        # Convert the DUT ECC output to a list of integers for easy comparison
        ow_encoded_data = dut.ow_encoded_data.value
        print(f'{ow_encoded_data=} <----------------------------------')
        # Convert to binary string, ensuring it's in '0' and '1'. Use binstr attribute for direct binary string representation.
        binary_str = ow_encoded_data.binstr
        # Convert the binary string to a list of integers (0 or 1), where the first element is the LSB and the last is the MSB.
        encoded_data_list = [int(bit) for bit in reversed(binary_str)]

        # Check encoded data
        (pass_or_fail, expected, msg) = check_hamming_encoded_data(encoded_data_list)
        
        # Verify the ECC bits match the expected values
        assert pass_or_fail == True, f"Mismatch for encoded data {data_value:x}: expected {expected:x}, got {encoded_data:x} Message: {msg}"
