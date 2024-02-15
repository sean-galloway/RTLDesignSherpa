import cocotb
from cocotb.triggers import Timer

def calculate_ecc(data):
    """Calculate the expected ECC bits for given data using the same logic as the Verilog module."""
    ecc = [0]*4
    ecc[3] = data[7] ^ data[6] ^ data[4] ^ data[3] ^ data[1]
    ecc[2] = data[7] ^ data[5] ^ data[4] ^ data[2] ^ data[1]
    ecc[1] = data[6] ^ data[5] ^ data[4] ^ data[0]
    ecc[0] = data[3] ^ data[2] ^ data[1] ^ data[0]
    return ecc

@cocotb.test()
async def hamming_encode_test(dut):
    """Test the Hamming code encoder with exhaustive inputs."""
    for data_value in range(256):  # Iterate over all possible 8-bit values
        data_bin = format(data_value, '08b')  # Convert to binary string
        data_list = [int(bit) for bit in data_bin[::-1]]  # Convert binary string to list of integers

        # Apply the test case to the DUT inputs
        dut.i_data.value = data_value

        # Wait for the combinational logic to settle
        await Timer(5, units='ns')
        
        # Calculate expected ECC bits
        expected_ecc = calculate_ecc(data_list)
        
        # Convert the DUT ECC output to a list of integers for easy comparison
        actual_ecc = [int(dut.o_ecc[i].value) for i in range(4)]
        
        # Verify the ECC bits match the expected values
        assert actual_ecc == expected_ecc, f"ECC mismatch for data {data_bin}: expected {expected_ecc}, got {actual_ecc}"
