import cocotb
from cocotb.triggers import Timer
import random

# A function to generate ECC for given data, mirroring your encoder's functionality.
# You would replace this with your actual ECC generation logic.
def generate_ecc(data):
    """Calculate the expected ECC bits for given data using the same logic as the Verilog module."""
    ecc =[0]*4
    ecc[3] = data[7] ^ data[6] ^ data[4] ^ data[3] ^ data[1]
    ecc[2] = data[7] ^ data[5] ^ data[4] ^ data[2] ^ data[1]
    ecc[1] = data[6] ^ data[5] ^ data[4] ^ data[0]
    ecc[0] = data[3] ^ data[2] ^ data[1] ^ data[0]
    return ecc

@cocotb.test()
async def test_hamming_decode_repair(dut):
    """Test Hamming code decoding and repair for all data inputs with correct ECC."""
    for data_value in range(256):  # 2^8 possible data inputs
        data_bin = format(data_value, '032b')
        data_list = [int(bit) for bit in data_bin[::-1]] 
        ecc_value = generate_ecc(data_list)  # Generate ECC for this data input
        ecc = int(''.join(str(bit) for bit in ecc_value[::-1]), 2)

        # Apply data and ECC to DUT
        dut.i_data.value = data_value
        dut.i_ecc.value = ecc
        
        await Timer(5, units='ns')  # Wait for logic to process
        
        # Check if data is correctly passed through and no error is reported
        print(f'Pass Testing: {data_value=} {ecc=}')
        assert dut.o_data.value == data_value, f"Data mismatch (no error expected) for input {data_value}"
        assert dut.o_error.value == 0, f"Unexpected error flag for correct input {data_value=} {ecc_value}"
        assert dut.o_repairable.value == 0, f"Unexpected repairable flag for correct input {data_value}"

        # Now, introduce a single-bit error in data to test error detection and repair
        # This is a simplified scenario; you would iterate over all bits for exhaustive testing
        error_bit_position = random.randint(0, 7)  # Introduce error at a random position
        data_with_error = data_value ^ (1 << error_bit_position)
        
        # Reapply erroneous data and original ECC to DUT
        print(f'Fail Testing: {data_with_error=} {ecc=}')
        dut.i_data.value = data_with_error

        await Timer(5, units='ns')  # Wait for logic to process
        
        # Check if error is detected and optionally if correctable error is repaired
        # The specific assertions here will depend on the expected behavior of your DUT with erroneous inputs
        assert dut.o_error.value == 1 and dut.o_repairable.value == 1, f"Unexpected, non-repairable error {data_with_error=} {ecc_value=}"
