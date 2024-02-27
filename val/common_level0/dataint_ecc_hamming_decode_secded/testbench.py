import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import os
import random
import pprint
pp = pprint.PrettyPrinter(indent=4)
from ConstrainedRandom import ConstrainedRandom

def hamming_decode_secded(data_width, parity_bits, total_width, data, corrupt_vector):
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
        print(f'-------hds------------> covered_bits_str: {i} is {covered_bits_str}')        
        encoded_data[(2**i)-1] = sum(encoded_data[pos] for pos in covered_bits) % 2

    # Calculate the SECDED bit (overall parity bit)
    encoded_data[secded_pos] = sum(encoded_data[:-1]) % 2

    # print the encoded_data
    encoded_data_str = ''.join(str(bit) for bit in reversed(encoded_data))
    print(f'-------hds-----------------> encoded_data_str: {encoded_data_str}')

    # Apply the corrupt vector to simulate errors
    corrupted_data = [encoded_data[i] ^ corrupt_vector[i] for i in range(total_width)]

    # Calculate the syndrome
    syndrome = 0
    for i in range(parity_bits):
        covered_bits = get_covered_bits(i)
        par = (sum(corrupted_data[pos] for pos in covered_bits) % 2)
        syndrome |= par << i
        print(f'{i=} {syndrome=}')

    # print the encoded_data
    overall_parity = sum(corrupted_data[:-1]) % 2
    corrupted_data_str = ''.join(str(bit) for bit in reversed(corrupted_data))
    print(f'-------hds---------------> corrupted_data_str: {corrupted_data_str}')

    # print(f'hds: {syndrome=} {type(syndrome)=}')

    # Check the overall parity using the SECDED bit
    # overall_parity = corrupted_data[-1]
    syndrome_bin = format(syndrome, f'0{parity_bits}b')
    print(f'Expected overall parity and syndrome: {overall_parity} {syndrome_bin}')

    # Detect and correct errors
    error_detected = 0
    double_error_detected = 0
    if (overall_parity != corrupted_data[secded_pos]) and (syndrome < total_width):
        # Single-bit error detected and corrected
        error_detected = 1
        corrupted_data[syndrome - 1] ^= 1  # Flip the corrupted bit
    elif (overall_parity == encoded_data[secded_pos]) and (syndrome == ((2**parity_bits)-1)):
        # Double-bit error detected
        error_detected = 1
        double_error_detected = 1

    # Extract the corrected data
    corrected_data = [corrupted_data[bit_position(i)] for i in range(data_width)]

    return corrected_data, error_detected, double_error_detected


def hamming_encode(data, corruption_vector, data_width, parity_bits, total_width):
    corruption_vector_str = ''.join(str(bit) for bit in reversed(corruption_vector))
    print(f'----------------------> corruption_vector_str: {corruption_vector_str}')

    # Calculate the positions of the parity bits
    parity_positions = [2 ** i - 1 for i in range(parity_bits)]
    dpmap = ['d'] * total_width
    for i in parity_positions:
        dpmap[i] = 'P'
    dpmap[-1] = 'P'
    dpmap_str = ''.join(reversed(dpmap))
    print(f'----------------------------------> dpmap_str: {dpmap_str}')

    # Initialize the encoded data with zeros
    encoded_data = [0] * total_width

    # Copy the data bits to the encoded data
    data_index = 0
    for i in range(total_width - 1):
        if i not in parity_positions:
            encoded_data[i] = data[data_index]
            data_index += 1

    # Calculate the parity bits
    for i in range(parity_bits):
        parity = 0
        for j in range(total_width):
            if (j + 1) & (2 ** i):
                parity ^= encoded_data[j]
        encoded_data[parity_positions[i]] = parity

    # Calculate the total parity
    total_parity = 0
    for i in range(total_width - 1):
        total_parity ^= encoded_data[i]

    # Add the total parity to the last position of the encoded data
    encoded_data[-1] = total_parity
    encoded_data_str = ''.join(str(bit) for bit in reversed(encoded_data))
    print(f'---------------------------> encoded_data_str: {encoded_data_str} uncorrupted')

    # Apply the corruption vector
    for i in range(total_width):
        if corruption_vector[i]:
            encoded_data[i] ^= 1

    encoded_data_str = ''.join(str(bit) for bit in reversed(encoded_data))
    print(f'---------------------------> encoded_data_str: {encoded_data_str} corrupted')

    return encoded_data

def generate_known_data(data, total_width, test_data):
    c_vec = [0]*total_width
    test_data.append((data, c_vec))    
    for i in range(total_width):
        c_vec = [0]*total_width
        c_vec[i] = 1
        test_data.append((data, c_vec))


def generate_test_data(width, total_width, count_small=2, count_big=2048, seed=1234):
    print(f'{width=} {total_width=} {count_small=} {count_big=} {seed=}')

    test_data = []
    data = 0
    generate_known_data(data, total_width, test_data)

    data = (2**width)-1
    generate_known_data(data, total_width, test_data)

    even_alt_ones = [1 if i % 2 == 0 else 0 for i in range(width)]
    data_str = ''.join(str(bit) for bit in even_alt_ones)
    data = int(data_str, 2)
    generate_known_data(data, total_width, test_data)

    odd_alt_ones = [0 if i % 2 == 0 else 1 for i in range(width)]
    data_str = ''.join(str(bit) for bit in odd_alt_ones)
    data = int(data_str, 2)
    generate_known_data(data, total_width, test_data)

    # Define the constraints and weights for the corruption vector
    constraints = [(0, 0), (1, 1), (2, 2), (3, 3)]
    weights = [0.6, 0.2, 0.2, 0.0]

    # define the test data
    max_value = 2**width
    rand_count = -1
    if max_value < 2**16:
        data_value = range(count_small)
        rand_count = count_small
    else:
        data_value = [random.randint(0, max_value-1) for _ in range(count_big)]
        rand_count = count_big

    rand_corruption = []
    for _ in range(rand_count):
        # Create a ConstrainedRandom object with the constraints and weights
        crand = ConstrainedRandom(constraints, weights, seed)

        # Not corrupting the parity bit for now!!!! TODO
        # Generate a random corruption vector with a specified number of ones
        num_ones = crand.next()  # Get the number of ones from the ConstrainedRandom object
        corrupt_vector = [1] * num_ones + [0] * (total_width - num_ones - 1)

        # Shuffle the vector to randomize the positions of the ones
        random.shuffle(corrupt_vector)
        corrupt_vector.append(0)
        rand_corruption.append(corrupt_vector)

    rand_data = list(zip(data_value, rand_corruption))
    return test_data + rand_data


@cocotb.test()
async def test_hamming_decode_repair(dut):
    """Test Hamming code decoding and repair with exhaustive or random inputs."""
    # assert reset, put known values on inputs
    dut.i_rst_n.value = 0
    dut.i_enable.value = 0
    dut.i_hamming_data.value = 0

    clock = Clock(dut.i_clk, 10, units="ns")  # Create a 100MHz clock
    cocotb.start_soon(clock.start())  # Start the clock

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    width = int(os.environ.get('WIDTH', '0'))
    parity_bits = int(dut.ParityBits)
    total_width = int(dut.TotalWidth)

    test_data = generate_test_data(width, total_width, count_small=2, count_big=2048, seed=seed)
    print('------------------------------------------------------')
    for data_value, corrupt_vector in test_data:
        data_bin = format(data_value, f'0{width}b')
        corrupted_vector_str = ''.join(str(bit) for bit in reversed(corrupt_vector))
        print(f'data: {data_bin}   corrupt_vector: {corrupted_vector_str}')
    print('------------------------------------------------------')

    # de-assert reset
    for _ in range(5):
        await RisingEdge(dut.i_clk) 
        await Timer(100, units='ps')  # Adding a 100 ps delay   
    dut.i_rst_n.value = 1

    for data_value, corrupt_vector in test_data:
        data_bin = format(data_value, f'0{width}b')
        corrupted_vector_str = ''.join(str(bit) for bit in reversed(corrupt_vector))
        print(f'------------> data: {data_bin}   corrupt_vector: {corrupted_vector_str}')
        inject_count = corrupt_vector.count(1)
        print(f'-------------------> Error Count: {inject_count}')
        data_list = [int(bit) for bit in reversed(data_bin)]

        # Flip the bits in data_list according to corrupt_vector
        corrupted_data_list = hamming_encode(data_list, corrupt_vector, width, parity_bits, total_width)

        # Convert the corrupted_data_list to an integer
        corrupted_data_str = ''.join(str(bit) for bit in reversed(corrupted_data_list))
        corrupted_data_int = int(corrupted_data_str, 2)

        # Apply the data and corruption vector to the DUT
        dut.i_hamming_data.value = corrupted_data_int
        dut.i_enable.value= 1

        await RisingEdge(dut.i_clk)
        await Timer(100, units='ps')  # Adding a 100 ps delay

        # Sample the output signals
        output_data = dut.o_data.value.integer
        error_detected = dut.o_error_detected.value.integer
        double_error_detected = dut.o_double_error_detected.value.integer

        # Apply junk and disable for a clock
        dut.i_hamming_data.value = 0
        dut.i_enable.value= 0
        await RisingEdge(dut.i_clk)
        await Timer(100, units='ps')  # Adding a 100 ps delay

        output_data_bin = format(output_data, f'0{width}b')

        # Calculate the expected values
        (expected_data, expected_error_detected, expected_double_error_detected) = hamming_decode_secded(width, parity_bits, total_width, data_list, corrupt_vector)

        # Convert the list of bits to a string and then to an integer
        expected_data_int = int(''.join(str(bit) for bit in reversed(expected_data)), 2)
        expected_data_bin = format(expected_data_int, f'0{width}b')
        print(f'Found:    data={output_data_bin} s={error_detected} d={double_error_detected}')
        print(f'Expected: data={expected_data_bin} s={expected_error_detected} d={expected_double_error_detected}')

        if (output_data != expected_data_int) or \
                (error_detected != expected_error_detected) or \
                (expected_double_error_detected != expected_double_error_detected):
            pf = 'FAIL'
        else:
            pf = 'PASS'

        print('======================================================================')
        print(f'   {pf}: data={data_bin}   corrupt_vector={corrupted_vector_str}')
        print('======================================================================')

        # Assert the results
        assert output_data == expected_data_int, f"Expected data {expected_data_int}, but found {output_data}"
        assert error_detected == expected_error_detected, f"Expected error_detected to be {expected_error_detected}, but found {error_detected}"
        assert (
            expected_double_error_detected == expected_double_error_detected
        ), f"Expected double_error_detected to be {expected_double_error_detected}, but found {expected_double_error_detected}"

    dut.i_enable.value= 0
