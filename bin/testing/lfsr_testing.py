def lfsr(seed, taps, width=8):
    """
    Generates subsequent values of an LFSR with specified width and tap positions.

    Args:
        seed (int): Initial seed value (integer).
        taps (list): List of tap positions (0-based indices).
        width (int, optional): Width of the LFSR (default is 8).

    Yields:
        int: Next LFSR value (0 or 1).
    """
    state = seed & ((1 << width) - 1)  # Ensure seed fits within specified width
    mask = sum(1 << t for t in taps)  # Create mask based on tap positions
    nbits = width - 1

    while True:
        result = (state << 1) & ((1 << width) - 1)
        xor = result >> nbits
        if xor != 0:
            result ^= mask
        yield result
        state = result
        # Terminate the loop when LFSR value equals the initial seed
        if state == seed:
            break

# Example usage:
seed_value = 0b11001001
tap_positions = [8, 7, 6, 1]
lfsr_width = 8

lfsr_generator = lfsr(seed_value, tap_positions, lfsr_width)
for _ in range(10):  # Generate 10 subsequent values
    print(next(lfsr_generator))
