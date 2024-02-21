def fibonacci_lfsr(seed, taps, width):
    """
    Generates subsequent values of a Fibonacci LFSR with a specified width.

    Args:
        seed (str): Initial seed (binary string).
        taps (tuple): Tuple of tap positions (0-based indices).
        width (int): Number of bits in the LFSR.

    Yields:
        int: Next LFSR value (0 or 1).
    """
    sr = seed.zfill(width)
    while True:
        xor = sum(int(sr[t - 1]) for t in taps) % 2
        yield xor
        sr = str(xor) + sr[:-1]
        if sr == seed:
            break

# Example usage:
seed_value = '11001001'
tap_positions = (8, 7, 6, 1)
lfsr_width = 8

lfsr_generator = fibonacci_lfsr(seed_value, tap_positions, lfsr_width)
for _ in range(10):  # Generate 10 subsequent values
    print(next(lfsr_generator))
