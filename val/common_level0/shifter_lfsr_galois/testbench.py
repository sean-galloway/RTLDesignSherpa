import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.clock import Clock
from cocotb.regression import TestFactory
import os
import random


# Utility function to run an LFSR test with given parameters
async def run_lfsr_test(dut, seed_value, taps, N):
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.i_rst_n.value = 0
    dut.i_enable.value = 0
    dut.i_seed_load.value = 0
    dut.i_seed_data.value = 0
    dut.i_taps.value = 0
    await Timer(10, units="ns")
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    # Load the seed and configure the taps
    dut.i_seed_load.value = 1
    dut.i_seed_data.value = seed_value
    dut.i_taps.value = taps
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_seed_load.value = 0
    dut.i_enable.value = 1

    # Monitor the LFSR output
    cycle_count = 0
    while int(dut.o_lfsr_out.value) != seed_value:
        await FallingEdge(dut.i_clk)
        cycle_count += 1
        # Limit to prevent infinite loops, adjust as necessary
        if cycle_count > 2**N:  
            print("Failed to loop back to the initial seed within a reasonable number of cycles.")
            break

    dut.i_enable.value = 0  # Disable LFSR
    
    # Reporting
    print(f"For seed={seed_value:0{N}b} and taps={taps}, it took {cycle_count} cycles to repeat.")

# Master function to generate and schedule tests based on parameters
async def schedule_tests(dut):
    N = len(dut.i_seed_data)
    # Define your tests here, for example:
    bin_str = ''.join(format(num, '012b') for num in (8, 6, 5, 4))
    print(f'{bin_str=}')
    seeds_and_taps = [
        (random.getrandbits(N), int(bin_str,2))
    ]

    for seed, taps in seeds_and_taps:
        await run_lfsr_test(dut, seed, taps, N)

# Entry point for the cocotb test
@cocotb.test()
async def dynamic_lfsr_tests(dut):
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')
    await schedule_tests(dut)

tf = TestFactory(dynamic_lfsr_tests)
tf.generate_tests()