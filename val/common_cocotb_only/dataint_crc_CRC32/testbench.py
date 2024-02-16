import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
import os
import random

@cocotb.test()
async def test_crc_basic(dut):
    """ Test the CRC calculation for a basic input """
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    clock = Clock(dut.i_clk, 10, units="ns")  # Create a 100MHz clock
    cocotb.start_soon(clock.start())  # Start the clock

    # Reset
    dut.i_rst_n.value = 0
    # Initialize inputs
    dut.i_load_crc_start.value = 0
    dut.i_load_from_cascade.value = 0
    dut.i_cascade_sel.value = 0
    dut.i_data.value = 0
    for _ in range(5):
        await FallingEdge(dut.i_clk)    
    dut.i_rst_n.value = 1
    for _ in range(5):
        await FallingEdge(dut.i_clk)  

    # Test 1: Load initial CRC value and check
    dut.i_load_crc_start.value = 1
    await FallingEdge(dut.i_clk)  
    dut.i_load_crc_start.value = 0
    assert dut.o_crc.value == int(dut.CRC_POLY_INITIAL), "CRC initial value incorrect"

    # Test 2: Load data and validate CRC calculation
    # This step depends on having a known input-output pair for validation
    test_data = 0x12345678  # Example test data
    expected_crc = 0xFFFFFFFF  # Replace with the expected CRC result for test_data
    dut.i_data.value = test_data
    dut.i_load_from_cascade.value = 1
    dut.i_cascade_sel.value = 1  # Adjust this to select the correct cascade input
    await FallingEdge(dut.i_clk)  

    # Verify the CRC output matches the expected value
    # Note: You may need to adjust this depending on when the CRC output is valid
    actual_crc = dut.o_crc.value
    print(f'test_data={hex(test_data)}   expected_crc={hex(expected_crc)}  actual_crc={hex(actual_crc)}')
    assert actual_crc == expected_crc, f"Unexpected CRC result: {hex(dut.o_crc.value)}"

    # Further tests can be added here to cover more scenarios and data patterns
