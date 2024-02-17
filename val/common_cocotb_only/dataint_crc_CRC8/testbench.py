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
    data_width = int(dut.DATA_WIDTH)
    chunks = int(dut.CHUNKS)
    crc_poly = int(dut.CRC_POLY) & 0xFFFFFFFF
    crc_poly_initial = int(dut.CRC_POLY_INITIAL) & 0xFFFFFFFF
    reflected_input = int(dut.REFLECTED_INPUT)
    reflected_output = int(dut.REFLECTED_OUTPUT)
    xor_output = int(dut.XOR_OUTPUT) & 0xFFFFFFFF
    print('-------------------------------------------')
    print('Settings:')
    print(f'    DATA_WIDTH:       {data_width}')
    print(f'    CHUNKS:           {chunks}')
    print(f'    CRC_POLY:         {hex(crc_poly)}')
    print(f'    CRC_POLY_INITIAL: {hex(crc_poly_initial)}')
    print(f'    REFLECTED_INPUT:  {reflected_input}')
    print(f'    REFLECTED_OUTPUT: {reflected_output}')
    print(f'    XOR_OUTPUT:       {hex(xor_output)}')
    print('-------------------------------------------')

    test_data = [
        (0x12, 0x7E),
        (0x0, 0x00),
        (0x1, 0x07),
        (0x2, 0x0E),
        (0x4, 0x1C),
        (0x8, 0x38),
        (0x10, 0x70),
        (0x20, 0xE0),
        (0x40, 0xC7),
        (0x80, 0x89)
    ]

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

    for data, expected_crc in test_data:
        # Test 1: Load initial CRC value and check
        dut.i_load_crc_start.value = 1
        await FallingEdge(dut.i_clk)  
        dut.i_load_crc_start.value = 0
        assert dut.o_crc.value == crc_poly_initial, "CRC initial value incorrect"

        # Test 2: Load data and validate CRC calculation
        # This step depends on having a known input-output pair for validation
        dut.i_data.value = data
        dut.i_load_from_cascade.value = 1
        dut.i_cascade_sel.value = 1
        await FallingEdge(dut.i_clk)
        dut.i_data.value = 0
        dut.i_load_from_cascade.value = 0
        dut.i_cascade_sel.value = 0
        await FallingEdge(dut.i_clk)  

        # Verify the CRC output matches the expected value
        # Note: You may need to adjust this depending on when the CRC output is valid
        actual_crc = dut.o_crc.value
        print(f'test_data={hex(data)}   expected_crc={hex(expected_crc)}  actual_crc={hex(actual_crc)}')
        assert actual_crc == expected_crc, f"Unexpected CRC result: expected {hex(expected_crc)} --> found {hex(dut.o_crc.value)}"

