import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
import os
import random
from crccheck.crc import CrcBase

class MyCustomCrc(CrcBase):
    _width = 8
    _poly = 0x07
    _initvalue = 0x00
    _reflect_input = False
    _reflect_output = False
    _finalxor = 0x00

@cocotb.test()
async def test_crc_basic(dut):
    """ Test the CRC calculation for a basic input """
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    clock = Clock(dut.i_clk, 10, units="ns")  # Create a 100MHz clock
    cocotb.start_soon(clock.start())  # Start the clock
    # Gather the settings from the Parameters to verify them
    data_width = int(dut.DATA_WIDTH)
    chunks = int(dut.CHUNKS)
    d_nybbles = chunks // 2
    crc_width = int(dut.CRC_WIDTH)
    nybbles = crc_width // 4
    crc_poly = int(dut.POLY) & 0xFFFFFFFF
    crc_poly_initial = int(dut.POLY_INIT) & 0xFFFFFFFF
    reflected_input = int(dut.REFIN)
    reflected_output = int(dut.REFOUT)
    xor_output = int(dut.XOROUT) & 0xFFFFFFFF
    print('-------------------------------------------')
    print('Settings:')
    print(f'    DATA_WIDTH: {data_width}')
    print(f'    CHUNKS:     {chunks}')
    print(f'    CRC_WIDTH:  {crc_width}')
    print(f'    POLY:       0x{hex(crc_poly)[2:].zfill(crc_width // 4)}')
    print(f'    POLY_INIT:  0x{hex(crc_poly_initial)[2:].zfill(crc_width // 4)}')
    print(f'    REFIN:      {reflected_input}')
    print(f'    REFOUT:     {reflected_output}')
    print(f'    XOROUT:     0x{hex(xor_output)[2:].zfill(crc_width // 4)}')
    print('-------------------------------------------')

    test_values = [ 0x1234,
                    0x0000,
                    0x0001,
                    0x0002,
                    0x0004,
                    0x0008,
                    0x0010,
                    0x0020,
                    0x0040,
                    0x0080,
                    0x0100,
                    0x0200,
                    0x0400,
                    0x0800,
                    0x1000,
                    0x2000,
                    0x4000,
                    0x8000]
    test_data = []
    for data in test_values:
        data_bytes = data.to_bytes(chunks, 'little')
        ecc = MyCustomCrc.calc(data_bytes)
        test_data.append((data, ecc))

    # add some random values to the list
    for _ in range(100):
        data = random.randint(0x00,0xFFFF)
        data_bytes = data.to_bytes(chunks, 'little')
        ecc = MyCustomCrc.calc(data_bytes)
        test_data.append((data, ecc))

    ##########################################################################
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
        dut.i_cascade_sel.value = 0x2
        await FallingEdge(dut.i_clk)
        dut.i_data.value = 0
        dut.i_load_from_cascade.value = 0
        dut.i_cascade_sel.value = 0
        await FallingEdge(dut.i_clk)  

        # Verify the CRC output matches the expected value
        # Note: You may need to adjust this depending on when the CRC output is valid
        actual_crc = dut.o_crc.value
        print(f'test_data=0x{hex(data)[2:].zfill(d_nybbles)}   expected_crc=0x{hex(expected_crc)[2:].zfill(nybbles)}  actual_crc=0x{hex(actual_crc)[2:].zfill(nybbles)}')
        assert actual_crc == expected_crc, f"Unexpected CRC result: data=0x{hex(data)[2:].zfill(d_nybbles)}  expected {hex(expected_crc)} --> found {hex(dut.o_crc.value)}"
