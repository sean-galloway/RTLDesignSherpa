import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
import os
import random
from crc_testing import CRCTesting

@cocotb.test()
async def test_crc_basic(dut):
    """ Test the CRC calculation for a basic input """
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    print(f'seed changed to {seed}')

    clock = Clock(dut.i_clk, 10, units="ns")  # Create a 100MHz clock
    cocotb.start_soon(clock.start())  # Start the clock

    crctest = CRCTesting(dut, 100)
    crctest.print_settings()
    crctest.generate_test_data()
    
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

    for data, expected_crc in crctest.test_data:
        # Test 1: Load initial CRC value and check
        dut.i_load_crc_start.value = 1
        await FallingEdge(dut.i_clk)  
        dut.i_load_crc_start.value = 0
        assert dut.o_crc.value == crctest.crc_poly_initial, "CRC initial value incorrect"

        # Test 2: Load data and validate CRC calculation
        # This step depends on having a known input-output pair for validation
        dut.i_data.value = data
        dut.i_load_from_cascade.value = 1
        dut.i_cascade_sel.value = 2
        await FallingEdge(dut.i_clk)
        dut.i_data.value = 0
        dut.i_load_from_cascade.value = 0
        dut.i_cascade_sel.value = 0
        await FallingEdge(dut.i_clk)  

        # Verify the CRC output matches the expected value
        # Note: You may need to adjust this depending on when the CRC output is valid
        actual_crc = dut.o_crc.value
        print(f'test_data=0x{hex(data)[2:].zfill(crctest.d_nybbles)}   expected_crc=0x{hex(expected_crc)[2:].zfill(crctest.nybbles)}  actual_crc=0x{hex(actual_crc)[2:].zfill(crctest.nybbles)}')
        assert actual_crc == expected_crc, f"Unexpected CRC result: data=0x{hex(data)[2:].zfill(crctest.d_nybbles)}  expected {hex(expected_crc)} --> found {hex(dut.o_crc.value)}"
