
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):

    dut.data.value = 0x0000
    await Timer(20, units="ns")

    dut.data.value = 0xFFFF
    await Timer(20, units="ns")

    await Timer(200, units="ns")

    hex_val = 0xFFFF
    # Walk 0's, low to high
    for i in range(16, -1, -1):
        hex_val &= ~(1<<i)
        print(f'Part 1: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.data.value = dec_val
        await Timer(20, units="ns")
    
    dut.data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x0000
    # Walk 1's, low to high
    for i in range(15, -1, -1):
        hex_val |= (1<<i)
        print(f'Part 2: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.data.value = dec_val
        await Timer(20, units="ns")

    dut.data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")
    
    hex_val = 0xFFFF
    # Walk single 0, low to high
    for i in range(16):
        hex_val &= ~(1<<i)
        print(f'Part 3: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.data.value = dec_val
        await Timer(20, units="ns")

    dut.data.value = 0x0000
    await Timer(20, units="ns")
    await Timer(200, units="ns")

    hex_val = 0x1
    # Walk single 1, low to high
    for i in range(16):
        print(f'Part 4: i={i}, hex={hex_val}')
        dec_val = int(hex_val)
        dut.data.value = dec_val
        await Timer(20, units="ns")
        hex_val = hex_val * 2

    await Timer(200, units="ns")


