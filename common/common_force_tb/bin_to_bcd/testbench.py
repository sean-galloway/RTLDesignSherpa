
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):

    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())

    dut.rst_n.value = 0
    dut.start.value = 0
    dut.binary_in.value = 0     

    await Timer(20, units="ns")

    dut.binary_in.value = 0x0
    await Timer(20, units="ns")

    dut.rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")

    for i in range(1000):
        dut.binary_in.value = i
        dut.start.value = 1      
        await Timer(20, units="ns")
        dut.start.value = 0      
        await Timer(3000, units="ns")

    await Timer(200, units="ns")

