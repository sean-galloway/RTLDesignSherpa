
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    dut.i_rst_n.value = 0
    dut.i_start.value = 0
    dut.i_binary.value = 0     

    await Timer(20, units="ns")

    dut.i_binary.value = 0x0
    await Timer(20, units="ns")

    dut.i_rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")

    for i in range(1000):
        dut.i_binary.value = i
        dut.i_start.value = 1      
        await Timer(20, units="ns")
        dut.i_start.value = 0      
        await Timer(3000, units="ns")

    await Timer(200, units="ns")

