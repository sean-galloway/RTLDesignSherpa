
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):
    q1 = queue.Queue()

    dut.high_count.value = 0
    dut.low_count.value = 0
    dut.repeat_count.value = 0
    dut.start.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())

    dut.rst_n.value = 0
    await Timer(20, units="ns")
    dut.rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")

    dut.high_count.value = 16
    dut.low_count.value = 8
    dut.repeat_count.value = 4
    dut.start.value = 1
    await Timer(20, units="ns")
    dut.start.value = 0

    await Timer(2500, units="ns")