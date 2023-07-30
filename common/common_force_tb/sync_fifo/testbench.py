
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):
    q1 = queue.Queue()

    dut.write.value = 0
    dut.read.value = 0
    dut.wr_data.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())

    dut.rst_n.value = 0
    await Timer(20, units="ns")
    dut.rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")
    i=0
    for _ in range(4):
        depth = 3
        while dut.wr_full.value == 0:
            dut.write.value = 1
            dut.wr_data.value = i
            q1.put(i) # this will add item from 0 to depth to the queue
            await Timer(10, units="ns")
            i++

        dut.write.value = 0

        await Timer(100, units="ns")

        golden_data_out=0

        while dut.rd_empty.value == 0:
            dut.read.value = 1
            golden_data_out = q1.get()
            print("FIFO data_out Value=",int(dut.rd_data.value), "Queue Value=",int(golden_data_out))
            assert dut.rd_data.value == golden_data_out, "test failed"
            await Timer(10, units="ns")

        dut.read.value = 0

    await Timer(500, units="ns")