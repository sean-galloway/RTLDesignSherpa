
import queue
from cocotb.triggers import Clock, Timer
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

    i=0
    await Timer(5, units="ns")
    while dut.wr_full.value == 0:
        q1.put(i) # this will additem from 0 to 20 to the queue
        dut.din.value = i;
        dut.wr_en.value = 1;
        await Timer(10, units="ns")
        i = i + 1;
        
    dut.wr_en.value = 0;
    
    await Timer(100, units="ns")

    golden_dout=0
    
    while dut.rd_empty.value == 0:
        dut.rd_en.value = 1
        golden_dout = q1.get()
        await Timer(10, units="ns")
        print("FIFO Dout Value=",int(dut.dout.value), "Queue Value=",int(golden_dout))
        assert dut.dout.value == golden_dout, "test failed"
        
    dut.rd_en.value = 0

    await Timer(500, units="ns")