
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):

    dut.write_A.value = 0
    dut.wr_data_A.value = 0
    dut.write_B.value = 0
    dut.wr_data_B.value = 0
    dut.write_C.value = 0
    dut.wr_data_C.value = 0
    dut.write_D.value = 0
    dut.wr_data_D.value = 0
    dut.start_pwm.value = 0

    cocotb.start_soon(Clock(dut.clk, 10, units="ns").start())

    dut.rst_n.value = 0
    await Timer(20, units="ns")
    dut.rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")

    dut.start_pwm.value = 1
    await Timer(20, units="ns")
    dut.start_pwm.value = 0

    dut.write_A.value = 1
    dut.wr_data_A.value = 160
    dut.write_B.value = 1
    dut.wr_data_B.value = 176
    dut.write_C.value = 1
    dut.wr_data_C.value = 192
    dut.write_D.value = 1
    dut.wr_data_D.value = 208
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+1
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+1
    dut.write_C.value = 1
    dut.wr_data_C.value = 192+1
    dut.write_D.value = 1
    dut.wr_data_D.value = 208+1
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+2
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+2
    dut.write_C.value = 1
    dut.wr_data_C.value = 192+2
    dut.write_D.value = 1
    dut.wr_data_D.value = 208+2
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+3
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+3
    dut.write_C.value = 1
    dut.wr_data_C.value = 192+3
    dut.write_D.value = 1
    dut.wr_data_D.value = 208+3
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+4
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+4
    dut.write_C.value = 0
    dut.write_D.value = 0
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+5
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+5
    dut.write_C.value = 0
    dut.write_D.value = 0
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+6
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+6
    dut.write_C.value = 0
    dut.write_D.value = 0
    await Timer(10, units="ns")

    dut.write_A.value = 1
    dut.wr_data_A.value = 160+7
    dut.write_B.value = 1
    dut.wr_data_B.value = 176+7
    dut.write_C.value = 0
    dut.write_D.value = 0
    await Timer(10, units="ns")

    for i in range(8, 16):
        dut.write_A.value = 1
        dut.wr_data_A.value = 160+i
        dut.write_B.value = 0
        dut.write_C.value = 0
        dut.write_D.value = 0
        await Timer(10, units="ns")

    dut.write_A.value = 0
    dut.write_B.value = 0
    dut.write_C.value = 0
    dut.write_D.value = 0
    await Timer(10, units="ns")

    await Timer(5000, units="ns")