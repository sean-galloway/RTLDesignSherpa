
import queue
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, Timer

@cocotb.test()
async def test_fifo(dut):

    dut.i_write_A.value = 0
    dut.i_wr_data_A.value = 0
    dut.i_write_B.value = 0
    dut.i_wr_data_B.value = 0
    dut.i_write_C.value = 0
    dut.i_wr_data_C.value = 0
    dut.i_write_D.value = 0
    dut.i_wr_data_D.value = 0
    dut.start_pwm.value = 0

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)

    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)

    await FallingEdge(dut.i_clk)

    dut.start_pwm.value = 1
    await FallingEdge(dut.i_clk)
    # dut.start_pwm.value = 0

    for i in range(40):
        dut.i_write_A.value = 0
        while dut.o_wr_full_A.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_A.value = 1
        dut.i_wr_data_A.value = 160+i
        await FallingEdge(dut.i_clk)
    dut.i_write_A.value = 0

    for i in range(24):
        dut.i_write_B.value = 0
        while dut.o_wr_full_B.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_B.value = 1
        dut.i_wr_data_B.value = 176+i
        await FallingEdge(dut.i_clk)
    dut.i_write_B.value = 0

    for i in range(12):
        dut.i_write_C.value = 0
        while dut.o_wr_full_C.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_C.value = 1
        dut.i_wr_data_C.value = 192+i
        await FallingEdge(dut.i_clk)
    dut.i_write_C.value = 0


    for i in range(6):
        dut.i_write_D.value = 0
        while dut.o_wr_full_D.value == 1:
            await FallingEdge(dut.i_clk)
        dut.i_write_D.value = 1
        dut.i_wr_data_D.value = 208+i
        await FallingEdge(dut.i_clk)
    dut.i_write_D.value = 0

    for _ in range(200):
        await FallingEdge(dut.i_clk)
