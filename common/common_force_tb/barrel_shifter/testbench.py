
import queue
from cocotb.clock import Clock
from cocotb.triggers import Timer
import cocotb

@cocotb.test()
async def test_fifo(dut):

    dut.data_in.value = 0xFFFF
    dut.shift_amount.value = 1
    dut.ctrl.value = 0x0
    await Timer(20, units="ns")

    for i in range(17):
        dut.data_in.value = 0xFFFF
        dut.shift_amount.value = i
        dut.ctrl.value = 0x1
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0xFFFF
        dut.shift_amount.value = i
        dut.ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")
    
    for i in range(17):
        dut.data_in.value = 0x7FFF
        dut.shift_amount.value = i
        dut.ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0xA5A5
        dut.shift_amount.value = i
        dut.ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0xC3C3
        dut.shift_amount.value = i
        dut.ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0x1
        dut.shift_amount.value = i
        dut.ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0x3
        dut.shift_amount.value = i
        dut.ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0x1
        dut.shift_amount.value = i
        dut.ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.data_in.value = 0x3
        dut.shift_amount.value = i
        dut.ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")