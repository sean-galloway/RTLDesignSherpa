
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_shifter_barrel')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_shifter_barrel.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_fifo(dut):

    dut.i_data.value = 0xFFFF
    dut.i_shift_amount.value = 1
    dut.i_ctrl.value = 0x0
    await Timer(20, units="ns")

    for i in range(17):
        dut.i_data.value = 0xFFFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x1
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xFFFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")
    
    for i in range(17):
        dut.i_data.value = 0x7FFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xA5A5
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xC3C3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x1
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x1
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")

tf = TestFactory(test_fifo)
tf.generate_tests()