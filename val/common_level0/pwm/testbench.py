
import queue
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb.regression import TestFactory

import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_pwm')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_pwm.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def test_fifo(dut):
    q1 = queue.Queue()

    dut.i_start.value = 0
    dut.i_duty.value = 0
    dut.i_period.value = 0
    dut.i_repeat_count.value = 0

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())

    dut.i_rst_n.value = 0
    await Timer(20, units="ns")
    dut.i_rst_n.value = 1
    await Timer(20, units="ns")

    await Timer(5, units="ns")

    dut.i_start.value = 1
    dut.i_duty.value = 7
    dut.i_period.value = 17
    dut.i_repeat_count.value = 5

    await Timer(20, units="ns")

    await Timer(2500, units="ns")

tf = TestFactory(test_fifo)
tf.generate_tests()