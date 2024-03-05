import os
import random
import ConstrainedRandom
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.clock import Clock
import logging

class TBBase():

    def __init__(self, dut):
        self.dut = dut
        self.log_path = os.environ.get('LOG_PATH')
        self.dut_name = os.environ.get('DUT')
        self.log = self.configure_logging(self.dut_name, self.log_path)

    def assert_reset(self):
        pass

    def start_clock(self, clk_name, freq=10, units='ns'):
        clk_signal = getattr(self.dut, clk_name)
        clock = Clock(clk_signal, freq, units=units)
        cocotb.start_soon(clock.start())

    async def wait_clocks(self, clk_name, count=1, delay=100, units='ps'):
        clk_signal = getattr(self.dut, clk_name)
        for _ in range(count):
            await RisingEdge(clk_signal)
            await Timer(delay, units=units)

    async def wait_time(self, delay=100, units='ps'):
        await Timer(delay, units=units)

    @staticmethod
    def configure_logging(dut_name, log_file_path):
        log = logging.getLogger(f'cocotb_log_{dut_name}')
        log.setLevel(logging.DEBUG)
        fh = logging.FileHandler(log_file_path)
        fh.setLevel(logging.DEBUG)
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        fh.setFormatter(formatter)
        log.addHandler(fh)
        return log
