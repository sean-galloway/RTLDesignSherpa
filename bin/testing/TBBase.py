import os
import random
import ConstrainedRandom
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.clock import Clock
import logging

class TBBase(object):
    """
    Configures logging for the testbench.

    Returns:
        logging.Logger: The configured logger object.
    """

    """
    Convert a value to an integer. If the value is already an integer, return it.
    If it is a hexadecimal string in the format "8'hXX", convert and return as an integer.

    Args:
        value: An integer or a string representing the hex value.

    Returns:
        int: The integer value.

    Raises:
        ValueError: If the input value is not a valid integer or hexadecimal string.
    """

    def __init__(self, dut):
        """
        Initializes the testbench object with the DUT and sets up logging.
        """
        self.dut = dut
        self.log_path = os.environ.get('LOG_PATH')
        self.dut_name = os.environ.get('DUT')
        self.log = self.configure_logging()

    def assert_reset(self):
        pass

    def deassert_reset(self):
        pass

    async def start_clock(self, clk_name, freq=10, units='ns'):
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

    def configure_logging(self):
        """
        Configures logging for the testbench.

        Returns:
            logging.Logger: The configured logger object.
        """
        log = logging.getLogger(f'cocotb_log_{self.dut_name}')
        log.setLevel(logging.DEBUG)
        fh = logging.FileHandler(self.log_path)
        fh.setLevel(logging.DEBUG)
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        fh.setFormatter(formatter)
        log.addHandler(fh)
        return log

    @staticmethod
    def convert_to_int(value):
        """
        Convert a value to an integer. If the value is already an integer, return it.
        If it is a hexadecimal string in the format "8'hXX", convert and return as an integer.

        :param value: An integer or a string representing the hex value.
        :return: The integer value.
        """
        if isinstance(value, int):
            return value
        elif isinstance(value, str) and "'h" in value:
            try:
                # Extract the hexadecimal part after "h"
                _, hex_value = value.split("'h")
                return int(hex_value, 16)
            except ValueError as e:
                raise ValueError(f"Invalid hexadecimal input: {value}") from e
        else:
            return int(value)
