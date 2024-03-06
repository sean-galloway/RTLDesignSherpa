import os
import random
import ConstrainedRandom
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.clock import Clock
import logging

class TBBase(object):
    """
    Initializes the testbench object with the DUT and sets up logging.

    Configures logging for the testbench.

    Starts a clock signal for the specified DUT.

    Waits for a specified number of rising edges on the clock signal.

    Waits for a specified amount of time.

    Convert a value to an integer. If the value is already an integer, return it.
    If it is a hexadecimal string in the format "8'hXX", convert and return as an integer.

    Generates a number with alternating '1's up to position N.

    Inverts the bits of a number up to position N.
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
        """
        Starts a clock signal for the specified DUT.

        Args:
            clk_name (str): The name of the clock signal.
            freq (int, optional): The frequency of the clock signal. Defaults to 10.
            units (str, optional): The units of the frequency. Defaults to 'ns'.

        Returns:
            None

        Examples:
            await start_clock('clk', freq=20, units='ps')
        """
        clk_signal = getattr(self.dut, clk_name)
        clock = Clock(clk_signal, freq, units=units)
        cocotb.start_soon(clock.start())

    async def wait_clocks(self, clk_name, count=1, delay=100, units='ps'):
        """
        Waits for a specified number of rising edges on the clock signal.

        Args:
            clk_name (str): The name of the clock signal.
            count (int, optional): The number of rising edges to wait for. Defaults to 1.
            delay (int, optional): The delay between each rising edge. Defaults to 100.
            units (str, optional): The units of the delay. Defaults to 'ps'.

        Returns:
            None
        """
        clk_signal = getattr(self.dut, clk_name)
        for _ in range(count):
            await RisingEdge(clk_signal)
            await Timer(delay, units=units)

    async def wait_time(self, delay=100, units='ps'):
        """
        Waits for a specified amount of time.

        Args:
            delay (int, optional): The duration to wait. Defaults to 100.
            units (str, optional): The units of the delay. Defaults to 'ps'.

        Returns:
            None
        """
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


    @staticmethod
    def generate_alternating_ones(N):
        """
        Generates a number with alternating '1's up to position N.

        Args:
            N (int): The position up to which to generate the number.

        Returns:
            int: The generated number with alternating '1's.
        """
        num = 0
        for i in range(N):
            if i % 2 == 0:  # Check if the position is even
                num |= 1 << i  # Set the bit at position 'i'
        return num

    @staticmethod
    def invert_bits(num, N):
        """
        Inverts the bits of a number up to position N.

        Args:
            num (int): The number to invert the bits of.
            N (int): The position up to which to invert the bits.

        Returns:
            int: The number with inverted bits up to position N.
        """
        # Create a mask of N 1's
        mask = (1 << N) - 1
        # XOR the number with the mask to invert its bits
        return num ^ mask
