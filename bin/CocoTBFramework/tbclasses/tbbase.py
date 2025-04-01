"""Base Testbanch Class handling the basics of cocotb"""
import os
import logging
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
from cocotb.utils import get_sim_time


class TBBase:
    """
    Base class for testbenches with improved logging functionality.
    """
    default_log_level = logging.DEBUG  # Class attribute for default log level

    def __init__(self, dut):
        """
        Initializes the testbench object with the DUT and sets up logging.
        """
        self.dut = dut

        # Get log path from environment or use a default if not specified
        self.log_path = os.environ.get('LOG_PATH')
        if not self.log_path:
            # Create a default log path if none is provided
            log_dir = os.path.join(os.getcwd(), 'logs')
            os.makedirs(log_dir, exist_ok=True)
            self.log_path = os.path.join(log_dir, 'default_cocotb.log')
            print(f"WARNING: LOG_PATH not specified in environment. Using default: {self.log_path}")

        self.dut_name = os.environ.get('DUT', 'unknown_dut')
        self.log_count = 0

        # Configure logging immediately
        self.log = self.configure_logging(level=TBBase.default_log_level)
        msg = f"Initialized testbench for {self.dut_name}"
        self.log.info(msg)
        msg = f"Log file: {self.log_path}"
        self.log.info(msg)

    @staticmethod
    def convert_param_type(value, default):
        """Converts environment variable values to the correct type based on the default value."""
        if isinstance(default, bool):  # Convert string to boolean
            if isinstance(value, bool):
                return value
            elif isinstance(value, str):
                return value.lower() in ["true", "1", "yes"]
            else:
                return bool(value)
        elif isinstance(default, int):  # Convert string to integer
            try:
                return int(value)
            except (ValueError, TypeError):
                return default
        elif isinstance(default, float):  # Convert string to float
            try:
                return float(value)
            except (ValueError, TypeError):
                return default
        return value  # Return as string if no conversion needed

    def assert_reset(self):
        """Base method to assert reset"""
        self.log.info("Base assert_reset called - should be overridden")

    def deassert_reset(self):
        """Base method to deassert reset"""
        self.log.info("Base deassert_reset called - should be overridden")

    async def start_clock(self, clk_name, freq=10, units='ns'):
        """
        Starts a clock signal for the specified DUT.
        """
        msg = f"Starting clock {clk_name} with frequency {freq} {units}"
        self.log.debug(msg)
        clk_signal = getattr(self.dut, clk_name)
        cocotb.start_soon(Clock(clk_signal, freq, units=units).start())
        await Timer(100, units='ps')
        msg = f"Clock {clk_name} started"
        self.log.debug(msg)

    async def wait_clocks(self, clk_name, count=1, delay=100, units='ps'):
        """
        Waits for a specified number of rising edges on the clock signal.
        """
        clk_signal = getattr(self.dut, clk_name)
        for _ in range(count):
            await RisingEdge(clk_signal)
            await Timer(delay, units=units)

    async def wait_falling_clocks(self, clk_name, count=1, delay=100, units='ps'):
        """
        Waits for a specified number of falling edges on the clock signal.
        """
        clk_signal = getattr(self.dut, clk_name)
        for _ in range(count):
            await FallingEdge(clk_signal)
            await Timer(delay, units=units)

    async def wait_time(self, delay=100, units='ps'):
        """
        Waits for a specified amount of time.
        """
        await Timer(delay, units=units)

    def configure_logging(self, level=logging.DEBUG):
        # sourcery skip: extract-duplicate-method, extract-method
        """
        Configures logging for the testbench with robust error handling.
        """
        log_name = f'cocotb_log_{self.dut_name}'
        log = logging.getLogger(log_name)

        # Remove any existing handlers to avoid duplicates
        for handler in log.handlers[:]:
            log.removeHandler(handler)

        # Set the log level
        log.setLevel(level)

        try:
            if log_dir := os.path.dirname(self.log_path):
                os.makedirs(log_dir, exist_ok=True)

            # Create file handler
            fh = logging.FileHandler(self.log_path, mode='a')  # Append mode
            fh.setLevel(logging.DEBUG)

            # Create formatter
            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            fh.setFormatter(formatter)

            # Add handler to logger
            log.addHandler(fh)

            # Enable propagation to root logger for console output
            log.propagate = True

            # Add a console handler as well
            console = logging.StreamHandler()
            console.setLevel(logging.INFO)
            console.setFormatter(formatter)
            log.addHandler(console)

            self.log_count += 1

        except Exception as e:
            # Fall back to print if logging setup fails
            print(f"ERROR setting up logging to {self.log_path}: {str(e)}")

            # Create a basic console logger as fallback
            console = logging.StreamHandler()
            console.setLevel(logging.DEBUG)
            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            console.setFormatter(formatter)
            log.addHandler(console)

        return log

    def log_flush(self):
        """Force flush all log handlers"""
        for handler in self.log.handlers:
            handler.flush()

    @staticmethod
    def get_time_ns_str():
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

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
    def hex_format(value, max_value):
        """
        Format an integer value as a hexadecimal string with leading zeros.

        Args:
            value (int): The integer value to format.
            max_value (int): The maximum value to determine the width of the hexadecimal string.

        Returns:
            str: The formatted hexadecimal string.

        Examples:
            hex_format(10, 255) returns '0A'
        """
        # Calculate the number of hexadecimal digits needed
        hex_width = (max_value.bit_length() + 3) // 4  # Round up division by 4
        return format(int(value), f'0{hex_width}X')

    @staticmethod
    def generate_alternating_ones(n):
        """
        Generates a number with alternating '1's up to position N.

        Args:
            N (int): The position up to which to generate the number.

        Returns:
            int: The generated number with alternating '1's.
        """
        num = 0
        for i in range(n):
            if i % 2 == 0:  # Check if the position is even
                num |= 1 << i  # Set the bit at position 'i'
        return num

    @staticmethod
    def invert_bits(num, n):
        """
        Inverts the bits of a number up to position N.

        Args:
            num (int): The number to invert the bits of.
            N (int): The position up to which to invert the bits.

        Returns:
            int: The number with inverted bits up to position N.
        """
        # Create a mask of N 1's
        mask = (1 << n) - 1
        # XOR the number with the mask to invert its bits
        return num ^ mask

    @staticmethod
    def convert_to_bytearray(data):
        """
        Convert the input data to a bytearray if it's not already one.

        Parameters:
        data (Any): The data to convert to a bytearray.

        Returns:
        bytearray: The converted bytearray.
        """
        if isinstance(data, bytearray):
            return data
        elif isinstance(data, (bytes, list)):
            return bytearray(data)
        else:
            raise TypeError("Input data must be a bytearray, bytes, or list of integers")


    @staticmethod
    def bytearray_to_hex_strings(bytearrays):
        """
        Convert a list of bytearray values into hex strings.

        Parameters:
        bytearrays (list of bytearray): The list of bytearray values to convert.

        Returns:
        list of str: The list of hex strings.
        """
        return [TBBase.bytearray_to_hex(ba) for ba in bytearrays]

    @staticmethod
    def bytearray_to_hex(bytearray_value):
        """
        Convert a single bytearray to a hex string.

        Parameters:
        bytearray_value (bytearray): The bytearray to convert.

        Returns:
        str: The hex string.
        """
        return ''.join(f'{byte:02X}, ' for byte in bytearray_value)

    @staticmethod
    def format_dec(decimal, width):
        """format a decimal to a string prepending 0's"""
        return f"{decimal:0{width}d}"
