from crc import Calculator, Configuration
import os
import subprocess
import random
import logging

class CRCTesting():
    """A class for testing CRC functionality.

    This class is used to test CRC functionality by generating test data based on the provided settings and calculating checksums.

    Args:
        dut: The design under test.
        rnd_count: The number of random values to generate for testing.

    Returns:
        None
    """
    def __init__(self, dut, rnd_count):
        """Initialize the CRCTesting class.

        This method initializes the CRCTesting class by setting up the necessary parameters for testing CRC functionality.

        Args:
            dut: The design under test.
            rnd_count: The number of random values to generate for testing.

        Returns:
            None
        """
        # Gather the settings from the Parameters to verify them
        self.log = logging.getLogger('cocotb_log_dataint_crc')
        self.data_width = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.chunks = self.convert_to_int(dut.CHUNKS.value)
        self.d_nybbles = self.chunks // 2
        self.crc_width = self.convert_to_int(os.environ.get('PARAM_CRC_WIDTH', '0'))
        self.nybbles = self.crc_width // 4
        mask = "F" * self.nybbles
        self.crc_poly = self.convert_to_int(os.environ.get('PARAM_POLY', '0')) & int(mask, 16)
        self.crc_poly_initial = self.convert_to_int(os.environ.get('PARAM_POLY_INIT', '0')) & int(mask, 16)
        self.reflected_input = self.convert_to_int(os.environ.get('PARAM_REFIN', '0'))
        self.reflected_output = self.convert_to_int(os.environ.get('PARAM_REFOUT', '0'))
        self.xor_output = self.convert_to_int(os.environ.get('PARAM_XOROUT', '0')) & int(mask, 16)
        self.rnd_count = rnd_count
        self.test_values = []
        self.test_data = []
        self.cfg = Configuration(
            width=self.crc_width,
            polynomial=self.crc_poly,
            init_value=self.crc_poly_initial,
            final_xor_value=self.xor_output,
            reverse_input=self.reflected_input,
            reverse_output=self.reflected_output
        )
        self.calculator = Calculator(self.cfg)


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
            except ValueError:
                raise ValueError(f"Invalid hexadecimal input: {value}")
        else:
            return int(value)


    def print_settings(self):
        """self.log.info the settings of the CRCTesting class.

        This method self.log.infos out the settings related to data width, chunks, CRC width, polynomial, initial polynomial value, input reflection, output reflection, and XOR output for CRC testing.

        Args:
            None
        Returns:
            None
        """
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    DATA_WIDTH: {self.data_width}')
        self.log.info(f'    CHUNKS:     {self.chunks}')
        self.log.info(f'    CRC_WIDTH:  {self.crc_width}')
        self.log.info(f'    POLY:       0x{hex(self.crc_poly)[2:].zfill(self.crc_width // 4)}')
        self.log.info(f'    POLY_INIT:  0x{hex(self.crc_poly_initial)[2:].zfill(self.crc_width // 4)}')
        self.log.info(f'    REFIN:      {self.reflected_input}')
        self.log.info(f'    REFOUT:     {self.reflected_output}')
        self.log.info(f'    XOROUT:     0x{hex(self.xor_output)[2:].zfill(self.crc_width // 4)}')
        self.log.info('-------------------------------------------')


    def generate_test_data(self):
        """Generate test data for CRC testing.

        This method generates test data for CRC testing based on the configured settings and calculates checksums for the generated data.

        Args:
            None

        Returns:
            None
        """
        walk_1_through_0s = [1 << i for i in range(self.data_width)]
        all_ones = 2**self.data_width - 1
        walk_0_through_1s = [all_ones ^ (1 << i) for i in range(self.data_width)]
        self.test_values = [0, all_ones] + walk_1_through_0s + walk_0_through_1s

        for data in self.test_values:
            data_bytes = data.to_bytes(self.chunks, 'little')
            ecc = self.calculator.checksum(data_bytes)
            # self.log.info(f'Data Generation: {data_bytes=} {ecc=}')
            self.test_data.append((data, ecc))

        # add some random values to the list
        for _ in range(self.rnd_count):
            data = random.randint(0x00, all_ones)
            data_bytes = data.to_bytes(self.chunks, 'little')
            ecc = self.calculator.checksum(data_bytes)
            # self.log.info(f'Data Generation: {data_bytes=} {ecc=}')
            self.test_data.append((data, ecc))
