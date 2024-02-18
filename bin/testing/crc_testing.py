from crc import Calculator, Configuration
import random

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
        self.dut = dut
        # Gather the settings from the Parameters to verify them
        self.data_width = int(dut.DATA_WIDTH)
        self.chunks = int(dut.CHUNKS)
        self.d_nybbles = self.chunks // 2
        self.crc_width = int(dut.CRC_WIDTH)
        self.nybbles = self.crc_width // 4
        self.crc_poly = int(dut.POLY) & 0xFFFFFFFF
        self.crc_poly_initial = int(dut.POLY_INIT) & 0xFFFFFFFF
        self.reflected_input = int(dut.REFIN)
        self.reflected_output = int(dut.REFOUT)
        self.xor_output = int(dut.XOROUT) & 0xFFFFFFFF
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


    def print_settings(self):
        """Print the settings of the CRCTesting class.

        This method prints out the settings related to data width, chunks, CRC width, polynomial, initial polynomial value, input reflection, output reflection, and XOR output for CRC testing.

        Args:
            None
        Returns:
            None
        """
        print('-------------------------------------------')
        print('Settings:')
        print(f'    DATA_WIDTH: {self.data_width}')
        print(f'    CHUNKS:     {self.chunks}')
        print(f'    CRC_WIDTH:  {self.crc_width}')
        print(f'    POLY:       0x{hex(self.crc_poly)[2:].zfill(self.crc_width // 4)}')
        print(f'    POLY_INIT:  0x{hex(self.crc_poly_initial)[2:].zfill(self.crc_width // 4)}')
        print(f'    REFIN:      {self.reflected_input}')
        print(f'    REFOUT:     {self.reflected_output}')
        print(f'    XOROUT:     0x{hex(self.xor_output)[2:].zfill(self.crc_width // 4)}')
        print('-------------------------------------------')


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
            print(f'Data Generation: {data_bytes=} {ecc=}')
            self.test_data.append((data, ecc))

        # add some random values to the list
        for _ in range(self.rnd_count):
            data = random.randint(0x00, all_ones)
            data_bytes = data.to_bytes(self.chunks, 'little')
            ecc = self.calculator.checksum(data_bytes)
            print(f'Data Generation: {data_bytes=} {ecc=}')
            self.test_data.append((data, ecc))
