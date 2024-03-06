from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from crc import Calculator, Configuration
import os
import random

class CRCTB(TBBase):
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
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
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


    async def clear_interface(self):
        self.dut.i_load_crc_start.value = 0
        self.dut.i_load_from_cascade.value = 0
        self.dut.i_cascade_sel.value = 0
        self.dut.i_data.value = 0


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    @staticmethod
    def find_highest_byte_enable(data_width):
        # Calculate the number of bytes - 1 to find the highest byte position
        highest_byte_position = (data_width // 8) - 1
        return 1 << highest_byte_position


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


    async def main_loop(self):
        for data, expected_crc in self.test_data:
            # Test 1: Load initial CRC value and check
            self.dut.i_load_crc_start.value = 1
            await self.wait_clocks('i_clk',1)
            self.dut.i_load_crc_start.value = 0
            assert self.dut.o_crc.value == self.crc_poly_initial, "CRC initial value incorrect"

            # Test 2: Load data and validate CRC calculation
            # This step depends on having a known input-output pair for validation
            self.dut.i_data.value = data
            self.dut.i_load_from_cascade.value = 1
            self.dut.i_cascade_sel.value = self.find_highest_byte_enable(self.data_width)
            await self.wait_clocks('i_clk',1)
            self.dut.i_data.value = 0
            self.dut.i_load_from_cascade.value = 0
            self.dut.i_cascade_sel.value = 0
            await self.wait_clocks('i_clk',1)
            # Verify the CRC output matches the expected value
            # Note: You may need to adjust this depending on when the CRC output is valid
            found_crc = self.dut.o_crc.value
            self.log.info(f'test_data=0x{hex(data)[2:].zfill(self.d_nybbles)}   expected_crc=0x{hex(expected_crc)[2:].zfill(self.nybbles)}  actual_crc=0x{hex(found_crc)[2:].zfill(self.nybbles)}')
            assert hex(found_crc) == hex(expected_crc), f"Unexpected CRC result: data=0x{hex(data)[2:].zfill(self.d_nybbles)}  expected {hex(expected_crc)} --> found {hex(found_crc)}"


crc_parameters = [
('CRC-08', 8, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
('CRC-08_CDMA2000', 8, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
('CRC-08_DARC', 8, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
('CRC-08_DVB-S2', 8, '8', "8'hD5", "8'h00", '0', '0', "8'h00"),
('CRC-08_EBU', 8, '8', "8'h1D", "8'hFF", '1', '1', "8'h00"),
('CRC-08_I-CODE', 8, '8', "8'h1D", "8'hFD", '0', '0', "8'h00"),
('CRC-08_ITU', 8, '8', "8'h07", "8'h00", '0', '0', "8'h55"),
('CRC-08_MAXIM', 8, '8', "8'h31", "8'h00", '1', '1', "8'h00"),
('CRC-08_ROHC', 8, '8', "8'h07", "8'hFF", '1', '1', "8'h00"),
('CRC-08_WCDMA', 8, '8', "8'h9B", "8'h00", '1', '1', "8'h00"),
('CRC-16_ARC', 8, '16', "16'h8005", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_AUG-CCITT', 8, '16', "16'h1021", "16'h1D0F", '0', '0', "16'h0000"),
('CRC-16_BUYPASS', 8, '16', "16'h8005", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_CCITT-FALSE', 8, '16', "16'h1021", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_CDMA2000', 8, '16', "16'hC867", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_DDS-110', 8, '16', "16'h8005", "16'h800D", '0', '0', "16'h0000"),
('CRC-16_DECT-R', 8, '16', "16'h0589", "16'h0000", '0', '0', "16'h0001"),
('CRC-16_DECT-X', 8, '16', "16'h0589", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_DNP', 8, '16', "16'h3D65", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_EN-13757', 8, '16', "16'h3D65", "16'h0000", '0', '0', "16'hFFFF"),
('CRC-16_GENIBUS', 8, '16', "16'h1021", "16'hFFFF", '0', '0', "16'hFFFF"),
('CRC-16_KERMIT', 8, '16', "16'h1021", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_MAXIM', 8, '16', "16'h8005", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_MCRF4XX', 8, '16', "16'h1021", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_MODBUS', 8, '16', "16'h8005", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_RIELLO', 8, '16', "16'h1021", "16'hB2AA", '1', '1', "16'h0000"),
('CRC-16_T10-DIF', 8, '16', "16'h8BB7", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TELEDISK', 8, '16', "16'hA097", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TMS37157', 8, '16', "16'h1021", "16'h89EC", '1', '1', "16'h0000"),
('CRC-16_USB', 8, '16', "16'h8005", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_X-25', 8, '16', "16'h1021", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_XMODEM', 8, '16', "16'h1021", "16'h0000", '0', '0', "16'h0000"),
('CRC-16A', 8, '16', "16'h1021", "16'hC6C6", '1', '1', "16'h0000"),
('CRC-32', 8, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32_BZIP2', 8, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'hFFFFFFFF"),
('CRC-32_JAMCRC', 8, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'h00000000"),
('CRC-32_MPEG-2', 8, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'h00000000"),
('CRC-32_POSIX', 8, '32', "32'h04C11DB7", "32'h00000000", '0', '0', "32'hFFFFFFFF"),
('CRC-32_SATA', 8, '32', "32'h04C11DB7", "32'h52325032", '0', '0', "32'h00000000"),
('CRC-32_XFER', 8, '32', "32'h000000AF", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-32C', 8, '32', "32'h1EDC6F41", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32D', 8, '32', "32'hA833982B", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32Q', 8, '32', "32'h814141AB", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-40_GSM', 8, '40', "40'h4820009", "40'h0000000000", '0', '0', "40'hFFFFFFFFFF"),
('CRC-64_ECMA-182', 8, '64', "64'h42F0E1EBA9EA3693", "64'h0000000000000000", '0', '0', "64'h0000000000000000"),
('CRC-64_GO-ISO', 8, '64', "64'h000000000000001B", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_MS', 8, '64', "64'h259C84CBA6426349", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'h0000000000000000"),
('CRC-64_REDIS', 8, '64', "64'hAD93D23594C935A9", "64'h0000000000000000", '1', '1', "64'h0000000000000000"),
('CRC-64_WE', 8, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '0', '0', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_XZ', 8, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-08', 16, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
('CRC-08_CDMA2000', 16, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
('CRC-08_DARC', 16, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
('CRC-08_DVB-S2', 16, '8', "8'hD5", "8'h00", '0', '0', "8'h00"),
('CRC-08_EBU', 16, '8', "8'h1D", "8'hFF", '1', '1', "8'h00"),
('CRC-08_I-CODE', 16, '8', "8'h1D", "8'hFD", '0', '0', "8'h00"),
('CRC-08_ITU', 16, '8', "8'h07", "8'h00", '0', '0', "8'h55"),
('CRC-08_MAXIM', 16, '8', "8'h31", "8'h00", '1', '1', "8'h00"),
('CRC-08_ROHC', 16, '8', "8'h07", "8'hFF", '1', '1', "8'h00"),
('CRC-08_WCDMA', 16, '8', "8'h9B", "8'h00", '1', '1', "8'h00"),
('CRC-16_ARC', 16, '16', "16'h8005", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_AUG-CCITT', 16, '16', "16'h1021", "16'h1D0F", '0', '0', "16'h0000"),
('CRC-16_BUYPASS', 16, '16', "16'h8005", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_CCITT-FALSE', 16, '16', "16'h1021", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_CDMA2000', 16, '16', "16'hC867", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_DDS-110', 16, '16', "16'h8005", "16'h800D", '0', '0', "16'h0000"),
('CRC-16_DECT-R', 16, '16', "16'h0589", "16'h0000", '0', '0', "16'h0001"),
('CRC-16_DECT-X', 16, '16', "16'h0589", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_DNP', 16, '16', "16'h3D65", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_EN-13757', 16, '16', "16'h3D65", "16'h0000", '0', '0', "16'hFFFF"),
('CRC-16_GENIBUS', 16, '16', "16'h1021", "16'hFFFF", '0', '0', "16'hFFFF"),
('CRC-16_KERMIT', 16, '16', "16'h1021", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_MAXIM', 16, '16', "16'h8005", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_MCRF4XX', 16, '16', "16'h1021", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_MODBUS', 16, '16', "16'h8005", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_RIELLO', 16, '16', "16'h1021", "16'hB2AA", '1', '1', "16'h0000"),
('CRC-16_T10-DIF', 16, '16', "16'h8BB7", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TELEDISK', 16, '16', "16'hA097", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TMS37157', 16, '16', "16'h1021", "16'h89EC", '1', '1', "16'h0000"),
('CRC-16_USB', 16, '16', "16'h8005", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_X-25', 16, '16', "16'h1021", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_XMODEM', 16, '16', "16'h1021", "16'h0000", '0', '0', "16'h0000"),
('CRC-16A', 16, '16', "16'h1021", "16'hC6C6", '1', '1', "16'h0000"),
('CRC-32', 16, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32_BZIP2', 16, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'hFFFFFFFF"),
('CRC-32_JAMCRC', 16, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'h00000000"),
('CRC-32_MPEG-2', 16, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'h00000000"),
('CRC-32_POSIX', 16, '32', "32'h04C11DB7", "32'h00000000", '0', '0', "32'hFFFFFFFF"),
('CRC-32_SATA', 16, '32', "32'h04C11DB7", "32'h52325032", '0', '0', "32'h00000000"),
('CRC-32_XFER', 16, '32', "32'h000000AF", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-32C', 16, '32', "32'h1EDC6F41", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32D', 16, '32', "32'hA833982B", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32Q', 16, '32', "32'h814141AB", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-40_GSM', 16, '40', "40'h4820009", "40'h0000000000", '0', '0', "40'hFFFFFFFFFF"),
('CRC-64_ECMA-182', 16, '64', "64'h42F0E1EBA9EA3693", "64'h0000000000000000", '0', '0', "64'h0000000000000000"),
('CRC-64_GO-ISO', 16, '64', "64'h000000000000001B", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_MS', 16, '64', "64'h259C84CBA6426349", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'h0000000000000000"),
('CRC-64_REDIS', 16, '64', "64'hAD93D23594C935A9", "64'h0000000000000000", '1', '1', "64'h0000000000000000"),
('CRC-64_WE', 16, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '0', '0', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_XZ', 16, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-08', 32, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
('CRC-08_CDMA2000', 32, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
('CRC-08_DARC', 32, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
('CRC-08_DVB-S2', 32, '8', "8'hD5", "8'h00", '0', '0', "8'h00"),
('CRC-08_EBU', 32, '8', "8'h1D", "8'hFF", '1', '1', "8'h00"),
('CRC-08_I-CODE', 32, '8', "8'h1D", "8'hFD", '0', '0', "8'h00"),
('CRC-08_ITU', 32, '8', "8'h07", "8'h00", '0', '0', "8'h55"),
('CRC-08_MAXIM', 32, '8', "8'h31", "8'h00", '1', '1', "8'h00"),
('CRC-08_ROHC', 32, '8', "8'h07", "8'hFF", '1', '1', "8'h00"),
('CRC-08_WCDMA', 32, '8', "8'h9B", "8'h00", '1', '1', "8'h00"),
('CRC-16_ARC', 32, '16', "16'h8005", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_AUG-CCITT', 32, '16', "16'h1021", "16'h1D0F", '0', '0', "16'h0000"),
('CRC-16_BUYPASS', 32, '16', "16'h8005", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_CCITT-FALSE', 32, '16', "16'h1021", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_CDMA2000', 32, '16', "16'hC867", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_DDS-110', 32, '16', "16'h8005", "16'h800D", '0', '0', "16'h0000"),
('CRC-16_DECT-R', 32, '16', "16'h0589", "16'h0000", '0', '0', "16'h0001"),
('CRC-16_DECT-X', 32, '16', "16'h0589", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_DNP', 32, '16', "16'h3D65", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_EN-13757', 32, '16', "16'h3D65", "16'h0000", '0', '0', "16'hFFFF"),
('CRC-16_GENIBUS', 32, '16', "16'h1021", "16'hFFFF", '0', '0', "16'hFFFF"),
('CRC-16_KERMIT', 32, '16', "16'h1021", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_MAXIM', 32, '16', "16'h8005", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_MCRF4XX', 32, '16', "16'h1021", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_MODBUS', 32, '16', "16'h8005", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_RIELLO', 32, '16', "16'h1021", "16'hB2AA", '1', '1', "16'h0000"),
('CRC-16_T10-DIF', 32, '16', "16'h8BB7", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TELEDISK', 32, '16', "16'hA097", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TMS37157', 32, '16', "16'h1021", "16'h89EC", '1', '1', "16'h0000"),
('CRC-16_USB', 32, '16', "16'h8005", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_X-25', 32, '16', "16'h1021", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_XMODEM', 32, '16', "16'h1021", "16'h0000", '0', '0', "16'h0000"),
('CRC-16A', 32, '16', "16'h1021", "16'hC6C6", '1', '1', "16'h0000"),
('CRC-32', 32, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32_BZIP2', 32, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'hFFFFFFFF"),
('CRC-32_JAMCRC', 32, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'h00000000"),
('CRC-32_MPEG-2', 32, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'h00000000"),
('CRC-32_POSIX', 32, '32', "32'h04C11DB7", "32'h00000000", '0', '0', "32'hFFFFFFFF"),
('CRC-32_SATA', 32, '32', "32'h04C11DB7", "32'h52325032", '0', '0', "32'h00000000"),
('CRC-32_XFER', 32, '32', "32'h000000AF", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-32C', 32, '32', "32'h1EDC6F41", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32D', 32, '32', "32'hA833982B", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32Q', 32, '32', "32'h814141AB", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-40_GSM', 32, '40', "40'h4820009", "40'h0000000000", '0', '0', "40'hFFFFFFFFFF"),
('CRC-64_ECMA-182', 32, '64', "64'h42F0E1EBA9EA3693", "64'h0000000000000000", '0', '0', "64'h0000000000000000"),
('CRC-64_GO-ISO', 32, '64', "64'h000000000000001B", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_MS', 32, '64', "64'h259C84CBA6426349", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'h0000000000000000"),
('CRC-64_REDIS', 32, '64', "64'hAD93D23594C935A9", "64'h0000000000000000", '1', '1', "64'h0000000000000000"),
('CRC-64_WE', 32, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '0', '0', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_XZ', 32, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-08', 40, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
('CRC-08_CDMA2000', 40, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
('CRC-08_DARC', 40, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
('CRC-08_DVB-S2', 40, '8', "8'hD5", "8'h00", '0', '0', "8'h00"),
('CRC-08_EBU', 40, '8', "8'h1D", "8'hFF", '1', '1', "8'h00"),
('CRC-08_I-CODE', 40, '8', "8'h1D", "8'hFD", '0', '0', "8'h00"),
('CRC-08_ITU', 40, '8', "8'h07", "8'h00", '0', '0', "8'h55"),
('CRC-08_MAXIM', 40, '8', "8'h31", "8'h00", '1', '1', "8'h00"),
('CRC-08_ROHC', 40, '8', "8'h07", "8'hFF", '1', '1', "8'h00"),
('CRC-08_WCDMA', 40, '8', "8'h9B", "8'h00", '1', '1', "8'h00"),
('CRC-16_ARC', 40, '16', "16'h8005", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_AUG-CCITT', 40, '16', "16'h1021", "16'h1D0F", '0', '0', "16'h0000"),
('CRC-16_BUYPASS', 40, '16', "16'h8005", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_CCITT-FALSE', 40, '16', "16'h1021", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_CDMA2000', 40, '16', "16'hC867", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_DDS-110', 40, '16', "16'h8005", "16'h800D", '0', '0', "16'h0000"),
('CRC-16_DECT-R', 40, '16', "16'h0589", "16'h0000", '0', '0', "16'h0001"),
('CRC-16_DECT-X', 40, '16', "16'h0589", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_DNP', 40, '16', "16'h3D65", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_EN-13757', 40, '16', "16'h3D65", "16'h0000", '0', '0', "16'hFFFF"),
('CRC-16_GENIBUS', 40, '16', "16'h1021", "16'hFFFF", '0', '0', "16'hFFFF"),
('CRC-16_KERMIT', 40, '16', "16'h1021", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_MAXIM', 40, '16', "16'h8005", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_MCRF4XX', 40, '16', "16'h1021", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_MODBUS', 40, '16', "16'h8005", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_RIELLO', 40, '16', "16'h1021", "16'hB2AA", '1', '1', "16'h0000"),
('CRC-16_T10-DIF', 40, '16', "16'h8BB7", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TELEDISK', 40, '16', "16'hA097", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TMS37157', 40, '16', "16'h1021", "16'h89EC", '1', '1', "16'h0000"),
('CRC-16_USB', 40, '16', "16'h8005", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_X-25', 40, '16', "16'h1021", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_XMODEM', 40, '16', "16'h1021", "16'h0000", '0', '0', "16'h0000"),
('CRC-16A', 40, '16', "16'h1021", "16'hC6C6", '1', '1', "16'h0000"),
('CRC-32', 40, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32_BZIP2', 40, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'hFFFFFFFF"),
('CRC-32_JAMCRC', 40, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'h00000000"),
('CRC-32_MPEG-2', 40, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'h00000000"),
('CRC-32_POSIX', 40, '32', "32'h04C11DB7", "32'h00000000", '0', '0', "32'hFFFFFFFF"),
('CRC-32_SATA', 40, '32', "32'h04C11DB7", "32'h52325032", '0', '0', "32'h00000000"),
('CRC-32_XFER', 40, '32', "32'h000000AF", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-32C', 40, '32', "32'h1EDC6F41", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32D', 40, '32', "32'hA833982B", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32Q', 40, '32', "32'h814141AB", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-40_GSM', 40, '40', "40'h4820009", "40'h0000000000", '0', '0', "40'hFFFFFFFFFF"),
('CRC-64_ECMA-182', 40, '64', "64'h42F0E1EBA9EA3693", "64'h0000000000000000", '0', '0', "64'h0000000000000000"),
('CRC-64_GO-ISO', 40, '64', "64'h000000000000001B", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_MS', 40, '64', "64'h259C84CBA6426349", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'h0000000000000000"),
('CRC-64_REDIS', 40, '64', "64'hAD93D23594C935A9", "64'h0000000000000000", '1', '1', "64'h0000000000000000"),
('CRC-64_WE', 40, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '0', '0', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_XZ', 40, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-08', 64, '8', "8'h07", "8'h00", '0', '0', "8'h00"),
('CRC-08_CDMA2000', 64, '8', "8'h9B", "8'hFF", '0', '0', "8'h00"),
('CRC-08_DARC', 64, '8', "8'h39", "8'h00", '1', '1', "8'h00"),
('CRC-08_DVB-S2', 64, '8', "8'hD5", "8'h00", '0', '0', "8'h00"),
('CRC-08_EBU', 64, '8', "8'h1D", "8'hFF", '1', '1', "8'h00"),
('CRC-08_I-CODE', 64, '8', "8'h1D", "8'hFD", '0', '0', "8'h00"),
('CRC-08_ITU', 64, '8', "8'h07", "8'h00", '0', '0', "8'h55"),
('CRC-08_MAXIM', 64, '8', "8'h31", "8'h00", '1', '1', "8'h00"),
('CRC-08_ROHC', 64, '8', "8'h07", "8'hFF", '1', '1', "8'h00"),
('CRC-08_WCDMA', 64, '8', "8'h9B", "8'h00", '1', '1', "8'h00"),
('CRC-16_ARC', 64, '16', "16'h8005", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_AUG-CCITT', 64, '16', "16'h1021", "16'h1D0F", '0', '0', "16'h0000"),
('CRC-16_BUYPASS', 64, '16', "16'h8005", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_CCITT-FALSE', 64, '16', "16'h1021", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_CDMA2000', 64, '16', "16'hC867", "16'hFFFF", '0', '0', "16'h0000"),
('CRC-16_DDS-110', 64, '16', "16'h8005", "16'h800D", '0', '0', "16'h0000"),
('CRC-16_DECT-R', 64, '16', "16'h0589", "16'h0000", '0', '0', "16'h0001"),
('CRC-16_DECT-X', 64, '16', "16'h0589", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_DNP', 64, '16', "16'h3D65", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_EN-13757', 64, '16', "16'h3D65", "16'h0000", '0', '0', "16'hFFFF"),
('CRC-16_GENIBUS', 64, '16', "16'h1021", "16'hFFFF", '0', '0', "16'hFFFF"),
('CRC-16_KERMIT', 64, '16', "16'h1021", "16'h0000", '1', '1', "16'h0000"),
('CRC-16_MAXIM', 64, '16', "16'h8005", "16'h0000", '1', '1', "16'hFFFF"),
('CRC-16_MCRF4XX', 64, '16', "16'h1021", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_MODBUS', 64, '16', "16'h8005", "16'hFFFF", '1', '1', "16'h0000"),
('CRC-16_RIELLO', 64, '16', "16'h1021", "16'hB2AA", '1', '1', "16'h0000"),
('CRC-16_T10-DIF', 64, '16', "16'h8BB7", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TELEDISK', 64, '16', "16'hA097", "16'h0000", '0', '0', "16'h0000"),
('CRC-16_TMS37157', 64, '16', "16'h1021", "16'h89EC", '1', '1', "16'h0000"),
('CRC-16_USB', 64, '16', "16'h8005", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_X-25', 64, '16', "16'h1021", "16'hFFFF", '1', '1', "16'hFFFF"),
('CRC-16_XMODEM', 64, '16', "16'h1021", "16'h0000", '0', '0', "16'h0000"),
('CRC-16A', 64, '16', "16'h1021", "16'hC6C6", '1', '1', "16'h0000"),
('CRC-32', 64, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32_BZIP2', 64, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'hFFFFFFFF"),
('CRC-32_JAMCRC', 64, '32', "32'h04C11DB7", "32'hFFFFFFFF", '1', '1', "32'h00000000"),
('CRC-32_MPEG-2', 64, '32', "32'h04C11DB7", "32'hFFFFFFFF", '0', '0', "32'h00000000"),
('CRC-32_POSIX', 64, '32', "32'h04C11DB7", "32'h00000000", '0', '0', "32'hFFFFFFFF"),
('CRC-32_SATA', 64, '32', "32'h04C11DB7", "32'h52325032", '0', '0', "32'h00000000"),
('CRC-32_XFER', 64, '32', "32'h000000AF", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-32C', 64, '32', "32'h1EDC6F41", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32D', 64, '32', "32'hA833982B", "32'hFFFFFFFF", '1', '1', "32'hFFFFFFFF"),
('CRC-32Q', 64, '32', "32'h814141AB", "32'h00000000", '0', '0', "32'h00000000"),
('CRC-40_GSM', 64, '40', "40'h4820009", "40'h0000000000", '0', '0', "40'hFFFFFFFFFF"),
('CRC-64_ECMA-182', 64, '64', "64'h42F0E1EBA9EA3693", "64'h0000000000000000", '0', '0', "64'h0000000000000000"),
('CRC-64_GO-ISO', 64, '64', "64'h000000000000001B", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_MS', 64, '64', "64'h259C84CBA6426349", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'h0000000000000000"),
('CRC-64_REDIS', 64, '64', "64'hAD93D23594C935A9", "64'h0000000000000000", '1', '1', "64'h0000000000000000"),
('CRC-64_WE', 64, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '0', '0', "64'hFFFFFFFFFFFFFFFF"),
('CRC-64_XZ', 64, '64', "64'h42F0E1EBA9EA3693", "64'hFFFFFFFFFFFFFFFF", '1', '1', "64'hFFFFFFFFFFFFFFFF")
]