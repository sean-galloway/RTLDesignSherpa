from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from crc import Calculator, Configuration
import os
import random

class CamTB(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.max_val = (2**self.N)-1


    async def main_loop(self):
        self.log.info("Main Test")
        tag_list = [random.randint(0x00, self.max_val) for _ in range(self.DEPTH)]
        self.log.info(f'{tag_list=}')
        for tag in tag_list:
            await self.mark_one_valid(tag)
        self.check_not_empty()
        self.check_full()
        random.shuffle(tag_list)
        tag = tag_list.pop()
        await self.mark_one_invalid(tag)
        self.check_not_empty()
        self.check_not_full()
        await self.mark_one_valid(tag)
        self.check_full()
        tag_list.append(tag)
        for tag in tag_list:
            await self.mark_one_invalid(tag)
        self.clear_interface()
        await self.wait_clocks('i_clk', 1)
        self.check_empty()
        self.check_not_full()


    async def clear_interface(self):
        self.dut.i_tag_in.value = 0
        self.dut.i_mark_valid.value = 0
        self.dut.i_mark_invalid.value = 0


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    def check_empty(self):
        assert self.dut.ow_tags_empty == 1, "CAM should be empty, but is not."


    def check_not_empty(self):
        assert self.dut.ow_tags_empty == 0, "CAM should not be empty, but is."


    def check_full(self):
        assert self.dut.ow_tags_full == 1, "CAM should be full, but is not."


    def check_not_full(self):
        assert self.dut.ow_tags_full == 0, "CAM should not be full, but is."


    async def mark_one_valid(self, tag_value):
        self.log.info(f"Marking Valid {hex(tag_value)}")
        self.dut.i_tag_in.value = tag_value
        self.dut.i_mark_valid.value = 1
        await self.wait_clocks('i_clk', 1)
        self.dut.i_tag_in.value = 0
        self.dut.i_mark_valid.value = 0


    async def mark_one_invalid(self, tag_value):
        self.log.info(f"Marking Valid {hex(tag_value)}")
        self.dut.i_tag_in.value = tag_value
        self.dut.i_mark_invalid.value = 1
        await self.wait_clocks('i_clk', 1)
        self.dut.i_tag_in.value = 0
        self.dut.i_mark_invalid.value = 0


    async def check_tag(self, tag_value, check):
        self.dut.i_tag_in.value = tag_value
        await self.wait_clocks('i_clk', 1)
        found = self.dut.ow_tag_status
        if check == 1:
            msg = f"Expected tag({hex(tag_value)}) to be True"
        else:
            msg = f"Expected tag({hex(tag_value)}) to be False"
        assert found == check, msg


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
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    DEPTH: {self.DEPTH}')
        self.log.info('-------------------------------------------')
