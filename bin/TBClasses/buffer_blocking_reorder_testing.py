from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.utils import get_sim_time
from crc import Calculator, Configuration
import os
import random
from ConstrainedRandom import ConstrainedRandom


class BufferBlockingReorderTB(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.TAG_WIDTH = self.convert_to_int(os.environ.get('PARAM_TAG_WIDTH', '0'))
        self.max_tag = (2**self.TAG_WIDTH)-1
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '0'))
        self.max_addr = (2**self.ADDR_WIDTH)-1
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.max_data = (2**self.DATA_WIDTH)-1
        self.COUNT_WIDTH = self.convert_to_int(os.environ.get('PARAM_COUNT_WIDTH', '0'))
        self.max_count = (2**self.COUNT_WIDTH)-1
        self.TIMER_WIDTH = self.convert_to_int(os.environ.get('PARAM_TIMER_WIDTH', '0'))
        self.max_timer = (2**self.TIMER_WIDTH)-1
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.percent_05 = int(self.max_tag*.05)
        self.percent_25 = int(self.max_tag*.55)
        self.percent_65 = int(self.max_tag*.65)
        self.tag_constraints = [(0, self.percent_05), 
                            (self.percent_05+1, self.percent_25),
                            (self.percent_25+1, self.percent_65),
                            (self.percent_65+1, self.max_tag-1)]
        self.tag_weights = [10, 2, 2, 1]
        self.ready_constraints = [(0, 3), (4, 8), (9, 15)]
        self.ready_weights = [ 5, 2, 1]
        self.put_constraints = [(0, 3), (4, 8), (9, 15)]
        self.put_weights = [ 5, 2, 1]



    async def randomize_ready(self, duration_ns=10000, min_interval=10, max_interval=100):
        """Randomly toggle i_pkt_ready signal within specified intervals."""
        crand = ConstrainedRandom(self.ready_constraints, self.ready_weights)
        end_time = get_sim_time('ns') + duration_ns
        while get_sim_time('ns') < end_time:
            interval = crand.next()
            await self.wait_clocks('i_clk', interval)
            self.dut.i_pkt_ready.value = not self.dut.i_pkt_ready.value


    async def add_rnd_pkt_after_full_clears(self, max_packets=256):
        """Wait for full to clear, then inject packets with a random delay."""
        crand = ConstrainedRandom(self.put_constraints, self.put_weights)
        await FallingEdge(self.dut.ow_pkt_full)
        interval = crand.next()
        await self.wait_clocks('i_clk', interval)
        
        for _ in range(random.randint(1, max_packets)):
            if not self.dut.ow_pkt_full.value:
                await self.add_rnd_pkt()
                interval = crand.next()
                await self.wait_clocks('i_clk', interval)
            else:
                while (self.dut.ow_pkt_full.value == 1):
                    interval = crand.next()
                    await self.wait_clocks('i_clk', interval)


    async def main_loop(self):
        self.log.info("Main Test")


    async def clear_interface(self):
        self.dut.i_pkt_put.value = 0
        self.dut.i_pkt_tag.value = 0
        self.dut.i_pkt_addr.value = 0
        self.dut.i_pkt_data.value = 0
        self.dut.i_pkt_count.value = 0
        self.dut.i_pkt_ready.value = 0


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    def check_empty(self):
        assert self.dut.ow_pkt_empty == 1, "ROB should be empty, but is not."


    def check_not_empty(self):
        assert self.dut.ow_pkt_empty == 0, "ROB should not be empty, but is."


    def check_full(self):
        assert self.dut.ow_pkt_full == 1, "ROB should be full, but is not."


    def check_not_full(self):
        assert self.dut.ow_pkt_full == 0, "ROB should not be full, but is."


    async def add_rnd_pkt(self):
        crand = ConstrainedRandom(self.tag_constraints, self.tag_weights)
        tag_val = crand.next()
        addr_val = random.randint(0, self.max_addr-1)
        data_val = random.randint(0, self.max_data-1)
        cnt_val = random.randint(0, self.max_count-1)
        await self.add_one_pkt(tag_val, addr_val, data_val, cnt_val)


    async def add_one_pkt(self, tag_val, addr_val, data_val, cnt_val):
        self.log.info(f"Putting Packet tag={self.hex_format(tag_val, self.max_tag)} " +\
                        f"addr={self.hex_format(addr_val, self.max_addr)} " +\
                        f"data={self.hex_format(data_val, self.max_data)} " +\
                        f"count={self.hex_format(cnt_val, self.max_count)}")
        self.dut.i_pkt_put.value = 1
        self.dut.i_pkt_tag.value = tag_val
        self.dut.i_pkt_addr.value = addr_val
        self.dut.i_pkt_data.value = data_val
        self.dut.i_pkt_count.value = cnt_val
        await self.wait_clocks('i_clk', 1)
        self.dut.i_pkt_put.value = 0
        self.dut.i_pkt_tag.value = 0
        self.dut.i_pkt_addr.value = 0
        self.dut.i_pkt_data.value = 0
        self.dut.i_pkt_count.value = 0


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
        self.log.info(f'    TAG_WIDTH:     {self.TAG_WIDTH}')
        self.log.info(f'    ADDR_WIDTH:    {self.ADDR_WIDTH}')
        self.log.info(f'    DATA_WIDTH:    {self.DATA_WIDTH}')
        self.log.info(f'    COUNT_WIDTH:   {self.COUNT_WIDTH}')
        self.log.info(f'    TIMER_WIDTH:   {self.TIMER_WIDTH}')
        self.log.info(f'    DEPTH:         {self.DEPTH}')
        self.log.info('Tag Constraints and Weights:')
        self.log.info(f'    {self.tag_constraints}')
        self.log.info(f'    {self.tag_weights}')
        self.log.info('Ready Constraints and Weights:')
        self.log.info(f'    {self.ready_constraints}')
        self.log.info(f'    {self.ready_weights}')
        self.log.info('Put Constraints and Weights:')
        self.log.info(f'    {self.put_constraints}')
        self.log.info(f'    {self.put_weights}')
        self.log.info('-------------------------------------------')
