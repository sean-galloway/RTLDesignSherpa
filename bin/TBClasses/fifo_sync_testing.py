from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from crc import Calculator, Configuration
import os
import random
from ConstrainedRandom import ConstrainedRandom

class FIFOSyncTB(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.TIMEOUT_CYCLES = 1000
        read_constraints = [(0, 2), (3, 8), (9,20)]
        read_weights = [5,2,1]
        self.read_crand = ConstrainedRandom(read_constraints, read_weights)
        write_constraints = [(0, 2), (3, 8), (9,20)]
        write_weights = [5,2,1]
        self.write_crand = ConstrainedRandom(write_constraints, write_weights)


    async def clear_interface(self):
        self.dut.i_write.value = 0
        self.dut.i_read.value = 0
        self.dut.i_wr_data.value = 0
        self.dut.i_rst_n.value = 0


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    async def main_loop(self, iterations, delay_clks_after):
        for _ in range(iterations):
            data = [random.randint(0, (1 << self.DATA_WIDTH) - 1) for _ in range(2*self.DEPTH)]
            cocotb.start_soon(self.write_fifo(data))
            read_values = await self.read_fifo(len(data))

            hex_data = [hex(num) for num in data]
            hex_read_data = [hex(num) for num in read_values]
            assert data == read_values, f"Data mismatch. Written: {hex_data}, Read: {hex_read_data}"

            await self.wait_clocks('i_clk', delay_clks_after)


    async def read_fifo(self, expected_data_length):
        self.log.info("Entering read_fifo with delay...")
        read_values = []
        timeout_counter = 0
        while self.dut.o_wr_full.value != 1:
            await self.wait_clocks('i_clk',1)
            timeout_counter += 1
            if timeout_counter >= self.TIMEOUT_CYCLES:
                self.log.error("Timeout waiting for FIFO to fill!")
                return

        delay = self.read_crand.next()
        for _ in range(delay):
            await self.wait_clocks('i_clk',1)

        data_read = 0
        timeout_counter = 0

        while data_read != expected_data_length:
            if self.dut.o_rd_empty.value == 1:
                self.dut.i_read.value = 0
                await self.wait_clocks('i_clk',1)
                self.log.info(f"FIFO Empty: waiting for more data (Iteration {data_read})")    
                continue

            self.dut.i_read.value = 1
            read_data = int(self.dut.ow_rd_data.value)
            read_values.append(read_data)
            data_read += 1
            await self.wait_clocks('i_clk',1)
            self.log.info(f"Read data from FIFO: {hex(read_data)} (Iteration {data_read})")

            delay = self.read_crand.next()
            self.dut.i_read.value = 0
            await self.wait_clocks('i_clk', delay)

            timeout_counter += 1
            if timeout_counter >= self.TIMEOUT_CYCLES:
                self.log.error("Timeout during read!")
                return

        self.dut.i_read.value = 0
        self.log.info("Exiting delayed_read_fifo...")
        return read_values


    async def write_fifo(self, data):
        self.log.info("Entering write_fifo...")
        self.dut.i_write.value = 0
        await self.wait_clocks('i_clk',1)      
        data_len = len(data)
        data_sent = 0
        timeout_counter = 0

        while data_sent != data_len:
            idx = data_sent
            self.log.info(f"Got Rising Edge of i_clk (Iteration {idx}). Checking if FIFO full...")

            while self.dut.o_wr_full.value == 0 and (data_sent != data_len):
                value = data[data_sent]
                idx = data_sent
                self.dut.i_write.value = 1
                self.dut.i_wr_data.value = value
                data_sent += 1
                await self.wait_clocks('i_clk',1)
                self.log.info(f"Writing data {hex(value)} to FIFO (Iteration {idx})...")

                self.dut.i_write.value = 0
                self.dut.i_write.value = 0
                delay = self.write_crand.next()
                await self.wait_clocks('i_clk', delay)

                timeout_counter += 1
                if timeout_counter >= self.TIMEOUT_CYCLES:
                    self.log.error("Timeout during write!")
                    return

            self.log.info(f"FIFO is full. Waiting for next clock cycle (Iteration {idx})...")
            self.dut.i_write.value = 0
            self.dut.i_wr_data.value = 0
            await self.wait_clocks('i_clk',1)

        self.dut.i_write.value = 0
        self.dut.i_wr_data.value = 0
        await self.wait_clocks('i_clk',1)

