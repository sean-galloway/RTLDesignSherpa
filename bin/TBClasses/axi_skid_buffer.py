from TBBase import TBBase
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from cocotb.utils import get_sim_time
import os
import random
from ConstrainedRandom import ConstrainedRandom

class AXISkidBufferTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.DEPTH = 2
        self.TIMEOUT_CYCLES = 100
        read_constraints = [(0, 1), (2, 8), (9,30)]
        read_weights = [5,2,1]
        self.read_crand = ConstrainedRandom(read_constraints, read_weights)
        write_constraints = [(0, 0), (1, 8), (9,20)]
        write_weights = [5,2,1]
        self.write_crand = ConstrainedRandom(write_constraints, write_weights)


    async def clear_interface(self):
        self.dut.i_wr_valid.value = 0
        self.dut.i_wr_data.value = 0
        self.dut.i_rd_ready.value = 0


    async def assert_reset(self):
        self.dut.i_axi_aresetn.value = 0
        await self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_axi_aresetn.value = 1
        self.log.info("Reset complete.")


    async def main_loop(self, iterations, delay_clks_after):
        for _ in range(iterations):
            # Define the test parameters
            transfer_count = self.DEPTH*5
            data = [random.randint(0, (1 << self.DATA_WIDTH) - 1) for _ in range(transfer_count)]
            pause_duration = 100  # Clock cycles to pause after count transfers

            # Start concurrent read and write operations
            write_skid = cocotb.start_soon(self.write_fifo(data, transfer_count, pause_duration))
            read_skid = cocotb.start_soon(self.read_fifo(transfer_count, pause_duration))

            # Wait for both operations to complete and compare results
            await write_skid
            read_data = await read_skid

            hex_data = [format(num, '02x') for num in data]
            hex_read_data = [format(num, '02x') for num in read_data]
            self.log.info(f'Written: {hex_data}')
            self.log.info(f'Read:    {hex_read_data}')
            assert data[:transfer_count] == read_data, f"Data mismatch. Written: {hex_data}, Read: {hex_read_data}"

            await self.wait_clocks('i_axi_aclk', delay_clks_after)


    async def write_fifo(self, data, count, pause_duration):
        self.log.info("Entering write_fifo with constrained random behavior...")
        hex_data = [format(num, '02x') for num in data]
        self.log.info(f'Attempting to write {count=} packets: {len(data)=} {hex_data=}')
        self.dut.i_wr_valid.value = 0
        data_sent = 0

        while data_sent < count:
            # Generate random behavior based on constrained random
            crand = self.write_crand.next()

            # Prepare the data and assert i_valid if crand permits
            if crand == 0:
                self.dut.i_wr_valid.value = 1
                idx = data_sent
                self.dut.i_wr_data.value = data[idx]
                await FallingEdge(self.dut.i_axi_aclk)

                while self.dut.o_wr_ready.value == 0:  # Wait until o_ready is asserted
                    await FallingEdge(self.dut.i_axi_aclk)
                    timeout_counter += 1

                    # Check for timeout
                    if timeout_counter >= self.TIMEOUT_CYCLES:
                        self.log.error("Timeout waiting for o_wr_ready to assert during write")
                        self.dut.i_wr_valid.value = 0  # Ensure i_valid is de-asserted on timeout
                        self.dut.i_wr_data.value = 0
                        return  # Exit the method on timeout

                # If o_ready is high and i_valid is high, increment data_sent
                data_sent += 1
                current_time_ns = get_sim_time('ns')
                self.log.info(f"Writing data to skid: {hex(data[idx])} pkt={data_sent:3} @ {current_time_ns}ns")
                await self.wait_clocks('i_axi_aclk', 1)
            else:
                self.log.info(f'---> i_wr_valid remains de-asserted for {crand} cycles')
                self.dut.i_wr_valid.value = 0
                self.dut.i_wr_data.value = 0
                await self.wait_clocks('i_axi_aclk', crand)

            # Reset values for the next iteration/data word
            self.dut.i_wr_valid.value = 0
            self.dut.i_wr_data.value = 0
            timeout_counter = 0

        # Final clean-up: Ensure i_valid is de-asserted after all data is sent
        await self.wait_clocks('i_axi_aclk', pause_duration)
        self.log.info(f'Exiting write after sending {data_sent} packets')


    async def read_fifo(self, count, pause_duration):
        self.log.info("Entering read_fifo with constrained random behavior...")
        self.log.info(f'Attempting to read  {count=} packets')
        read_values = []
        self.dut.i_rd_ready.value = 0
        data_read = 0
        timeout_counter = 0

        while data_read < count:
            # Generate random behavior based on constrained random
            crand = self.write_crand.next()
            
            # Prepare the data and assert i_valid if crand permits
            if crand == 0:
                self.dut.i_rd_ready.value = 1
                await FallingEdge(self.dut.i_axi_aclk)
                while self.dut.o_rd_valid.value == 0:
                    await FallingEdge(self.dut.i_axi_aclk)
                    timeout_counter += 1
                    if timeout_counter >= self.TIMEOUT_CYCLES:
                        self.log.error("Timeout during read, waiting for o_rd_valid to assert")
                        return  read_values # Exit the method on timeout
                read_data = int(self.dut.o_rd_data.value)
                read_values.append(read_data)
                data_read += 1
                current_time_ns = get_sim_time('ns')
                self.log.info(f"Read data from skid:  {hex(read_data)} pkt={data_read:3} @ {current_time_ns}ns")
                await self.wait_clocks('i_axi_aclk', 1)
            else:
                self.log.info(f'---> i_rd_ready remains de-asserted for {crand} cycles')
                self.dut.i_rd_ready.value = 0
                await self.wait_clocks('i_axi_aclk', crand)

            # Reset values for the next iteration/data word
            self.dut.i_rd_ready.value = 0
            timeout_counter = 0

        await self.wait_clocks('i_axi_aclk',pause_duration)
        self.log.info(f'Exiting read after receiving {data_read} packets')

        return read_values
