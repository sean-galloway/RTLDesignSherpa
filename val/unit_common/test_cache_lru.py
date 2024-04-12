import cocotb
from cocotb.triggers import FallingEdge, Timer, Event
from cocotb.clock import Clock
from cocotb.queue import Queue
from cocotb.utils import get_sim_time
import os
import subprocess
import random
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase
from ConstrainedRandom import ConstrainedRandom

class CTCache(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.A = self.convert_to_int(os.environ.get('PARAM_A', '0'))
        self.DW = self.convert_to_int(os.environ.get('PARAM_DW', '0'))
        self.AW = self.convert_to_int(os.environ.get('PARAM_AW', '0'))
        self.LINE_SIZE = self.DW // 8
        self.max_val = (2 ** self.AW) - 1
        self.data_memory = {}  # Dictionary to store written data
        self.address_queue = Queue()  # Queue to store addresses for read operations
        self.num_ops = 1000

    async def clear_interface(self):
        self.dut.i_rd.value = 0
        self.dut.i_wr.value = 0
        self.dut.i_wr_data.value = 0
        self.dut.i_wr_dm.value = 0
        self.dut.i_snoop_valid.value = 0
        self.dut.i_snoop_cmd.value = 0
        self.dut.i_snoop_addr.value = 0
        self.log.info('Clearing interface done.')

    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()
        self.log.info('Assert reset done.')

    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")

    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    DEPTH: {self.DEPTH}')
        self.log.info(f'    A:     {self.A}')
        self.log.info(f'    DW:    {self.DW}')
        self.log.info(f'    AW:    {self.AW}')
        self.log.info('-------------------------------------------')

    async def main_loop(self, count=100):
        """ Test with randomized concurrent read/write operations and snoop requests """
        operation_done_event = Event()

        # Start the concurrent processes
        cocotb.start_soon(self.drive_writes(operation_done_event))
        cocotb.start_soon(self.drive_reads(operation_done_event))
        cocotb.start_soon(self.drive_snoop(operation_done_event))

        # Wait for the operations to complete
        await operation_done_event.wait()

        # Run after the run
        await self.wait_clocks('i_clk', 50)

    async def drive_writes(self, operation_done_event):
        """Randomly perform write operations and add addresses to the queue."""
        write_constraints = [(0, 20), (21, 60), (61, 90), (91, 100)]
        write_weights = [10, 20, 15, 1]
        crand_write = ConstrainedRandom(write_constraints, write_weights)
        delay_constraints = [(0, 2), (3, 10), (11, 20), (21, 30)]
        delay_weights = [5, 10, 5, 1]
        crand_delay = ConstrainedRandom(delay_constraints, delay_weights)

        num_operations = self.num_ops

        for _ in range(num_operations):
            if crand_write.next() > 50:  # Adjust the threshold as needed
                wr_addr = random.randint(0, self.max_val)
                wr_data = random.randint(0, 2 ** self.DW - 1)
                wr_dm = random.randint(0, 2 ** self.LINE_SIZE - 1)
                self.dut.i_wr_addr.value = wr_addr
                self.dut.i_wr.value = 1
                self.dut.i_wr_data.value = wr_data
                self.dut.i_wr_dm.value = wr_dm
                await Timer(100, units='ps')
                await self.wait_clocks('i_clk', 1)
                is_hit = self.dut.o_wr_hit.value
                addr_hex = self.hex_format(wr_addr, self.max_val)
                wr_data_hex = self.hex_format(wr_data, self.max_val)
                wr_dm_hex = self.hex_format(wr_dm, self.max_val)
                current_time_ns = get_sim_time('ns')
                self.log.info(f'Write: Addr: {addr_hex} Data: {wr_data_hex} DM: {wr_dm_hex} Hit: {is_hit} Time: {current_time_ns}')
                self.dut.i_wr.value = 0
                self.dut.i_wr_data.value = 0
                self.dut.i_wr_dm.value = 0
                self.address_queue.put_nowait(wr_addr)  # Add the written address to the queue
                self.data_memory[wr_addr] = wr_data  # Store the written data in the dictionary

            await self.wait_clocks('i_clk', crand_delay.next())

        operation_done_event.set()

    async def drive_reads(self, operation_done_event):
        """Randomly perform read operations using addresses from the queue."""
        read_constraints = [(0, 10), (11, 50), (51, 80), (81, 100)]
        read_weights = [5, 10, 20, 1]
        crand_read = ConstrainedRandom(read_constraints, read_weights)
        delay_constraints = [(0, 2), (3, 10), (11, 20), (21, 30)]
        delay_weights = [5, 10, 5, 1]
        crand_delay = ConstrainedRandom(delay_constraints, delay_weights)

        num_operations = self.num_ops

        for _ in range(num_operations):
            if crand_read.next() > 50:  # Adjust the threshold as needed
                if not self.address_queue.empty():
                    rd_addr = self.address_queue.get_nowait()
                    self.dut.i_rd_addr.value = rd_addr
                    self.dut.i_rd.value = 1
                    await Timer(100, units='ps')
                    await self.wait_clocks('i_clk', 1)
                    is_hit = self.dut.o_rd_hit.value
                    rd_data = self.dut.o_rd_data.value
                    addr_hex = self.hex_format(rd_addr, self.max_val)
                    rd_data_hex = self.hex_format(rd_data, self.max_val)
                    current_time_ns = get_sim_time('ns')
                    expected_data = self.data_memory.get(rd_addr, 0)  # Get the expected data from the dictionary
                    self.log.info(f'Read: Addr: {addr_hex} Data: {rd_data_hex} Expected: {self.hex_format(expected_data, self.max_val)} Hit: {is_hit} Time: {current_time_ns}')
                    if expected_data != rd_data:
                        self.log.error(f"Error: Read data mismatch for address {addr_hex}. Expected: {self.hex_format(expected_data, self.max_val)}, Actual: {rd_data_hex}")
                    self.dut.i_rd.value = 0

            await self.wait_clocks('i_clk', crand_delay.next())

        operation_done_event.set()

    async def drive_snoop(self, operation_done_event):
        """Randomly perform snoop operations."""
        snoop_constraints = [(0, 60), (61, 90), (91, 100)]
        snoop_weights = [30, 15, 1]
        crand_snoop = ConstrainedRandom(snoop_constraints, snoop_weights)
        delay_constraints = [(0, 2), (3, 10), (11, 20), (21, 30)]
        delay_weights = [5, 10, 5, 1]
        crand_delay = ConstrainedRandom(delay_constraints, delay_weights)

        num_operations = self.num_ops

        for _ in range(num_operations):
            if crand_snoop.next() > 50:  # Adjust the threshold as needed
                if random.random() < 0.2:  # 20% chance of generating a guaranteed miss
                    snoop_addr = random.randint(0, self.max_val)  # Generate a random address
                    while snoop_addr in self.data_memory:  # Ensure the address is not in the data_memory
                        snoop_addr = random.randint(0, self.max_val)
                elif self.address_queue.empty():
                    snoop_addr = random.randint(0, self.max_val)  # Generate a random address if the queue is empty

                else:
                    snoop_addr = self.address_queue.get_nowait()  # Use an address from the queue
                snoop_cmd = random.choices([0, 1, 2], weights=[6, 3, 1])[0]  # Adjust the weights as needed
                self.dut.i_snoop_addr.value = snoop_addr
                self.dut.i_snoop_valid.value = 1
                self.dut.i_snoop_cmd.value = snoop_cmd
                await Timer(100, units='ps')
                await self.wait_clocks('i_clk', 1)
                is_hit = self.dut.o_snoop_hit.value
                is_dirty = self.dut.o_snoop_dirty.value
                snoop_data = self.dut.o_snoop_data.value
                addr_hex = self.hex_format(snoop_addr, self.max_val)
                snoop_data_hex = self.hex_format(snoop_data, self.max_val) if is_hit else 'x' * (self.DW // 4)
                current_time_ns = get_sim_time('ns')
                self.log.info(f'Snoop: Addr: {addr_hex} Cmd: {snoop_cmd} Data: {snoop_data_hex} Hit: {is_hit} Dirty: {is_dirty} Time: {current_time_ns}')
                self.dut.i_snoop_valid.value = 0
                self.dut.i_snoop_cmd.value = 0
                self.dut.i_snoop_addr.value = 0

            await self.wait_clocks('i_clk', crand_delay.next())

        operation_done_event.set()

@cocotb.test()
async def cache_test(dut):
    """Test the cache"""
    tb = CTCache(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.main_loop()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__))  # gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common'))  # path to hdl folder where .v files are placed

@pytest.mark.parametrize("depth, a, dw, aw, lru_w", [(64, 4, 32, 32, 3)])
def test_cache(request, depth, a, dw, aw, lru_w):
    dut_name = "cache_lru"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {'DEPTH': depth, 'A': a, 'DW': dw, 'AW': aw, 'LRU_WIDTH': lru_w}

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_common', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit_common', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],  # where to search for all the python test files
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )