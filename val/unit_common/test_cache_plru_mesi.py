import cocotb
from cocotb.triggers import FallingEdge, Timer, Event, RisingEdge
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

class CTCacheMESI(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.A = self.convert_to_int(os.environ.get('PARAM_A', '0'))
        self.DW = self.convert_to_int(os.environ.get('PARAM_DW', '0'))
        self.AW = self.convert_to_int(os.environ.get('PARAM_AW', '0'))
        self.LINE_SIZE = self.DW // 8
        self.max_val_aw = (2 ** self.AW) - 1
        self.max_val_dw = (2 ** self.DW) - 1
        self.max_val_dm = (2 ** self.LINE_SIZE) - 1
        self.data_memory = {}  # Dictionary to store written data
        self.address_queue = Queue()  # Queue to store addresses for read operations
        self.num_ops = 1000

    async def clear_interface(self):
        self.dut.i_sysbusin_valid.value = 0
        self.dut.i_sysbusin_op_rdxwr.value = 0
        self.dut.i_sysbusin_addr.value = 0
        self.dut.i_sysbusin_data.value = 0
        self.dut.i_sysbusin_dm.value = 0
        self.dut.i_sysbusout_ready = 0
        self.dut.i_memin_valid.value = 0
        self.dut.i_memin_op_rdxwr.value = 0
        self.dut.i_memin_addr.value = 0
        self.dut.i_memin_data.value = 0
        self.dut.i_memin_dm.value = 0
        self.dut.i_memout_ready = 0
        self.dut.i_snoop_valid.value = 0
        self.dut.i_snoop_cmd.value = 0
        self.dut.i_snoop_addr.value = 0
        self.dut.i_c2c_snp_ready = 0
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
        cocotb.start_soon(self.drive_sysbus(operation_done_event))
        cocotb.start_soon(self.drive_membus(operation_done_event))
        cocotb.start_soon(self.drive_snoop(operation_done_event))

        # Wait for the operations to complete
        await operation_done_event.wait()

        # Run after the run
        await self.wait_clocks('i_clk', 50)

    async def drive_sysbus(self, operation_done_event):
        # sourcery skip: low-code-quality
        """Randomly perform read/write operations on the sysbus interface."""
        write_constraints = [(0, 20), (21, 60), (61, 90), (91, 100)]
        write_weights = [10, 20, 15, 1]
        crand_write = ConstrainedRandom(write_constraints, write_weights)

        delay_constraints = [(0, 2), (3, 10), (11, 20), (21, 30)]
        delay_weights = [5, 10, 5, 1]
        crand_delay = ConstrainedRandom(delay_constraints, delay_weights)

        num_operations = self.num_ops
        count = 0
        for _ in range(num_operations):
            op_type = random.choice(['read', 'write'])
            self.log.info(f'sysbus: {count=} {op_type=}')
            count += 1

            if op_type == 'write' and crand_write.next() > 50:  # Adjust the threshold as needed
                wr_addr = random.randint(0, self.max_val_aw)
                wr_data = random.randint(0, self.max_val_dw)
                wr_dm = random.randint(0, self.max_val_dm)

                self.dut.i_sysbusin_valid.value = 1
                self.dut.i_sysbusin_op_rdxwr.value = 1
                self.dut.i_sysbusin_addr.value = wr_addr
                self.dut.i_sysbusin_data.value = wr_data
                self.dut.i_sysbusin_dm.value = wr_dm

                await self.wait_clocks('i_clk', 1)
                while not self.dut.o_sysbusin_ready.value:
                    await self.wait_clocks('i_clk', 1)

                self.dut.i_sysbusin_valid.value = 0

                addr_hex = self.hex_format(wr_addr, self.max_val_aw)
                wr_data_hex = self.hex_format(wr_data, self.max_val_dw)
                wr_dm_hex = self.hex_format(wr_dm, self.max_val_dm)
                current_time_ns = get_sim_time('ns')
                self.log.info(f'Write: Addr: {addr_hex} Data: {wr_data_hex} DM: {wr_dm_hex} Time: {current_time_ns}')
                self.data_memory[addr_hex] = wr_data_hex  # Store the written data in the dictionary

            else:  # op_type == 'read'
                rd_addr = random.randint(0, self.max_val_aw)

                self.dut.i_sysbusin_valid.value = 1
                self.dut.i_sysbusin_op_rdxwr.value = 0
                self.dut.i_sysbusin_addr.value = rd_addr
                self.dut.i_sysbusin_data.value = 0
                self.dut.i_sysbusin_dm.value = 0

                await self.wait_clocks('i_clk', 1)
                while not self.dut.o_sysbusin_ready.value:
                    await self.wait_clocks('i_clk', 1)

                self.dut.i_sysbusin_valid.value = 0
                self.address_queue.put_nowait(rd_addr)  # Add the read address to the queue

                self.dut.i_sysbusout_ready.value = 1
                await self.wait_clocks('i_clk', 1)
                while not self.dut.o_sysbusout_valid.value:
                    await self.wait_clocks('i_clk', 1)

                self.dut.i_sysbusout_ready.value = 0

                rd_data = self.dut.o_sysbusout_data.value
                addr_hex = self.hex_format(rd_addr, self.max_val_aw)
                rd_data_hex = self.hex_format(rd_data, self.max_val_dw)
                current_time_ns = get_sim_time('ns')
                self.log.info(f'Read: Addr: {addr_hex} Data: {rd_data_hex} Time: {current_time_ns}')

            await self.wait_clocks('i_clk', crand_delay.next())

        operation_done_event.set()

    async def drive_membus(self, operation_done_event):
        """Handle requests on the membus interface."""

        while True:
            await self.wait_clocks('i_clk', 1)

            if self.dut.o_memout_valid.value:
                self.dut.i_memout_ready.value = 1
                await self.wait_clocks('i_clk', 1)
                op_type = 'write' if self.dut.o_memout_op_rdxwr.value else 'read'
                addr = self.dut.o_memout_addr.value
                addr_hex = self.hex_format(addr, self.max_val_aw)

                if op_type == 'write':
                    data = self.dut.o_memout_data.value
                    self.data_memory[addr] = data  # Store the written data in the dictionary
                    addr_hex = self.hex_format(addr, self.max_val_aw)
                    data_hex = self.hex_format(data, self.max_val_dw)
                    current_time_ns = get_sim_time('ns')
                    self.log.info(f'Mem Write: Addr: {addr_hex} Data: {data_hex} Time: {current_time_ns}')
                else:
                    data = self.data_memory.get(addr_hex, 0)  # Get the read data from the dictionary
                    self.dut.i_memin_valid.value = 1
                    self.dut.i_memin_op_rdxwr.value = 0
                    self.dut.i_memin_addr.value = addr
                    self.dut.i_memin_data.value = data

                    while not self.dut.o_memin_ready.value:
                        await self.wait_clocks('i_clk', 1)

                    self.dut.i_memin_valid.value = 0

                    addr_hex = self.hex_format(addr, self.max_val_aw)
                    data_hex = self.hex_format(data, self.max_val_dw)
                    current_time_ns = get_sim_time('ns')
                    self.log.info(f'Mem Read: Addr: {addr_hex} Data: {data_hex} Time: {current_time_ns}')

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
                    snoop_addr = random.randint(0, self.max_val_aw)  # Generate a random address
                    while snoop_addr in self.data_memory:  # Ensure the address is not in the data_memory
                        snoop_addr = random.randint(0, self.max_val_dw)
                elif self.address_queue.empty():
                    snoop_addr = random.randint(0, self.max_val_aw)  # Generate a random address if the queue is empty
                else:
                    snoop_addr = self.address_queue.get_nowait()  # Use an address from the queue

                snoop_cmd = random.choices([0, 1, 2], weights=[6, 3, 1])[0]  # Adjust the weights as needed
                self.dut.i_snoop_addr.value = snoop_addr
                self.dut.i_snoop_valid.value = 1
                self.dut.i_snoop_cmd.value = snoop_cmd

                await self.wait_clocks('i_clk', 1)

                while not self.dut.o_snoop_ready.value:
                    await self.wait_clocks('i_clk', 1)

                self.dut.i_snoop_valid.value = 0

                is_hit = self.dut.o_snoop_hit.value
                is_dirty = self.dut.o_snoop_dirty.value
                snoop_data = self.dut.o_snoop_data.value
                addr_hex = self.hex_format(snoop_addr, self.max_val_aw)
                snoop_data_hex = self.hex_format(snoop_data, self.max_val_dw) if is_hit else 'x' * (self.DW // 4)
                current_time_ns = get_sim_time('ns')
                self.log.info(f'Snoop: Addr: {addr_hex} Cmd: {snoop_cmd} Data: {snoop_data_hex} Hit: {is_hit} Dirty: {is_dirty} Time: {current_time_ns}')

                if snoop_cmd == 0 and is_hit:
                    await RisingEdge(self.dut.o_c2c_snp_valid)
                    while not self.dut.i_c2c_snp_ready.value:
                        await self.wait_clocks('i_clk', 1)
                    c2c_data = self.dut.o_c2c_snp_data.value
                    c2c_data_hex = self.hex_format(c2c_data, self.max_val_aw)
                    self.log.info(f'C2C Transfer: Addr: {addr_hex} Data: {c2c_data_hex} Time: {current_time_ns}')

            await self.wait_clocks('i_clk', crand_delay.next())

        operation_done_event.set()


@cocotb.test()
async def cache_mesi_test(dut):
    """Test the MESI cache"""
    tb = CTCacheMESI(dut)
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
axi_rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi'))  # path to hdl folder where .v files are placed

@pytest.mark.parametrize("depth, a, dw, aw", [(64, 4, 32, 32)])
def test_cache_plru_mesi(request, depth, a, dw, aw):
    dut_name = "cache_plru_mesi"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "counter_bin.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(axi_rtl_dir, "axi_fifo_sync.sv"),
        os.path.join(rtl_dir, "fifo_sync.sv"),
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {'DEPTH': depth, 'A': a, 'DW': dw, 'AW': aw}

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

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