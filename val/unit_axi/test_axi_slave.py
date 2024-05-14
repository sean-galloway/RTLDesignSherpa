import contextlib
import itertools
import logging
import os
import random
import subprocess

import cocotb.triggers

from cocotb_test.simulator import run
import pytest

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ReadOnly

from cocotb.regression import TestFactory

from cocotbext.axi import AxiBus, AxiMaster, AxiRam
from TBBase import TBBase
from pprint import pprint


class AxiSlaveTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_AXI_DATA_WIDTH', '0'))
        cocotb.start_soon(Clock(dut.aclk, 2, units="ns").start())
        bus = AxiBus.from_prefix(dut, "s_axi")
        self.axi_master = AxiMaster(bus, dut.aclk, dut.aresetn, reset_active_level=False)
        self.axi_sparse_ram = {}
        self.done = False

        # Start the write_ram and read_ram coroutines
        cocotb.start_soon(self.write_ram())
        cocotb.start_soon(self.read_ram())
        self.log.info("Init Done.")


    def set_idle_generator(self, generator=None):
        if generator:
            self.axi_master.write_if.aw_channel.set_pause_generator(generator())
            self.axi_master.write_if.w_channel.set_pause_generator(generator())
            self.axi_master.read_if.ar_channel.set_pause_generator(generator())


    def set_backpressure_generator(self, generator=None):
        if generator:
            self.axi_master.write_if.b_channel.set_pause_generator(generator())
            self.axi_master.read_if.r_channel.set_pause_generator(generator())


    async def cycle_reset(self):
        self.log.info("Reset Start")
        self.dut.aresetn.value = 0
        self.dut.i_wr_pkt_ready.value = 0
        self.dut.i_rd_pkt_ready.value = 0
        self.dut.i_rdret_pkt_valid.value = 0
        self.dut.i_rdret_pkt_data.value = 0
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 0
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.log.info("Reset Done.")


    async def write_ram(self):
        while not self.done:
            # Wait for the valid signal to be asserted
            while not self.dut.o_wr_pkt_valid.value:
                await RisingEdge(self.dut.aclk)

            # Randomly assert the ready signal
            ready_delay = random.randint(0,0)  # Random delay between 0 and 4 clock cycles
            for _ in range(ready_delay):
                self.dut.i_wr_pkt_ready.value = 0
                await RisingEdge(self.dut.aclk)

            self.dut.i_wr_pkt_ready.value = 1

            # Capture the write data from the interface
            addr = int(self.dut.o_wr_pkt_addr.value)
            data = int(self.dut.o_wr_pkt_data.value)
            strb = int(self.dut.o_wr_pkt_strb.value)
            addr_hex = f'{addr:08x}'

            # Wait for a clock cycle
            await RisingEdge(self.dut.aclk)

            # Perform the write operation
            data_hex = f'{data:08x}'
            self.axi_sparse_ram[addr_hex] = data
            self.log.info(f'write_ram: {addr_hex=} {data_hex=}')

            # De-assert the ready signal
            self.dut.i_wr_pkt_ready.value = 0

            # Wait for a clock cycle before proceeding to the next transaction
            await RisingEdge(self.dut.aclk)


    async def read_ram(self):
        while not self.done:
            # Wait for the rd_pkt_valid signal to be asserted by the DUT
            while not self.dut.o_rd_pkt_valid.value:
                await RisingEdge(self.dut.aclk)

            # Capture the read address from the DUT
            addr = int(self.dut.o_rd_pkt_addr.value)
            addr_hex = f'{addr:08x}'

            # Randomly assert the ready signal
            ready_delay = random.randint(0,0)  # Random delay between 0 and 4 clock cycles
            for _ in range(ready_delay):
                self.dut.i_rd_pkt_ready.value = 0
                await RisingEdge(self.dut.aclk)

            # Assert the rd_pkt_ready signal
            self.dut.i_rd_pkt_ready.value = 1

            # Wait for a clock cycle
            await RisingEdge(self.dut.aclk)

            # De-assert the rd_pkt_ready signal
            self.dut.i_rd_pkt_ready.value = 0

            # Perform the read operation on the AXI RAM
            data = self.axi_sparse_ram[addr_hex] if addr_hex in self.axi_sparse_ram else 0
            data_hex = f'{data:08x}'
            self.log.info(f'read_ram: {addr_hex=} {data_hex=}')

            # Wait for the rdret_pkt_ready signal to be asserted by the DUT
            while not self.dut.o_rdret_pkt_ready.value:
                await RisingEdge(self.dut.aclk)

            # Drive the read data back to the DUT
            self.dut.i_rdret_pkt_valid.value = 1
            self.dut.i_rdret_pkt_data.value = data

            # Wait for a clock cycle
            await RisingEdge(self.dut.aclk)

            # De-assert the rdret_pkt_valid signal
            self.dut.i_rdret_pkt_valid.value = 0

            # Wait for a clock cycle before proceeding to the next transaction
            await RisingEdge(self.dut.aclk)


    def cycle_pause(self):
        return itertools.cycle([1, 1, 1, 0])


    async def run_test_write(self, idle_inserter=None, backpressure_inserter=None, size=None):
        self.log.info("run test write")
        byte_lanes = self.axi_master.write_if.byte_lanes
        max_burst_size = self.axi_master.write_if.max_burst_size

        if size is None:
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for length in list(range(1, byte_lanes*2))+[1024]:
            for offset in list(range(byte_lanes))+list(range(4096-(byte_lanes*8), 4096)):
                addr = offset+0x1000
                test_data = bytearray([x % 256 for x in range(length)])
                self.log.info(f"test_write: length {length}, offset {offset}, data {test_data}")
                await self.axi_master.write(addr, test_data, size=size)
                self.log.info(f"test_write: {addr=} {length=} {test_data=}")

        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)


    async def run_test_read(self, idle_inserter=None, backpressure_inserter=None, size=None):
        self.log.info("run test read")
        byte_lanes = self.axi_master.write_if.byte_lanes
        max_burst_size = self.axi_master.write_if.max_burst_size

        if size is None:
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for length in list(range(1, byte_lanes*2))+[1024]:
            for offset in list(range(byte_lanes))+list(range(4096-(byte_lanes*8), 4096)):
                self.log.info("length %d, offset %d", length, offset)
                addr = offset+0x1000
                test_data = bytearray([x % 256 for x in range(length)])
                data = await self.axi_master.read(addr, length, size=size)
                # assert data.data == test_data

        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)

    async def run_test_write_read(self, idle_inserter=None, backpressure_inserter=None, size=None):
        self.log.info("run test read")
        byte_lanes = self.axi_master.write_if.byte_lanes
        max_burst_size = self.axi_master.write_if.max_burst_size

        if size is None:
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for length in list(range(1, byte_lanes*2))+[1024]:
            for offset in list(range(byte_lanes))+list(range(4096-(byte_lanes*8), 4096)):
                self.log.info("length %d, offset %d", length, offset)
                addr = offset+0x1000
                test_data = bytearray([x % 256 for x in range(length)])
                await self.axi_master.write(addr, test_data, size=size)
                data = await self.axi_master.read(addr, length, size=size)
                assert data.data == test_data

        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)


    async def main_loop(self):
        data_width = self.DATA_WIDTH
        byte_lanes = data_width // 8
        max_burst_size = (byte_lanes-1).bit_length()

        # write tests
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)

        # read tests
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)

        # write_read tests
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)


@cocotb.test()
async def AxiSlave_test(dut):
    tb = AxiSlaveTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.cycle_reset()
    await tb.wait_clocks('aclk', 2)
    await tb.main_loop()
    await tb.wait_clocks('aclk', 2)
    tb.done = True
    tb.log.info("Test completed successfully.")


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi')) #path to hdl folder where .v files are placed


@pytest.mark.parametrize("id_width, addr_width, data_width, user_width", [(8,32,32,1)])
def test_axi(request, id_width, addr_width, data_width, user_width):
    dut_name = "axi_slave"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "counter_bin.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(rtl_axi_dir, "fifo_axi_sync.sv"),
        os.path.join(rtl_axi_dir, "axi_skid_buffer.sv"),
        os.path.join(rtl_axi_dir, "axi_gen_addr.sv"),
        os.path.join(rtl_axi_dir, f"{dut_name}.sv")
    ]
    includes = []
    parameters = {
        'AXI_ID_WIDTH': id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': user_width,
    }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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
