import itertools
import logging
import os
import random
import subprocess

import cocotb_test.simulator
import pytest

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ReadOnly, NextTimeStep

from cocotb.regression import TestFactory

from cocotbext.axi import AxiBus, AxiMaster
from cocotbext.axi.sparse_memory import SparseMemory
from TBBase import TBBase


class TB:
    def __init__(self, dut):
        self.dut = dut

        self.log = logging.getLogger("cocotb.tb")
        self.log.setLevel(logging.DEBUG)

        cocotb.start_soon(Clock(dut.s_axi_aclk, 2, units="ns").start())

        self.axi_master = AxiMaster(AxiBus.from_prefix(dut, "s_axi"), dut.s_axi_aclk, dut.s_axi_aresetn)
        self.axi_ram = SparseMemory(size=2**16)

        # Start the write_ram and read_ram coroutines
        cocotb.start_soon(self.write_ram())
        cocotb.start_soon(self.read_ram())


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
        self.dut.s_axi_aresetn.value = 0
        self.dut.i_wr_pkt_ready.value = 0
        self.dut.i_rd_pkt_ready.value = 0
        self.dut.i_rdret_pkt_valid.value = 0
        self.dut.i_rdret_pkt_data.value = 0
        await RisingEdge(self.dut.s_axi_aclk)
        await RisingEdge(self.dut.s_axi_aclk)
        self.dut.s_axi_aresetn.value = 0
        await RisingEdge(self.dut.s_axi_aclk)
        await RisingEdge(self.dut.s_axi_aclk)
        self.dut.s_axi_aresetn.value = 1
        await RisingEdge(self.dut.s_axi_aclk)
        await RisingEdge(self.dut.s_axi_aclk)

    @cocotb.coroutine
    def write_ram(self):
        while True:
            # Wait for the valid signal to be asserted
            yield ReadOnly()
            while not self.dut.o_wr_pkt_valid.value:
                yield RisingEdge(self.dut.s_axi_aclk)

            # Randomly assert the ready signal
            ready_delay = int(random() * 5)  # Random delay between 0 and 4 clock cycles
            for _ in range(ready_delay):
                self.dut.i_wr_pkt_ready.value = 0
                yield RisingEdge(self.dut.s_axi_aclk)

            self.dut.i_wr_pkt_ready.value = 1

            # Capture the write data from the interface
            addr = int(self.dut.o_wr_pkt_addr.value)
            data = int(self.dut.o_wr_pkt_data.value)
            strb = int(self.dut.o_wr_pkt_strb.value)

            # Wait for a clock cycle
            yield RisingEdge(self.dut.s_axi_aclk)

            # Perform the write operation
            yield self.axi_ram.write(addr, data)

            # De-assert the ready signal
            self.dut.i_wr_pkt_ready.value = 0

            # Wait for a clock cycle before proceeding to the next transaction
            yield RisingEdge(self.dut.s_axi_aclk)

    @cocotb.coroutine
    def read_ram(self):
        while True:
            # Wait for the rd_pkt_valid signal to be asserted by the DUT
            yield ReadOnly()
            while not self.dut.o_rd_pkt_valid.value:
                yield RisingEdge(self.dut.s_axi_aclk)

            # Capture the read address from the DUT
            addr = int(self.dut.o_rd_pkt_addr.value)

            # Assert the rd_pkt_ready signal
            self.dut.i_rd_pkt_ready.value = 1

            # Wait for a clock cycle
            yield RisingEdge(self.dut.s_axi_aclk)

            # De-assert the rd_pkt_ready signal
            self.dut.i_rd_pkt_ready.value = 0

            # Perform the read operation on the AXI RAM
            data = yield self.axi_ram.read(addr)

            # Wait for the rdret_pkt_ready signal to be asserted by the DUT
            yield ReadOnly()
            while not self.dut.o_rdret_pkt_ready.value:
                yield RisingEdge(self.dut.s_axi_aclk)

            # Drive the read data back to the DUT
            self.dut.i_rdret_pkt_valid.value = 1
            self.dut.i_rdret_pkt_data.value = data

            # Wait for a clock cycle
            yield RisingEdge(self.dut.s_axi_aclk)

            # De-assert the rdret_pkt_valid signal
            dut.i_rdret_pkt_valid.value = 0

            # Wait for a clock cycle before proceeding to the next transaction
            yield RisingEdge(self.dut.s_axi_aclk)

async def run_test_write(dut, idle_inserter=None, backpressure_inserter=None, size=None):

    tb = TB(dut)

    byte_lanes = tb.axi_master.write_if.byte_lanes
    max_burst_size = tb.axi_master.write_if.max_burst_size

    if size is None:
        size = max_burst_size

    await tb.cycle_reset()

    tb.set_idle_generator(idle_inserter)
    tb.set_backpressure_generator(backpressure_inserter)

    for length in list(range(1, byte_lanes*2))+[1024]:
        for offset in list(range(byte_lanes))+list(range(4096-byte_lanes, 4096)):
            tb.log.info("length %d, offset %d", length, offset)
            addr = offset+0x1000
            test_data = bytearray([x % 256 for x in range(length)])

            await tb.axi_master.write(addr, test_data, size=size)

            await RisingEdge(dut.s_axi_aclk)


async def run_test_read(dut, idle_inserter=None, backpressure_inserter=None, size=None):

    tb = TB(dut)

    byte_lanes = tb.axi_master.write_if.byte_lanes
    max_burst_size = tb.axi_master.write_if.max_burst_size

    if size is None:
        size = max_burst_size

    await tb.cycle_reset()

    tb.set_idle_generator(idle_inserter)
    tb.set_backpressure_generator(backpressure_inserter)

    for length in list(range(1, byte_lanes*2))+[1024]:
        for offset in list(range(byte_lanes))+list(range(4096-byte_lanes, 4096)):
            tb.log.info("length %d, offset %d", length, offset)
            addr = offset+0x1000
            test_data = bytearray([x % 256 for x in range(length)])

            data = await tb.axi_master.read(addr, length, size=size)

            assert data.data == test_data

            await RisingEdge(dut.s_axi_aclk)


async def run_test_write_words(dut):

    tb = TB(dut)

    byte_lanes = tb.axi_master.write_if.byte_lanes

    await tb.cycle_reset()

    for length, offset in itertools.product(list(range(1, 4)), list(range(byte_lanes))):
        tb.log.info("length %d, offset %d", length, offset)
        addr = offset+0x1000

        test_data = bytearray([x % 256 for x in range(length)])
        event = tb.axi_master.init_write(addr, test_data)
        await event.wait()
        assert tb.axi_ram.read(addr, length) == test_data

        test_data = bytearray([x % 256 for x in range(length)])
        await tb.axi_master.write(addr, test_data)
        assert tb.axi_ram.read(addr, length) == test_data

        test_data = [x * 0x1001 for x in range(length)]
        await tb.axi_master.write_words(addr, test_data)
        assert tb.axi_ram.read_words(addr, length) == test_data

        test_data = [x * 0x10200201 for x in range(length)]
        await tb.axi_master.write_dwords(addr, test_data)
        assert tb.axi_ram.read_dwords(addr, length) == test_data

        test_data = [x * 0x1020304004030201 for x in range(length)]
        await tb.axi_master.write_qwords(addr, test_data)
        assert tb.axi_ram.read_qwords(addr, length) == test_data

        test_data = 0x01*length
        await tb.axi_master.write_byte(addr, test_data)
        assert tb.axi_ram.read_byte(addr) == test_data

        test_data = 0x1001*length
        await tb.axi_master.write_word(addr, test_data)
        assert tb.axi_ram.read_word(addr) == test_data

        test_data = 0x10200201*length
        await tb.axi_master.write_dword(addr, test_data)
        assert tb.axi_ram.read_dword(addr) == test_data

        test_data = 0x1020304004030201*length
        await tb.axi_master.write_qword(addr, test_data)
        assert tb.axi_ram.read_qword(addr) == test_data

    await RisingEdge(dut.s_axi_aclk)
    await RisingEdge(dut.s_axi_aclk)


async def run_test_read_words(dut):

    tb = TB(dut)

    byte_lanes = tb.axi_master.write_if.byte_lanes

    await tb.cycle_reset()

    for length, offset in itertools.product(list(range(1, 4)), list(range(byte_lanes))):
        tb.log.info("length %d, offset %d", length, offset)
        addr = offset+0x1000

        test_data = bytearray([x % 256 for x in range(length)])
        tb.axi_ram.write(addr, test_data)
        event = tb.axi_master.init_read(addr, length)
        await event.wait()
        assert event.data.data == test_data

        test_data = bytearray([x % 256 for x in range(length)])
        tb.axi_ram.write(addr, test_data)
        assert (await tb.axi_master.read(addr, length)).data == test_data

        test_data = [x * 0x1001 for x in range(length)]
        tb.axi_ram.write_words(addr, test_data)
        assert await tb.axi_master.read_words(addr, length) == test_data

        test_data = [x * 0x10200201 for x in range(length)]
        tb.axi_ram.write_dwords(addr, test_data)
        assert await tb.axi_master.read_dwords(addr, length) == test_data

        test_data = [x * 0x1020304004030201 for x in range(length)]
        tb.axi_ram.write_qwords(addr, test_data)
        assert await tb.axi_master.read_qwords(addr, length) == test_data

        test_data = 0x01*length
        tb.axi_ram.write_byte(addr, test_data)
        assert await tb.axi_master.read_byte(addr) == test_data

        test_data = 0x1001*length
        tb.axi_ram.write_word(addr, test_data)
        assert await tb.axi_master.read_word(addr) == test_data

        test_data = 0x10200201*length
        tb.axi_ram.write_dword(addr, test_data)
        assert await tb.axi_master.read_dword(addr) == test_data

        test_data = 0x1020304004030201*length
        tb.axi_ram.write_qword(addr, test_data)
        assert await tb.axi_master.read_qword(addr) == test_data

    await RisingEdge(dut.s_axi_aclk)
    await RisingEdge(dut.s_axi_aclk)


async def run_stress_test(dut, idle_inserter=None, backpressure_inserter=None):

    tb = TB(dut)

    await tb.cycle_reset()

    tb.set_idle_generator(idle_inserter)
    tb.set_backpressure_generator(backpressure_inserter)

    async def worker(master, offset, aperture, count=16):
        for k in range(count):
            length = random.randint(1, min(512, aperture))
            addr = offset+random.randint(0, aperture-length)
            test_data = bytearray([x % 256 for x in range(length)])

            await Timer(random.randint(1, 100), 'ns')

            await master.write(addr, test_data)

            await Timer(random.randint(1, 100), 'ns')

            data = await master.read(addr, length)
            assert data.data == test_data

    workers = []

    for k in range(16):
        workers.append(cocotb.start_soon(worker(tb.axi_master, k*0x1000, 0x1000, count=16)))

    while workers:
        await workers.pop(0).join()

    await RisingEdge(dut.s_axi_aclk)
    await RisingEdge(dut.s_axi_aclk)


def cycle_pause():
    return itertools.cycle([1, 1, 1, 0])


if cocotb.SIM_NAME:

    data_width = int(os.environ.get('AXI_DATA_WIDTH', '0'))
    byte_lanes = data_width // 8
    max_burst_size = (byte_lanes-1).bit_length()

    for test in [run_test_write, run_test_read]:

        factory = TestFactory(test)
        factory.add_option("idle_inserter", [None, cycle_pause])
        factory.add_option("backpressure_inserter", [None, cycle_pause])
        factory.add_option("size", [None]+list(range(max_burst_size)))
        factory.generate_tests()

    for test in [run_test_write_words, run_test_read_words]:

        factory = TestFactory(test)
        factory.generate_tests()

    factory = TestFactory(run_stress_test)
    factory.generate_tests()



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

    cocotb_test.simulator.run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )