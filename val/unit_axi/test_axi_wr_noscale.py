import sys
import os
import subprocess

# Add the project root to the Python search path
repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
sys.path.append(repo_root)

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

from cocotbext.axi import AxiBus, AxiWriteBus, AxiMaster, AxiMasterWrite, AxiRamWrite, AxiSlave, MemoryRegion, AxiSlaveWrite
# import cocotbext.apb as apb
from pprint import pprint
from TBBase import TBBase
from APB import APBMonitor, APBSlave
from DelayRandomizer import DelayRandomizer


def convert_to_bytearray(data):
    """
    Convert the input data to a bytearray if it's not already one.
    
    Parameters:
    data (Any): The data to convert to a bytearray.

    Returns:
    bytearray: The converted bytearray.
    """
    if isinstance(data, bytearray):
        return data
    elif isinstance(data, (bytes, list)):
        return bytearray(data)
    else:
        raise TypeError("Input data must be a bytearray, bytes, or list of integers")


def bytearray_to_hex_strings(bytearrays):
    """
    Convert a list of bytearray values into hex strings.
    
    Parameters:
    bytearrays (list of bytearray): The list of bytearray values to convert.

    Returns:
    list of str: The list of hex strings.
    """
    return [bytearray_to_hex(ba) for ba in bytearrays]

def bytearray_to_hex(bytearray_value):
    """
    Convert a single bytearray to a hex string.
    
    Parameters:
    bytearray_value (bytearray): The bytearray to convert.

    Returns:
    str: The hex string.
    """
    return ''.join(f'{byte:02X}, ' for byte in bytearray_value)


class Axi2AxiTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.log = self.configure_logging(level=logging.DEBUG)
        self.log.info('Starting Axi2AxiTB')
        self.MST_DATA_WIDTH   = self.convert_to_int(os.environ.get('PARAM_AXI_MST_DATA_WIDTH', '0'))
        self.SLV_DATA_WIDTH   = self.convert_to_int(os.environ.get('PARAM_AXI_SLV_DATA_WIDTH', '0'))
        self.mst_strb_bits    = self.MST_DATA_WIDTH // 8
        self.slv_strb_bits    = self.SLV_DATA_WIDTH // 8
        self.debug            = True
        mst_bus               = AxiWriteBus.from_prefix(dut, "s_axi")
        self.axi_master       = AxiMasterWrite(mst_bus, dut.aclk, dut.aresetn, reset_active_level=False)   
        slv_bus               = AxiWriteBus.from_prefix(dut, "m_axi")
        self.axi_slave        = AxiSlaveWrite(slv_bus, dut.aclk, dut.aresetn, reset_active_level=False)   
        region                = MemoryRegion(2**self.axi_slave.address_width)
        self.axi_slave.target = region
        mem_bus               = AxiWriteBus.from_prefix(dut, 'm_axi')
        self.axi_ram          = AxiRamWrite(mem_bus, dut.aclk, dut.aresetn, reset_active_level=False, size=2**15)
        self.cycle_count      = 32
        self.main_loop_count  = 0
        self.log.info("Axi2AxiTB Init Done.")


    def set_idle_generator(self, generator=None):
        if generator:
            self.axi_master.aw_channel.set_pause_generator(generator())
            self.axi_master.w_channel.set_pause_generator(generator())
            self.axi_slave.b_channel.set_pause_generator(generator())


    def set_backpressure_generator(self, generator=None):
        if generator:
            self.axi_master.b_channel.set_pause_generator(generator())
            self.axi_slave.aw_channel.set_pause_generator(generator())
            self.axi_slave.w_channel.set_pause_generator(generator())


    async def cycle_reset(self):
        self.log.info("Reset Start")
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 2)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        self.log.info("Reset Done.")


    def cycle_pause(self):
        return itertools.cycle([1, 1, 1, 0])


    async def run_test_write(self, idle_inserter=None, backpressure_inserter=None, size=None):
        # sourcery skip: move-assign
        self.log.info(f'run test write/read: {size=}')
        max_burst_size = self.axi_master.max_burst_size
        length = self.cycle_count

        if size is None:
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for addr in range(length):
            test_data = bytearray([x % 256 for x in range(length)])
            self.log.info(f"run_test_write/write(AXI-wr): offset {addr}, size {size}, data {[f'{x:02X}' for x in test_data]}")
            await self.axi_master.write(addr, test_data, size=size)
            await self.wait_clocks('aclk', 10)

        await self.wait_clocks('aclk', 2)


    async def main_loop(self):
        self.main_loop_count += 1
        self.log.info(f"main_loop called {self.main_loop_count} times")

        max_burst_size = self.axi_master.max_burst_size

        # write_tests
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)


@cocotb.test()
async def axi_wr_noscale_test(dut):
    tb = Axi2AxiTB(dut)
    cocotb.start_soon(Clock(dut.aclk, 2, units="ns").start())
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
rtl_integ_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl', 'integ_axi', 'axi_xbar')) #path to hdl folder where .v files are placed

# @pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width", [(8,32,8,1,12,8),(8,32,16,1,12,8),(8,32,32,1,12,8),(8,32,64,1,12,8)])
@pytest.mark.parametrize("id_width, addr_width, mst_data_width, slv_data_width, user_width ", [(8,32,32,32,1)])
def test_axi_wr_noscale(request, id_width, addr_width, mst_data_width, slv_data_width, user_width ):
    dut_name = "axi_wr_noscale"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_axi_dir, "axi_skid_buffer.sv"),
        os.path.join(rtl_axi_dir, "axi_slave_wr_stub.sv"),
        os.path.join(rtl_axi_dir, "axi_master_wr_stub.sv"),
        os.path.join(rtl_integ_axi_dir, f"{dut_name}.sv")
    ]
    includes = []
    parameters = {
        'AXI_ID_WIDTH':       id_width,
        'AXI_ADDR_WIDTH':     addr_width,
        'AXI_MST_DATA_WIDTH': mst_data_width,
        'AXI_SLV_DATA_WIDTH': slv_data_width,
        'AXI_USER_WIDTH':     user_width
    }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

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
