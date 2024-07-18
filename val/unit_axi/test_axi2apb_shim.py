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

from cocotbext.axi import AxiBus, AxiMaster
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


class Axi2ApbTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.log = self.configure_logging(level=logging.DEBUG)
        self.log.info('Starting Axi2ApbTB')
        self.DATA_WIDTH      = self.convert_to_int(os.environ.get('PARAM_AXI_DATA_WIDTH', '0'))      
        self.APB_ADDR_WIDTH  = self.convert_to_int(os.environ.get('PARAM_APB_ADDR_WIDTH', '0'))
        self.APB_DATA_WIDTH  = self.convert_to_int(os.environ.get('PARAM_APB_DATA_WIDTH', '0'))
        self.strb_bits       = self.DATA_WIDTH // 8
        self.debug           = True
        bus                  = AxiBus.from_prefix(dut, "s_axi")
        self.axi_master      = AxiMaster(bus, dut.aclk, dut.aresetn, reset_active_level=False)   
        self.registers       = 32 * self.strb_bits
        self.slave_register  = list(range(self.registers))
        apb_slv_constraints  = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_monitor     = APBMonitor(dut, 'm_apb', dut.aclk,
                                            bus_width=self.APB_DATA_WIDTH, addr_width=self.APB_ADDR_WIDTH)
        self.apb_slave       = APBSlave(dut, 'm_apb', dut.aclk, registers=self.slave_register,
                                            bus_width=self.APB_DATA_WIDTH, addr_width=self.APB_ADDR_WIDTH,
                                            constraints=apb_slv_constraints)
        self.main_loop_count = 0
        self.log.info("Axi2ApbTB Init Done.")


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
        await self.apb_slave.reset_bus()
        await self.wait_clocks('aclk', 2)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        self.log.info("Reset Done.")


    def cycle_pause(self):
        return itertools.cycle([1, 1, 1, 0])


    async def run_test_write_read(self, idle_inserter=None, backpressure_inserter=None, size=None):
        # sourcery skip: move-assign
        self.log.info(f'run test write/read: {size=}')
        max_burst_size = self.axi_master.write_if.max_burst_size
        length = int(self.registers/(self.DATA_WIDTH/self.APB_DATA_WIDTH))

        if size is None:
            # size = int(max_burst_size / (self.DATA_WIDTH/self.APB_DATA_WIDTH))
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for addr in range(length):
            test_data = bytearray([x % 256 for x in range(length)])
            self.log.info(f"run_test_write/write(AXI-wr): offset {addr}, size {size}, data {[f'{x:02X}' for x in test_data]}")
            await self.axi_master.write(addr, test_data, size=size)
            await self.wait_clocks('aclk', 100)
            if self.debug:
                self.apb_slave.dump_registers()

            data = await self.axi_master.read(addr, length, size=size)
            self.log.info(f"run_test_write/read(AXI-rd): offset {addr}, size {size}, length {length} data {[f'{x:02X}' for x in test_data]}")

            data_ba = convert_to_bytearray(data.data)
            data_in_hex = bytearray_to_hex_strings([data_ba])
            self.log.info(f'Read  Data: {data_in_hex}')

            data_bk_ba = convert_to_bytearray(test_data)
            data_bk_hex = bytearray_to_hex_strings([data_bk_ba])
            self.log.info(f'Write Data: {data_bk_hex}')

            assert data.data == test_data
            await self.wait_clocks('aclk', 100)

        await self.wait_clocks('aclk', 2)


    async def main_loop(self):
        self.main_loop_count += 1
        self.log.info(f"main_loop called {self.main_loop_count} times")

        max_burst_size = self.axi_master.write_if.max_burst_size

        # write_read tests
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 0, 0]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave.delay_crand = DelayRandomizer(apb_slv_constraints)
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)

        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [3, 3, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave.delay_crand = DelayRandomizer(apb_slv_constraints)
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)


@cocotb.test()
async def axi2apb_shim_test(dut):
    tb = Axi2ApbTB(dut)
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

# @pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width", [(8,32,8,1,12,8),(8,32,16,1,12,8),(8,32,32,1,12,8),(8,32,64,1,12,8)])
@pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width", [(8,32,8,1,12,8)])
def test_axi2abp_shim(request, id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width):
    dut_name = "axi2apb_shim"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir,     "counter_bin.sv"),
        os.path.join(rtl_dir,     "fifo_control.sv"),
        os.path.join(rtl_axi_dir, "axi_fifo_sync.sv"),
        os.path.join(rtl_axi_dir, "axi_skid_buffer.sv"),
        os.path.join(rtl_axi_dir, "axi_gen_addr.sv"),
        os.path.join(rtl_axi_dir, "axi_slave_rd_stub.sv"),
        os.path.join(rtl_axi_dir, "axi_slave_wr_stub.sv"),
        os.path.join(rtl_axi_dir, "axi_slave_stub.sv"),
        os.path.join(rtl_axi_dir, "axi2apb_convert.sv"),
        os.path.join(rtl_axi_dir, "apb_master_stub.sv"),
        os.path.join(rtl_axi_dir, f"{dut_name}.sv")
    ]
    includes = []
    parameters = {
        'AXI_ID_WIDTH':   id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': user_width,
        'APB_ADDR_WIDTH': apb_addr_width,
        'APB_DATA_WIDTH': apb_data_width,
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
