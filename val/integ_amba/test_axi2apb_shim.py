import os
import itertools
import logging
import os
import random
import subprocess

import pytest
import cocotb
import cocotb.triggers
from cocotb_test.simulator import run
from cocotb.clock import Clock
from cocotbext.axi import AxiBus, AxiMaster

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_slave, create_apb_monitor

from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd


class Axi2ApbTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.log = self.configure_logging(level=logging.DEBUG)
        self.log.info('Starting Axi2ApbTB')
        self.DATA_WIDTH      = self.convert_to_int(os.environ.get('TEST_AXI_DATA_WIDTH', '0'))
        self.APB_ADDR_WIDTH  = self.convert_to_int(os.environ.get('TEST_APB_ADDR_WIDTH', '0'))
        self.APB_DATA_WIDTH  = self.convert_to_int(os.environ.get('TEST_APB_DATA_WIDTH', '0'))
        self.strb_bits       = self.DATA_WIDTH // 8
        self.APB_STRB_WIDTH  = self.APB_DATA_WIDTH // 8
        with open("debug_log.txt", "a") as debug_file:
            debug_file.write(f'Axi2ApbTB:: {self.DATA_WIDTH=} {self.APB_ADDR_WIDTH=} {self.APB_DATA_WIDTH=}\n')

        self.debug           = True
        bus                  = AxiBus.from_prefix(dut, "s_axi")
        self.axi_master      = AxiMaster(bus, dut.aclk, dut.aresetn, reset_active_level=False)
        self.registers       = 32 * self.strb_bits
        self.slave_register  = list(range(self.registers))

        # Set up randomizers
        self.apb_slave_randomizer = FlexRandomizer({
            'ready': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
            'error': ([(0, 0), (1, 1)], [10, 0])
        })

        # Configure APB components
        self.apb_monitor = create_apb_monitor(
            dut,
            'APB Monitor',
            'm_apb',
            dut.pclk,
            addr_width=self.APB_ADDR_WIDTH,
            data_width=self.APB_DATA_WIDTH,
            log=self.log
        )

        self.apb_slave = create_apb_slave(
            dut,
            'APB Slave',
            'm_apb',
            dut.pclk,
            registers=[0] * (self.registers * self.APB_STRB_WIDTH),
            addr_width=self.APB_ADDR_WIDTH,
            data_width=self.APB_DATA_WIDTH,
            randomizer=self.apb_slave_randomizer,
            log=self.log
        )

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
        self.dut.presetn.value = 0
        await self.apb_slave.reset_bus()
        await self.wait_clocks('pclk', 2)
        self.dut.aresetn.value = 1
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 2)
        self.log.info("Reset Done.")

    def cycle_pause(self):
        return itertools.cycle([1, 1, 1, 0])

    async def run_test_write_read(self, idle_inserter=None, backpressure_inserter=None, size=None):
        # sourcery skip: move-assign
        msg = f'run test write/read: {size=}'
        self.log.info(msg)
        max_burst_size = self.axi_master.write_if.max_burst_size
        length = int(self.registers/(self.DATA_WIDTH/self.APB_DATA_WIDTH))
        # length = 10

        if size is None:
            # size = int(max_burst_size / (self.DATA_WIDTH/self.APB_DATA_WIDTH))
            size = max_burst_size

        self.set_idle_generator(idle_inserter)
        self.set_backpressure_generator(backpressure_inserter)

        for addr in range(length):
            test_data = bytearray([x % 256 for x in range(length)])
            msg = f"run_test_write/write(AXI-wr): offset {addr}, size {size}, data {[f'{x:02X}' for x in test_data]}"
            self.log.info(msg)
            await self.axi_master.write(addr, test_data, size=size)
            await self.wait_clocks('aclk', 100)
            if self.debug:
                self.apb_slave.dump_registers()

            data = await self.axi_master.read(addr, length, size=size)
            msg = f"run_test_write/read(AXI-rd): offset {addr}, size {size}, length {length} data {[f'{x:02X}' for x in test_data]}"
            self.log.info(msg)

            data_ba = self.convert_to_bytearray(data.data)
            data_in_hex = self.bytearray_to_hex_strings([data_ba])
            msg = f'Read  Data: {data_in_hex}'
            self.log.info(msg)

            data_bk_ba = self.convert_to_bytearray(test_data)
            data_bk_hex = self.bytearray_to_hex_strings([data_bk_ba])
            msg = f'Write Data: {data_bk_hex}'
            self.log.info(msg)

            assert data.data == test_data
            await self.wait_clocks('aclk', 100)

        await self.wait_clocks('aclk', 2)


    async def main_loop(self):
        self.main_loop_count += 1
        msg = f"main_loop called {self.main_loop_count} times"
        self.log.info(msg)

        max_burst_size = self.axi_master.write_if.max_burst_size

        # write_read tests
        apb_slv_constraints = {
                'ready': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0]),
                'error': ([(0, 0), (1, 1)], [10, 0]),
        }
        self.apb_slave.set_randomizer(FlexRandomizer(apb_slv_constraints))
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)

        apb_slv_constraints = {
                'ready': ([(0, 0), (1, 5), (6, 10)], [3, 3, 1]),
                'error': ([(0, 0), (1, 1)], [10, 0]),
        }
        self.apb_slave.set_randomizer(FlexRandomizer(apb_slv_constraints))
        for idle in [None, self.cycle_pause]:
            for backpressure in [None, self.cycle_pause]:
                for bsize in [None]+list(range(max_burst_size)):
                    await self.run_test_write_read(idle_inserter=idle, backpressure_inserter=backpressure, size=bsize)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi2apb_shim_test(dut):
    tb = Axi2ApbTB(dut)
    cocotb.start_soon(Clock(dut.aclk,  1, units="ns").start())
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.cycle_reset()
    await tb.wait_clocks('aclk', 2)
    await tb.main_loop()
    await tb.wait_clocks('aclk', 2)
    tb.done = True
    tb.log.info("Test completed successfully.")


# @pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width", [(8,32,8,1,12,8),(8,32,16,1,12,8),(8,32,32,1,12,8),(8,32,64,1,12,8)])
@pytest.mark.parametrize("id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width", [(8,32,8,1,12,8)])
def test_axi2abp_shim(request, id_width, addr_width, data_width, user_width, apb_addr_width, apb_data_width):

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba': 'rtl/amba',
        })

    dut_name = "axi4_to_apb_shim"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], "shared/cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "apb/apb_master_stub.sv"),

        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_fifo_sync.sv"),

        os.path.join(rtl_dict['rtl_amba'], "shared/axi_gen_addr.sv"),
        os.path.join(rtl_dict['rtl_amba'], "shims/axi4_to_apb_convert.sv"),

        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi_slave_wr_stub.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi_slave_rd_stub.sv"),
        os.path.join(rtl_dict['rtl_amba'], "axi4/stubs/axi_slave_stub.sv"),

        os.path.join(rtl_dict['rtl_amba'], f"shims/{dut_name}.sv")
    ]

    # create a human readable test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(data_width, 3)
    aaw_str = TBBase.format_dec(apb_addr_width, 3)
    adw_str = TBBase.format_dec(apb_data_width, 3)
    test_name_plus_params = f"test_{dut_name}_aw{aw_str}_dw{dw_str}_uw{uw_str}_aaw{aaw_str}_adw{adw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it int he simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH':   str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'APB_ADDR_WIDTH': str(apb_addr_width),
        'APB_DATA_WIDTH': str(apb_data_width),
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        # 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749) # str(random.randint(0, 100000))
    }

    extra_env = {f'TEST_{k}': str(v) for k, v in rtl_parameters.items()}


    compile_args = [
            "--trace-fst",
            "--trace-structs",
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace-fst",  # Tell Verilator to use FST
            "--trace-structs",
            "--trace-depth", "99",
    ]

    plusargs = [
            "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure