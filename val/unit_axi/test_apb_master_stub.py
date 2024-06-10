import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb.queue import Queue
from cocotb.utils import get_sim_time
import os
import subprocess
import random
import math
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase
from ConstrainedRandom import ConstrainedRandom
from APB import APBMonitor, APBSlave, APBCommandPacket

class APBMasterStub_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '0'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.CMD_PACKET_WIDTH = self.ADDR_WIDTH + self.DATA_WIDTH + self.STRB_WIDTH + 4  # addr, data, strb, prot, pwrite
        self.RESP_PACKET_WIDTH = self.DATA_WIDTH + 2  # data, resp
        cocotb.start_soon(Clock(dut.aclk, 2, units="ns").start())
        self.registers = 32 * self.STRB_WIDTH
        self.clog2_registers = math.ceil(math.log2(self.registers))
        self.slave_register = list(range(self.registers))
        self.apb_monitor = APBMonitor(dut, 'm_apb', 'aclk')
        self.apb_slave = APBSlave(dut, 'm_apb', 'aclk', registers=self.slave_register)
        self.cmd_queue = Queue()

        # Constrained random settings for command generation
        self.pwrite_constraints = [(0, 0), (1, 1)]
        self.pwrite_weights     = [1, 0]
        min_high = (4  * self.STRB_WIDTH)-1
        max_low  = (4  * self.STRB_WIDTH)
        max_high = (32 * self.STRB_WIDTH)-1
        self.paddr_constraints  = [(0, min_high), (max_low, max_high)]
        self.paddr_weights      = [3, 1]
        self.pprot_constraints  = [(0, 0), (1, 7)]
        self.pprot_weights      = [4, 1]

        # Constrained random settings for response generation
        self.cmd_valid_crand = ConstrainedRandom([(0, 0), (1, 1), (2, 10)], [5, 2, 1])
        self.rsp_ready_crand = ConstrainedRandom([(0, 0), (1, 1), (2, 10)], [5, 2, 1])

    async def reset_dut(self):
        self.log.debug('Starting reset_dut')
        self.dut.aresetn.value = 0
        self.dut.i_cmd_valid.value = 0
        self.dut.i_cmd_data.value = 0
        self.dut.i_rsp_ready.value = 0
        await self.apb_slave.reset_bus()
        await self.wait_clocks('aclk', 2)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        self.log.debug('Ending reset_dut')

    async def response_handler(self):
        response_count = 0
        while True:
            self.dut.i_rsp_ready.value = 0
            rand_delay = self.rsp_ready_crand.next()
            for _ in range(rand_delay):
                await self.wait_clocks('aclk', 1)
            self.dut.i_rsp_ready.value = 1
            if self.dut.o_rsp_valid.value:
                response_count += 1
                self.log.debug(f'{response_count=}')
                cmd_packet = self.cmd_queue.get_nowait()
                transaction = self.apb_monitor.transaction_queue.get_nowait()
                response = self.dut.o_rsp_data.value.integer

                # Un-bundling the response
                response_pslverr = (response >> self.DATA_WIDTH) & 0x1
                response_prdata = response & ((1 << self.DATA_WIDTH) - 1)

                self.log.debug('Command Queue Command:')
                cmd_packet.log_packet()
                self.log.debug('Transaction Removed:')
                self.apb_monitor.print(transaction)
                assert transaction.direction == cmd_packet.direction, \
                    f"Direction mismatch: Expected {cmd_packet.direction}, Actual {transaction.direction}"
                assert transaction.address == cmd_packet.paddr, \
                    f"Address mismatch: Expected 0x{cmd_packet.paddr:08X}, Actual 0x{transaction.address:08X}"
                assert transaction.prot == cmd_packet.pprot, \
                    f"PPROT mismatch: Expected {cmd_packet.pprot}, Actual {transaction.prot}"
                assert transaction.error == response_pslverr, \
                    f"PSLVERR mismatch: Expected {response_pslverr}, Actual {transaction.error}"

                if transaction.direction == "READ":
                    expected_data = transaction.data
                    assert response_prdata == expected_data, \
                        f"Data mismatch: Expected 0x{expected_data:08X}, Got 0x{response_prdata:08X}"

            await self.wait_clocks('aclk', 1)


    async def main_loop(self):
        self.log.debug('Starting main_loop')
        cocotb.start_soon(self.apb_monitor.monitor())
        self.log.debug('Starting main_loop start response_handler')
        cocotb.start_soon(self.response_handler())
        self.log.debug('Starting main_loop start driver')
        cocotb.start_soon(self.apb_slave.driver())
        self.log.debug('Starting main_loop completed start driver')

        # Randomly mixed read/write operations
        for i in range(20):
            self.log.debug(f'Mixed Loop {i}')
            rand_delay = self.cmd_valid_crand.next()
            self.dut.i_cmd_valid.value = 0
            for _ in range(rand_delay):
                await self.wait_clocks('aclk', 1)

            self.dut.i_cmd_valid.value = 1
            while not self.dut.o_cmd_ready.value:
                await self.wait_clocks('aclk', 1)

            cmd_packet = APBCommandPacket(
                data_width         = self.DATA_WIDTH,
                addr_width         = self.ADDR_WIDTH,
                strb_width         = self.STRB_WIDTH,
                log                = self.log,
                pwrite_constraints = self.pwrite_constraints,
                pwrite_weights     = self.pwrite_weights,
                paddr_constraints  = self.paddr_constraints,
                paddr_weights      = self.paddr_weights,
                pprot_constraints  = self.pprot_constraints,
                pprot_weights      = self.pprot_weights
            )
            cmd_packet.start_time = get_sim_time('ns')
            cmd_packet.count = i+1
            cmd_packet.log_packet()

            self.dut.i_cmd_data.value = cmd_packet.pack_cmd_packet()
            await self.wait_clocks('aclk', 1)

            self.cmd_queue.put_nowait(cmd_packet)

            self.apb_slave.dump_registers()

        self.dut.i_cmd_valid.value = 0
        await self.wait_clocks('aclk', 50)

@cocotb.test()
async def apb_master_stub_test(dut):
    tb = APBMasterStub_TB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.reset_dut()
    await tb.main_loop()
    tb.log.info("Test completed successfully.")

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__))
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common'))
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi'))

@pytest.mark.parametrize("data_width, addr_width", [(32, 32)])
def test_apb_master_stub(request, data_width, addr_width):
    dut_name = "apb_master_stub"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, "counter_bin.sv"),
        os.path.join(rtl_dir, "fifo_control.sv"),
        os.path.join(rtl_axi_dir, "axi_fifo_sync.sv"),
        os.path.join(rtl_axi_dir, "axi_skid_buffer.sv"),
        os.path.join(rtl_axi_dir, f"{dut_name}.sv")
    ]
    includes = []
    parameters = {
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': addr_width,
    }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )
