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
from DelayRandomizer import DelayRandomizer
from ConstrainedRandom import ConstrainedRandom
from APB import APBTransaction, APBMonitor, APBSlave
from APBTransactionExtra import APBTransactionExtra as APBTransaction

class APBMasterStub_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '0'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.CMD_PACKET_WIDTH = self.ADDR_WIDTH + self.DATA_WIDTH + self.STRB_WIDTH + 4  # addr, data, strb, prot, pwrite
        self.RESP_PACKET_WIDTH = self.DATA_WIDTH + 2  # data, resp
        self.registers = 32 * self.STRB_WIDTH
        self.slave_register = list(range(self.registers))
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 0, 0]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_monitor = APBMonitor(dut, 'm_apb', dut.aclk, bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH)
        self.apb_slave   = APBSlave(dut, 'm_apb', dut.aclk, registers=self.slave_register,
                                    bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH,
                                    constraints=apb_slv_constraints)
        self.cmd_queue = Queue()

        # Constrained random settings for command generation
        addr_min_hi = (4  * self.STRB_WIDTH)-1
        addr_max_lo = (4  * self.STRB_WIDTH)
        addr_max_hi = (32 * self.STRB_WIDTH)-1
        self.apb_cmd_constraints = {
            'last':   ([(0, 0), (1, 1)],
                        [1, 1]),
            'first':  ([(0, 0), (1, 1)],
                        [1, 1]),
            'pwrite': ([(0, 0), (1, 1)],
                        [1, 1]),
            'paddr':  ([(0, addr_min_hi), (addr_max_lo, addr_max_hi)],
                        [4, 1]),
            'pstrb':  ([(15, 15), (0, 14)],
                        [4, 1]),
            'pprot':  ([(0, 0), (1, 7)],
                        [4, 1])
        }

        # Constrained random settings for response generation
        self.cmd_valid_crand = ConstrainedRandom([(0, 0), (1, 1), (2, 10)], [5, 0, 0])
        self.rsp_ready_crand = ConstrainedRandom([(0, 0), (1, 1), (2, 10)], [5, 0, 0])


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
            if self.dut.o_rsp_valid.value:
                rand_delay = self.rsp_ready_crand.next()
                for _ in range(rand_delay):
                    await self.wait_clocks('aclk', 1)
                self.dut.i_rsp_ready.value = 1
                response_count += 1
                self.log.debug(f'{response_count=}')
                cmd_packet = self.cmd_queue.get_nowait()
                mon_packet = self.apb_monitor._recvQ.popleft()
                response = self.dut.o_rsp_data.value.integer

                # Un-bundling the response
                response_pslverr = (response >> self.DATA_WIDTH) & 0x1
                response_prdata = response & ((1 << self.DATA_WIDTH) - 1)
                cmd_packet.pslverr = response_pslverr
                if cmd_packet.direction == 'READ':
                    cmd_packet.prdata = response_prdata
                assert cmd_packet == mon_packet, \
                    f'cmd_packet:\n{cmd_packet}\n' +\
                    f'mon_packet:\n{mon_packet}\n'

            await self.wait_clocks('aclk', 1)


    async def main_loop(self):
        self.log.debug('Starting main_loop')
        self.log.debug('Starting main_loop start response_handler')
        cocotb.start_soon(self.response_handler())
        cmd_packet = APBTransaction(
                data_width         = self.DATA_WIDTH,
                addr_width         = self.ADDR_WIDTH,
                strb_width         = self.STRB_WIDTH,
                constraints        = self.apb_cmd_constraints
        )
        # Randomly mixed read/write operations
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 0, 0]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave.delay_crand = DelayRandomizer(apb_slv_constraints)
        for i in range(200):
            self.log.debug(f'Mixed Loop {i}')
            rand_delay = self.cmd_valid_crand.next()
            self.log.debug(f'main_loop: {rand_delay=}')
            self.dut.i_cmd_valid.value = 0
            for _ in range(rand_delay):
                await self.wait_clocks('aclk', 1)

            self.dut.i_cmd_valid.value = 1

            transaction = cmd_packet.set_constrained_random()
            transaction.start_time = get_sim_time('ns')
            transaction.count = i+1
            lines = transaction.formatted(self.ADDR_WIDTH, self.DATA_WIDTH, self.STRB_WIDTH).splitlines()
            for line in lines:
                self.log.debug(line)

            self.dut.i_cmd_data.value = cmd_packet.pack_cmd_packet()

            while not self.dut.o_cmd_ready.value:
                self.log.debug('waiting for o_cmd_ready')
                await self.wait_clocks('aclk', 1)

            await self.wait_clocks('aclk', 1)

            self.cmd_queue.put_nowait(transaction)
            self.apb_slave.dump_registers()

        self.dut.i_cmd_valid.value = 0
        await self.wait_clocks('aclk', 50)

        # Randomly mixed read/write operations
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [3, 3, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave.delay_crand = DelayRandomizer(apb_slv_constraints)
        for i in range(200):
            self.log.debug(f'Mixed Loop {i}')
            rand_delay = self.cmd_valid_crand.next()
            self.log.debug(f'main_loop: {rand_delay=}')
            self.dut.i_cmd_valid.value = 0
            for _ in range(rand_delay):
                await self.wait_clocks('aclk', 1)

            self.dut.i_cmd_valid.value = 1

            transaction = cmd_packet.set_constrained_random()
            transaction.start_time = get_sim_time('ns')
            transaction.count = i+1
            lines = transaction.formatted(self.ADDR_WIDTH, self.DATA_WIDTH, self.STRB_WIDTH).splitlines()
            for line in lines:
                self.log.debug(line)

            self.dut.i_cmd_data.value = cmd_packet.pack_cmd_packet()

            while not self.dut.o_cmd_ready.value:
                self.log.debug('waiting for o_cmd_ready')
                await self.wait_clocks('aclk', 1)

            await self.wait_clocks('aclk', 1)

            self.cmd_queue.put_nowait(transaction)
            self.apb_slave.dump_registers()

        self.dut.i_cmd_valid.value = 0
        await self.wait_clocks('aclk', 50)

@cocotb.test()
async def apb_master_stub_test(dut):
    tb = APBMasterStub_TB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.start_clock('aclk', 10, 'ns')
    await tb.reset_dut()
    await tb.main_loop()
    # await tb.wait_clocks('aclk', 50)
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
