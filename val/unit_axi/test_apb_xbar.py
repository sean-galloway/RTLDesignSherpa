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
from APB import APBTransaction, APBMonitor, APBSlave, APBMaster

class APBXbar_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.M = 5
        self.S = 3
        self.ADDR_WIDTH = 32
        self.DATA_WIDTH = 32
        self.STRB_WIDTH = 8
        self.SLAVE_ENABLE = [1, 1, 1, 1, 1]
        self.SLAVE_ADDR_BASE  = [  0x0, 0x1000, 0x2000, 0x3000, 0x4000] 
        self.SLAVE_ADDR_LIMIT = [0xFFF, 0x1FFF, 0x2FFF, 0x3FFF, 0x4FFF]

        self.registers = 32 * self.STRB_WIDTH
        self.slave_register = list(range(self.registers))

        # Create the Monitors
        self.apb_master_mon = []
        self.apb_slave_mon = []
        for i in range(self.M):
            mon = APBMonitor(dut, f'm{i}_apb', dut.aclk, bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH)
            self.apb_master_mon.append(mon)
        for i in range(self.S):
            mon = APBMonitor(dut, f's{i}_apb', dut.aclk, bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH)
            self.apb_slave_mon.append(mon)

        # Create the Slaves
        apb_slv_constraints = {
                'ready': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
                'error': ([[0, 0], [1, 1]], [10, 0]),
        }
        self.apb_slave = []
        for i in range(self.S):
            slave   = APBSlave(dut, f's{i}_apb', dut.aclk, registers=self.slave_register,
                                    bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH,
                                    constraints=apb_slv_constraints)
            self.apb_slave.append(slave)
        
        apb_mst_constraints = {
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 2, 1]),
            'penable': ([[0, 0], [1, 2]], [4, 1]),
        }
        self.apb_master = []
        for i in range(self.M):
            master   = APBSlave(dut, f'm{i}_apb', dut.aclk,
                                    bus_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH,
                                    constraints=apb_mst_constraints)
            self.apb_master.append(master)


    async def reset_dut(self):
        self.log.debug('Starting reset_dut')
        self.dut.aresetn.value = 0
        for i in range(self.M):
            self.apb_master[i].reset_bus()
        for i in range(self.S):
            self.apb_slave[i].reset_bus()
        await self.wait_clocks('aclk', 2)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        self.log.debug('Ending reset_dut')


@cocotb.test()
async def apb_xbar_wrap_test(dut):
    tb = APBXbar_TB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    await tb.start_clock('aclk', 10, 'ns')
    await tb.reset_dut()
    # await tb.main_loop()
    await tb.wait_clocks('aclk', 50)
    tb.log.info("Test completed successfully.")

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__))
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common'))
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi/'))
rtl_integ_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'integ_axi/apb_xbar'))

@pytest.mark.parametrize()
def test_apb_xbar_wrap(request):
    dut_name = "apb_xbar_wrap"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_axi_dir, "apb_xbar.sv"),
        os.path.join(rtl_integ_axi_dir, f"{dut_name}.sv")
    ]
    includes = []

    parameters = {
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
