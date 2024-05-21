import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import os
import subprocess
import random
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase
from APB import APBMonitor, APBSlave, APBBase, APBCommandGenerator

class APBMasterStub_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '0'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('PARAM_ADDR_WIDTH', '0'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.CMD_PACKET_WIDTH = self.ADDR_WIDTH + self.DATA_WIDTH + self.STRB_WIDTH + 4  # addr, data, strb, prot, pwrite
        self.RESP_PACKET_WIDTH = self.DATA_WIDTH + 2  # data, resp
        cocotb.start_soon(Clock(dut.aclk, 2, units="ns").start())
        self.registers = 32
        self.slave_register = list(range(self.registers))
        self.apb_monitor = APBMonitor(dut, 'm_apb', 'aclk')
        self.apb_slave = APBSlave(dut, 'm_apb', 'aclk', registers=self.slave_register)
        self.cmd_generator = APBCommandGenerator(self.DATA_WIDTH, self.ADDR_WIDTH, self.STRB_WIDTH)


    async def reset_dut(self):
        self.dut.aresetn.value = 0
        self.dut.i_cmd_valid.value = 0
        self.dut.i_cmd_data.value = 0
        self.dut.i_rsp_ready.value = 0
        await self.apb_slave.reset_bus()
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)


    async def main_loop(self):
        cocotb.start_soon(self.apb_monitor.monitor())
        cocotb.start_soon(self.apb_slave.driver())

        # Test write operations
        for _ in range(10):
            cmd_packet = self.cmd_generator.generate_write_cmd()
            self.dut.i_cmd_valid.value = 1
            self.dut.i_cmd_data.value = cmd_packet
            await RisingEdge(self.dut.aclk)
            while not self.dut.o_cmd_ready.value:
                await RisingEdge(self.dut.aclk)
            self.dut.i_cmd_valid.value = 0
            await RisingEdge(self.dut.aclk)

        # Test read operations
        for _ in range(10):
            cmd_packet = self.cmd_generator.generate_read_cmd()
            self.dut.i_cmd_valid.value = 1
            self.dut.i_cmd_data.value = cmd_packet
            await RisingEdge(self.dut.aclk)
            while not self.dut.o_cmd_ready.value:
                await RisingEdge(self.dut.aclk)
            self.dut.i_cmd_valid.value = 0
            await RisingEdge(self.dut.aclk)

            while not self.dut.o_rsp_valid.value:
                await RisingEdge(self.dut.aclk)
            rsp_data = self.dut.o_rsp_data.value
            # Verify the response data
            await RisingEdge(self.dut.aclk)

        # Test back-to-back read and write operations
        for _ in range(10):
            # Write operation
            cmd_packet = self.cmd_generator.generate_write_cmd()
            self.dut.i_cmd_valid.value = 1
            self.dut.i_cmd_data.value = cmd_packet
            await RisingEdge(self.dut.aclk)
            while not self.dut.o_cmd_ready.value:
                await RisingEdge(self.dut.aclk)
            self.dut.i_cmd_valid.value = 0
            await RisingEdge(self.dut.aclk)

            # Read operation
            cmd_packet = self.cmd_generator.generate_read_cmd()
            self.dut.i_cmd_valid.value = 1
            self.dut.i_cmd_data.value = cmd_packet
            await RisingEdge(self.dut.aclk)
            while not self.dut.o_cmd_ready.value:
                await RisingEdge(self.dut.aclk)
            self.dut.i_cmd_valid.value = 0
            await RisingEdge(self.dut.aclk)

            while not self.dut.o_rsp_valid.value:
                await RisingEdge(self.dut.aclk)
            rsp_data = self.dut.o_rsp_data.value
            # Verify the response data
            await RisingEdge(self.dut.aclk)

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

# @pytest.mark.parametrize("data_width, addr_width", [(32, 32), (64, 32), (128, 32), (64, 12)])
@pytest.mark.parametrize("data_width, addr_width", [(32, 32)])
def test_apb_master_stub(request, data_width, addr_width):
    dut_name = "apb_master_stub"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
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