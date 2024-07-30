import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.clock import Clock
import os
import subprocess
import random
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase


class CheckSumTB(TBBase):
    
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.WIDTH = self.convert_to_int(os.environ.get('PARAM_WIDTH', '0'))
        self.max_value = 2**self.WIDTH-1
        self.mask = (1 << self.WIDTH)-1
        self.log.info(f'{self.max_value=}')

    async def clear_interface(self):
        self.dut.i_reset.value = 0
        self.dut.i_valid.value = 0
        self.dut.i_data.value = 0


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        self.clear_interface()


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    WIDTH:  {self.WIDTH}')
        self.log.info('-------------------------------------------')

    async def main_loop(self, count=100):
        for _ in range(10):  # Perform 10 sets of checks
            # Generate a random burst length between 8 and 24
            burst_length = random.randint(8, 24)
            total = 0
            total_list = []

            # Drive the burst of data
            for _ in range(burst_length):
                data = random.randint(0, self.max_value)
                total += data
                total_list.append(data)
                
                self.dut.i_data.value = data
                self.dut.i_valid.value = 1
                await self.wait_clocks('i_clk',1)

            # Check the checksum
            self.dut.i_valid.value = 0  # Deassert i_valid after the burst
            self.dut.i_data.value = 0
            await self.wait_clocks('i_clk',1)            
            actual_chksum = int(self.dut.o_chksum.value)
            expected_chksum = total & self.mask
            self.log.info(f'{total=:x} {actual_chksum=:x} {expected_chksum=:x}')
            hex_values = ' '.join(f"{num:x}" for num in total_list)
            self.log.info(f'{hex_values=}')
            assert actual_chksum == expected_chksum, f"Checksum mismatch: expected {expected_chksum}, got {actual_chksum} {total_list=}"

            # Assert i_reset for two clocks while i_valid is 0
            self.dut.i_reset = 1
            await self.wait_clocks('i_clk',2)
            self.dut.i_reset = 0
            await self.wait_clocks('i_clk',20)


@cocotb.test()
async def checksum_test(dut):
    """Test the checksum module with random data bursts."""
    tb = CheckSumTB(dut)
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
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [4,8,12,16])
def test_dataint_checksum(request, width):
    dut_name = "dataint_checksum"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_checksum"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_checksum.sv"),
    ]
    includes = []
    parameters = {'WIDTH':width, }

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
