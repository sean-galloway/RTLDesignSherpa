import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.clock import Clock
import random
import os
import subprocess
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase

class LFSR_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.width = self.convert_to_int(os.environ.get('PARAM_WIDTH', '0'))
        self.total_width = self.width+1
        self.max_val = (2**self.width)-1
        self.tap_index_width = self.convert_to_int(os.environ.get('PARAM_TAP_INDEX_WIDTH', '0'))
        self.tap_count = self.convert_to_int(os.environ.get('PARAM_TAP_COUNT', '0'))
        temp_str = os.environ.get('PARAM_TAPS', '0')
        self.taps = [int(x) for x in temp_str.strip('[]').split(',')]

    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    WIDTH: {self.width}')
        self.log.info(f'    TIW:   {self.tap_index_width}')
        self.log.info(f'    TC:    {self.tap_count}')
        self.log.info(f'    TAPS:  {self.taps}')
        self.log.info('-------------------------------------------')

    async def clear_interface(self):
        self.dut.i_enable.value = 0
        self.dut.i_seed_load.value = 0
        self.dut.i_seed_data.value = 0
        self.dut.i_seed_load.value = 0

    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()
        self.log.info('Assert reset done.')

    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")

    async def set_taps(self):
        concatenated_taps = 0
        for i, tap in enumerate(self.taps):
            concatenated_taps |= tap << (int(i) * self.tap_index_width)
        self.dut.i_taps.value = concatenated_taps

    async def load_seed(self, seed):
        self.dut.i_seed_load.value = 1
        self.dut.i_seed_data.value = seed
        await self.wait_clocks('i_clk', 1)
        self.dut.i_seed_load.value = 0

    async def enable_lfsr(self):
        self.dut.i_enable.value = 1

    async def disable_lfsr(self):
        self.dut.i_enable.value = 0

    async def main_loop(self, seed):
        num_cycles = 100
        expected_lfsr_output = seed  # Initialize with the seed value

        for _ in range(num_cycles):
            lfsr_output = self.dut.o_lfsr_out.value
            lfsr_output_hex = hex(lfsr_output)
            expected_hex = hex(expected_lfsr_output)
            lfsr_done = self.dut.ow_lfsr_done.value
            self.log.info(f"LFSR Output: {lfsr_output_hex}, Expected: {expected_hex}, LFSR Done: {lfsr_done}")

            # Check if the LFSR output matches the expected value
            assert lfsr_output == expected_lfsr_output, f"LFSR output mismatch: Expected {expected_hex}, Got {lfsr_output_hex}"

            await self.wait_clocks('i_clk', 1)  # Wait for the clock edge before updating

            # Update the expected LFSR output for the next cycle
            feedback = expected_lfsr_output & 1  # LSB as feedback

            for tap in self.taps:
                if tap > 0:
                    bit_index = tap - 1  # Adjust tap position by subtracting 1
                    feedback ^= (expected_lfsr_output >> bit_index) & 1

            expected_lfsr_output = ((expected_lfsr_output >> 1) | (feedback << (self.width - 1))) & self.max_val


@cocotb.test()
async def lfsr_test(dut):
    tb = LFSR_TB(dut)
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
    await tb.set_taps()
    seed = random.randint(0, tb.max_val)
    await tb.enable_lfsr()
    await tb.load_seed(seed)
    await tb.main_loop(seed)
    await tb.disable_lfsr()
    await tb.wait_clocks('i_clk', 15)
    tb.log.info("Test completed successfully.")


# Path setup and test parametrization
repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__))
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common'))

@pytest.mark.parametrize("width, tap_index_width, tap_count, taps", [(8, 8, 4, [8,6,5,4]), (16, 8, 4, [16,15,13,4]), (32, 8, 4,[32,22,2,1])])
def test_shifter_lfsr_galois(request, width, tap_index_width, tap_count, taps):
    dut_name = "shifter_lfsr_galois"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {'WIDTH': width, 'TAP_INDEX_WIDTH': tap_index_width, 'TAP_COUNT': tap_count, 'TAPS':taps}

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit_common', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
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