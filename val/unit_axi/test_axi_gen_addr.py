import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import os
import subprocess
import random
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase

class AxiGenAddr_TB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.aw = self.convert_to_int(os.environ.get('PARAM_AW', '0'))
        self.dw = self.convert_to_int(os.environ.get('PARAM_DW', '0'))
        self.odw = self.convert_to_int(os.environ.get('PARAM_ODW', '0'))
        self.len_sz = self.convert_to_int(os.environ.get('PARAM_LEN_SZ', '0'))

    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    AW:     {self.aw}')
        self.log.info(f'    DW:     {self.dw}')
        self.log.info(f'    ODW:    {self.odw}')
        self.log.info(f'    LEN_SZ: {self.len_sz}')
        self.log.info('-------------------------------------------')

    async def clear_interface(self):
        self.dut.i_curr_addr.value = 0
        self.dut.i_size.value = 0
        self.dut.i_burst.value = 0
        self.dut.i_len.value = 0


    @staticmethod
    def clog2(val):
        return (val - 1).bit_length()


    async def main_loop(self, seed):
        # Define the test scenarios
        test_scenarios = [
            {"name": "FIXED_BURST", "burst": 0},
            {"name": "INCR_BURST", "burst": 1},
            {"name": "WRAP_BURST", "burst": 2},
        ]

        # Define the address locations within a 4KB boundary
        address_locations = [
            {"name": "BOTTOM", "offset": 0},
            {"name": "MIDDLE", "offset": 2048},
            {"name": "TOP", "offset": 4095},
        ]

        # Define the size and length combinations
        size_length_combinations = [
            {"size": 0, "len": 0},
            {"size": 0, "len": 1},
            {"size": 0, "len": 2},
            {"size": 0, "len": 4},
            {"size": 0, "len": 8},
            {"size": 0, "len": 255},
            {"size": 1, "len": 0},
            {"size": 1, "len": 1},
            {"size": 1, "len": 2},
            {"size": 1, "len": 4},
            {"size": 1, "len": 8},
            {"size": 1, "len": 255},
            {"size": 2, "len": 0},
            {"size": 2, "len": 1},
            {"size": 2, "len": 2},
            {"size": 2, "len": 4},
            {"size": 2, "len": 8},
            {"size": 2, "len": 255},
            {"size": 3, "len": 0},
            {"size": 3, "len": 1},
            {"size": 3, "len": 2},
            {"size": 3, "len": 4},
            {"size": 3, "len": 8},
            {"size": 3, "len": 255},
            {"size": 4, "len": 0},
            {"size": 4, "len": 1},
            {"size": 4, "len": 2},
            {"size": 4, "len": 4},
            {"size": 4, "len": 8},
            {"size": 4, "len": 255},
            {"size": 5, "len": 0},
            {"size": 5, "len": 1},
            {"size": 5, "len": 2},
            {"size": 5, "len": 4},
            {"size": 5, "len": 8},
            {"size": 5, "len": 255},
            {"size": 6, "len": 0},
            {"size": 6, "len": 1},
            {"size": 6, "len": 2},
            {"size": 6, "len": 4},
            {"size": 6, "len": 8},
            {"size": 6, "len": 255},
            {"size": 7, "len": 0},
            {"size": 7, "len": 1},
            {"size": 7, "len": 2},
            {"size": 7, "len": 4},
            {"size": 7, "len": 8},
            {"size": 7, "len": 255},
        ]

        # Initialize the base address
        base_address = 0

        # Iterate over the test scenarios
        for scenario in test_scenarios:
            burst = scenario["burst"]

            # Iterate over the address locations
            for location in address_locations:
                offset = location["offset"]

                # Iterate over the size and length combinations
                for combination in size_length_combinations:
                    size = combination["size"]
                    len_val = combination["len"]

                    # Calculate the current address
                    curr_addr = base_address | offset

                    # Apply the inputs to the DUT
                    self.dut.i_curr_addr.value = curr_addr
                    self.dut.i_size.value = size
                    self.dut.i_burst.value = burst
                    self.dut.i_len.value = len_val

                    await self.wait_time(10, 'ns')

                    # Calculate the expected next address
                    increment_pre = int(1 << size)
                    odw_bytes = self.odw // 8
                    if self.odw == self.dw:
                        increment = increment_pre
                    else:
                        increment = min(increment_pre, odw_bytes)
                    wrap_mask = (1 << (size + self.clog2(len_val + 1))) - 1
                    aligned_addr = (curr_addr + increment) & ~(increment - 1)
                    wrap_addr = (curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask)

                    if burst == 0:  # FIXED burst
                        expected_next_addr = curr_addr
                    elif burst == 1:  # INCR burst
                        expected_next_addr = curr_addr + increment
                    else:  # WRAP burst
                        expected_next_addr = wrap_addr

                    # Check the actual next address against the expected value
                    actual_next_addr = self.dut.ow_next_addr.value

                    # Print the test case information
                    self.log.info(f"Test Case: {scenario['name']}_{location['name']}_SIZE_{size}_LEN_{len_val}")
                    self.log.info(f"  Current Address: {hex(curr_addr)}")
                    self.log.info(f"  Size: {size}")
                    self.log.info(f"  Burst: {burst}")
                    self.log.info(f"  Length: {len_val}")
                    self.log.info(f"  Expected Next Address: {hex(expected_next_addr)}")
                    self.log.info(f"  Actual Next Address: {hex(actual_next_addr)}")
                    assert actual_next_addr == expected_next_addr, f"Error: Expected next address {hex(expected_next_addr)}, but got {hex(actual_next_addr)}"
                    self.log.info("  Test Passed\n")

                # Increment the base address for the next iteration
                base_address += 0x10000

@cocotb.test()
async def axi_addr_gen_test(dut):
    tb = AxiGenAddr_TB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(10, 'ns')
    await tb.main_loop(seed)
    await tb.wait_time(10, 'ns')
    tb.log.info("Test completed successfully.")


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed
rtl_axi_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'axi')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("aw, dw, odw, len_sz", [(32, 32, 32, 8), (32, 32, 8, 8)])
def test_axi_gen_addr(request, aw, dw, odw, len_sz):
    dut_name = "axi_gen_addr"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_axi_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {"AW":aw, "DW":dw, 'LEN':len_sz, "ODW":odw}

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
