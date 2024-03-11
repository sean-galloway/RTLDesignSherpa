import cocotb
from cocotb.triggers import Timer
# from cocotb.regression import TestFactory
import os
import subprocess
import random
import os
import subprocess
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase


class AddHierTB(TBBase):
    
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.C = self.convert_to_int(os.environ.get('PARAM_C', '0'))
        self.max_val = 2**(self.N)
        self.max_value_N = 2**self.N


    async def clear_interface(self):
        for i in range(self.C):
            self.dut.i_numbers[i] = 0


    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    N:     {self.N}')
        self.log.info('-------------------------------------------')


    async def main_loop(self, count=256):
        for _ in range(100):
            # Create and drive random numbers
            input_data = [random.randint(0, self.max_val) for _ in range(self.C)]
            for i, val in enumerate(input_data):
                self.dut.i_numbers[i].value = val
            
            # Calculate expected sum
            expected_sum = sum(input_data)
            expected_sum = (expected_sum % self.max_value_N)

            await self.wait_time(2, 'ns')
            
            # Check the result
            assert int(self.dut.ow_sum) == expected_sum,\
                f"Mismatch detected: Expected {expected_sum}, got {int(self.dut.ow_sum)}, list={input_data}"


@cocotb.test
async def adder_test(dut):
    """ Test math_adder_hierarchical with random values """
    tb = AddHierTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(2, 'ns')
    await tb.main_loop()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n, c", [(16, 6), (8, 5), (4, 8)])
def test_math_adder_hierarchical(request, n, c):
    dut_name = "math_adder_hierarchical"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_hierarchical"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_carry_lookahead.sv"),
        os.path.join(rtl_dir, "math_adder_hierarchical.sv"),
    ]
    includes = []
    parameters = {'N':n,'C':c, }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
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
