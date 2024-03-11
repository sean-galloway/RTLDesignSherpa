import cocotb
import itertools
from cocotb.triggers import Timer

# from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import random
from TBBase import TBBase


class AddSubTB(TBBase):
    
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.max_val = 2**self.N


    async def clear_interface(self):
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_c.value = 0


    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    N:     {self.N}')
        self.log.info('-------------------------------------------')


    async def main_loop(self, count=256):
        if self.max_val < count:
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            a_list = [random.randint(0, self.max_val) for _ in range(count)]
            b_list = [random.randint(0, self.max_val) for _ in range(count)]

        # Test the adder/subtractor
        for a, b, cin in itertools.product(a_list, b_list, range(2)):

            # Apply test inputs
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            self.dut.i_c.value = cin

            # Wait for a simulation time to ensure values propagate
            await self.wait_time(2, 'ns')

            # Check if the operation is addition or subtraction
            if cin == 0:
                expected_sum = a + b
                expected_c = 1 if expected_sum >= (self.max_val) else 0
                expected_sum = expected_sum % (self.max_val)
            else:
                expected_sum = a - b
                if expected_sum < 0:
                    expected_sum += (self.max_val)
                    expected_c = 0
                else:
                    expected_c = 1
            found = self.dut.ow_sum.value.integer
            self.log.info(f'{self.max_val=} {a=} {b=} {cin=} {expected_sum=} {found=}')
            # Check results
            assert self.dut.ow_sum.value.integer == expected_sum,\
                f"For inputs {a} and {b} with carry-in {cin}, expected sum was {expected_sum} but got {self.dut.ow_sum.value.integer}"
            assert self.dut.ow_carry.value == expected_c,\
                f"For inputs {a} and {b} with carry-in {cin}, expected carry/borrow was {expected_c} but got {self.dut.ow_carry.value}"


@cocotb.test()
async def addsub_dut_test(dut):
    """Test logic for a specific set of input values."""
    tb = AddSubTB(dut)
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

@pytest.mark.parametrize("n", [4, 8, 12])
def test_math_addsub_full_nbit(request, n):
    dut_name = "math_addsub_full_nbit"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_addsub_full_nbit"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_full.sv"),
        os.path.join(rtl_dir, "math_addsub_full_nbit.sv"),
    ]
    includes = []
    parameters = {'N':n, }

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
