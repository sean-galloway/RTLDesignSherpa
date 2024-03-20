import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer
# from cocotb.regression import TestFactory
import os
import subprocess
import pytest
import random
from cocotb_test.simulator import run
from TBBase import TBBase
from ConstrainedRandom import ConstrainedRandom


class RRArb(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.CLIENTS = self.convert_to_int(os.environ.get('PARAM_CLIENTS', '0'))


    async def clear_interface(self):
        self.dut.i_block_arb.value = 0
        self.dut.i_req.value = 0
        self.log.info('Clearing interface done.')


    async def assert_reset(self):
        self.dut.i_rst_n.value = 0
        await self.clear_interface()
        self.log.info('Assert reset done.')


    async def deassert_reset(self):
        self.dut.i_rst_n.value = 1
        self.log.info("Reset complete.")


    def print_settings(self):
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    CLIENTS:  {self.CLIENTS}')
        self.log.info('-------------------------------------------')


    async def basic_tests(self):
        for i in range(self.CLIENTS):
            self.dut.i_req.value = (1 << i)
            await self.wait_clocks('i_clk', 1)
            assert self.dut.o_gnt.value.integer == (1 << i), f"Expected o_gnt[{i}] to be high"


    async def test_multiple(self):
        for i in range(self.CLIENTS - 1):
            self.dut.i_req.value = (1 << i) | (1 << (i + 1))
            await self.wait_clocks('i_clk', 1)
            assert self.dut.o_gnt.value.integer in [
                1 << i,
                1 << (i + 1),
            ], f"Expected either o_gnt[{i}] or o_gnt[{i + 1}] to be high"


    async def test_all(self):
        num_clients = self.CLIENTS
        self.dut.i_req.value = (1 << num_clients) - 1  # All bits set
        await self.wait_clocks('i_clk', 1)
        
        # ensure only on agent is granted
        granted_clients = [i for i, bit in enumerate(bin(self.dut.o_gnt.value.integer)[2:].zfill(num_clients)) if bit == '1']
        assert len(granted_clients) == 1, "Expected exactly one client to be granted when all request."

        # Now, advance some cycles to observe the round-robin behavior
        previous_grant = granted_clients[0]
        for _ in range(num_clients * 2):  # Go through enough cycles to see a full rotation
            await self.wait_clocks('i_clk', 1)
            self.dut.i_req.value = (1 << num_clients) - 1  # Keep all request active
            await self.wait_clocks('i_clk', 1)

            granted_clients = [i for i, bit in enumerate(bin(self.dut.o_gnt.value.integer)[2:].zfill(num_clients)) if bit == '1']
            assert len(granted_clients) == 1, f"Expected exactly one grant at each cycle, got {len(granted_clients)} grants."
            
            # Check for round-robin progression, which is less strict without internal state knowledge but expects a change.
            assert granted_clients[0] != previous_grant, "Expected a different client to be granted in a round-robin fashion."
            previous_grant = granted_clients[0]


    async def main_loop(self):
        await self.basic_tests()
        await self.test_multiple()
        await self.test_all()


@cocotb.test()
async def arbiter_round_robin_test(dut):
    """Test the round-robin arbiter"""
    tb = RRArb(dut)
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

@pytest.mark.parametrize("clients", [6])
def test_arbiter_round_robin(request, clients):
    dut_name = "arbiter_round_robin"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name   

    verilog_sources = [
        os.path.join(rtl_dir, "find_first_set.sv"),
        os.path.join(rtl_dir, "find_last_set.sv"),
        os.path.join(rtl_dir, "leading_one_trailing_one.sv"),
        os.path.join(rtl_dir, f"{dut_name}.sv"),

    ]
    includes = []
    parameters = {'CLIENTS':clients, }

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
