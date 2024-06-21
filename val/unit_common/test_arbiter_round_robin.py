import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer
from cocotb.queue import Queue
# from cocotb.regression import TestFactory
import os
import subprocess
import pytest
import random
from cocotb_test.simulator import run
from TBBase import TBBase
from ConstrainedRandom import ConstrainedRandom


class ArbiterTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.CLIENTS = int(dut.CLIENTS)
        self.WAIT_GNT_ACK = int(dut.WAIT_GNT_ACK)
        self.pending_reqs = [0] * self.CLIENTS


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


    def random_delay(self, min_clocks=5, max_clocks=15):
        return random.randint(min_clocks, max_clocks)


    async def generate_requests(self, num_cycles=20):
        for _ in range(num_cycles):
            for i in range(self.CLIENTS):
                if self.pending_reqs[i] == 0 and random.random() < 0.5:
                    self.pending_reqs[i] = 1
            self.dut.i_req.value = int("".join(map(str, self.pending_reqs)), 2)
            self.log.debug(f'    New req: {self.dut.i_req}')

            await self.wait_clocks('i_clk', 1)


    async def check_grants(self):
        while True:
            await self.wait_clocks('i_clk', 1)
            if self.dut.o_gnt_valid.value == 1:
                grant_id = int(self.dut.o_gnt_id.value)
                expected_gnt = (1 << grant_id)
                self.log.debug(f'Current req: {self.dut.i_req.value}')
                assert self.dut.o_gnt.value == expected_gnt, f"Expected grant: {expected_gnt}, got: {int(self.dut.o_gnt.value)}"
                assert self.dut.i_req.value & self.dut.o_gnt.value, "Grant should be in response to a request"
                self.log.debug(f'Clearing bit {grant_id}')
                self.log.debug(f'   before: {self.pending_reqs}')
                self.pending_reqs[grant_id] = 0  # Clear the request once granted
                self.log.debug(f'    after: {self.pending_reqs}')
                # Update i_req to reflect the cleared request
                self.dut.i_req.value = int("".join(map(str, self.pending_reqs)), 2)


    async def handle_grant_ack(self):
        while True:
            await RisingEdge(self.dut.i_clk)
            if self.WAIT_GNT_ACK == 1 and self.dut.o_gnt_valid.value == 1:
                grant_id = self.dut.o_gnt_id.value
                grant_ack_delay = self.random_delay()
                for _ in range(grant_ack_delay):
                    await self.wait_clocks('i_clk', 1)
                self.dut.i_gnt_ack.value = (1 << grant_id)
                await self.wait_clocks('i_clk', 1)
                self.dut.i_gnt_ack.value = 0
                
                
    async def run_test(self):
        cocotb.start_soon(self.generate_requests(20*self.CLIENTS))
        cocotb.start_soon(self.check_grants())
        cocotb.start_soon(self.handle_grant_ack())

        # Run for a sufficient number of clock cycles
        for _ in range(1000):
            await RisingEdge(self.dut.i_clk)


@cocotb.test()
async def arbiter_round_robin_test(dut):
    """Test the round-robin arbiter"""
    tb = ArbiterTB(dut)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    await tb.start_clock('i_clk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.run_test()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

# @pytest.mark.parametrize("clients, wait_ack", [(6, 0)])
@pytest.mark.parametrize("clients, wait_ack", [(6, 0), (4, 1)])
def test_arbiter_round_robin(request, clients, wait_ack):
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
    parameters = {'CLIENTS':clients, 'WAIT_GNT_ACK':wait_ack}

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
