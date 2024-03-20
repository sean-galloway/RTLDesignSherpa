import cocotb
from cocotb.triggers import FallingEdge, Timer, Event
from cocotb.clock import Clock
from cocotb.queue import Queue
from cocotb.utils import get_sim_time
import os
import subprocess
import random
import pytest
from cocotb_test.simulator import run
from TBBase import TBBase
from ConstrainedRandom import ConstrainedRandom


class CTScore(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.max_val = (self.N**2)-1

    async def clear_interface(self):
        self.dut.i_mark_valid.value = 0
        self.dut.i_tag_in_valid.value = 0
        self.dut.i_mark_invalid.value = 0
        self.dut.i_tag_in_invalid.value = 0
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
        self.log.info(f'    N:      {self.N}')
        self.log.info(f'    DEPTH:  {self.DEPTH}')
        self.log.info('-------------------------------------------')


    async def main_loop(self, count=100):
        """ Test with randomized mark valid/invalid operations """        
        tag_queue = Queue()
        set_done_event = Event()
        clear_done_event = Event()

        num_operations = 100

        # Start the concurrent processes
        cocotb.start_soon(self.drive_mark_valid(tag_queue, num_operations, set_done_event))
        cocotb.start_soon(self.drive_mark_invalid(tag_queue, num_operations, clear_done_event))

        # Wait for both operations to complete
        await set_done_event.wait()
        await clear_done_event.wait()
        
        # Run after the run
        await self.wait_clocks('i_clk', 50)


    async def drive_mark_valid(self, tag_queue, num_operations, operation_done_event):
        """Randomly mark entries as valid and handle hit scenarios."""
        TOTAL_DEPTH = 2**self.N
        valid_constraints = [(0, self.N-1), (self.N-1, TOTAL_DEPTH-1)]
        valid_weights = [10, 1]
        crand = ConstrainedRandom(valid_constraints, valid_weights)
        valid_del_constraints = [(0, 2), (3, 15)]
        valid_del_weights = [3, 1]
        crand_del = ConstrainedRandom(valid_del_constraints, valid_del_weights)
        for _ in range(num_operations):
            # Randomly choose to mark an entry as valid or simulate a hit scenario
            # tag_to_mark = random.randint(0, TOTAL_DEPTH - 1)
            tag_to_mark = crand.next()
            
            # Drive the inputs
            self.dut.i_mark_valid.value = 1
            self.dut.i_tag_in_valid.value = tag_to_mark
            await Timer(100, units='ps')
            is_hit = self.dut.w_hit
            mark_valid_tag = self.dut.o_tag_remap.value if is_hit else tag_to_mark
            mark_valid_tag_hex = self.hex_format(mark_valid_tag, self.max_val)
            tag_in_hex = self.hex_format(tag_to_mark, self.max_val)
            # Wait for one clock cycle
            await self.wait_clocks('i_clk', 1)
            # If there was a hit, remap should be used. Otherwise, the actual tag.
            tag_queue.put_nowait(mark_valid_tag)
            current_time_ns = get_sim_time('ns')
            self.log.info(f'MarkValid:   Tag: {mark_valid_tag_hex} Hit: {is_hit} Tag: {tag_in_hex} Time: {current_time_ns}')

            # Clear the drive signals
            self.dut.i_mark_valid.value = 0
            self.dut.i_tag_in_valid.value = 0

            while tag_queue.qsize() == self.DEPTH:
                await self.wait_clocks('i_clk', 1)
            
            # Add a random delay before the next operation
            await self.wait_clocks('i_clk', crand_del.next())
        
        operation_done_event.set()


    async def drive_mark_invalid(self, tag_queue,  num_operations, operation_done_event):
        """Randomly mark entries as invalid after they've been marked valid."""
        invalid_constraints = [(0, 0), (1, 10), (11, 30), (30, 40)]
        invalid_weights = [2, 5, 10, 1]
        crand = ConstrainedRandom(invalid_constraints, invalid_weights)
        just_empty = True
        for _ in range(num_operations):
            while tag_queue.empty():
                await self.wait_clocks('i_clk', 1)
                just_empty = True

            if just_empty:
                await self.wait_clocks('i_clk', crand.next())
            just_empty = False
            tag_to_mark_invalid = await tag_queue.get()
            mark_invalid_tag = self.hex_format(tag_to_mark_invalid, self.max_val)
            
            self.dut.i_mark_invalid.value = 1
            self.dut.i_tag_in_invalid.value = tag_to_mark_invalid

            # Wait for one clock cycle
            await self.wait_clocks('i_clk', 1)
            current_time_ns = get_sim_time('ns')
            self.log.info(f'MarkInValid: Tag: {mark_invalid_tag}                                   Time: {current_time_ns}')
            
            self.dut.i_mark_invalid.value = 0
            self.dut.i_tag_in_invalid.value = 0
            await self.wait_clocks('i_clk', crand.next())

        operation_done_event.set()                


@cocotb.test()
async def cam_scoreboard_test(dut):
    """Test the scoreboard"""
    tb = CTScore(dut)
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

@pytest.mark.parametrize("n, depth", [(8, 16)])
def test_junk_cam_tag_scoreboard(request, n, depth):
    dut_name = "cam_tag_scoreboard"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = dut_name   

    verilog_sources = [
        os.path.join(rtl_dir, f"{dut_name}.sv"),
    ]
    includes = []
    parameters = {'N':n,'DEPTH':depth}

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
