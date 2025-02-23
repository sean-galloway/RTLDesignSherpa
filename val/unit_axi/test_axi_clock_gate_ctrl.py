import cocotb
from cocotb.triggers import Timer
import os
import subprocess
import pytest
from cocotb_test.simulator import run
from TBClasses.TBBase import TBBase
from TBClasses.ConstrainedRandom import ConstrainedRandom
from itertools import product

class AXIClockGateCtrlTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.N = self.convert_to_int(os.environ.get('N', '4'))

        # Maximum counter value
        self.max_count = 2**self.N - 1
        self.last_idle_count = self.max_count

        # Setup constrained random generators
        self.idle_count_gen = ConstrainedRandom(
            constraints=[(0, 2**self.N - 1)],
            weights=[1],
            is_integer=True
        )

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.i_cfg_cg_enable.value = 0
        self.dut.i_cfg_idle_count.value = self.max_count
        self.last_idle_count = self.max_count
        self.dut.i_user_valid.value = 0
        self.dut.i_axi_valid.value = 0
        self.log.info('Assert reset done.')
        await self.wait_clocks('clk_in', 10)

    async def deassert_reset(self):
        await self.wait_clocks('clk_in', 2)
        self.dut.aresetn.value = 1
        self.log.info("Reset complete.")
        await self.wait_clocks('clk_in', 10)

    async def verify_clock_gating(self, cycles, expected_enabled):
        """Verify clock gating behavior for specified cycles"""
        await self.wait_clocks('clk_in', cycles)
        if expected_enabled:
            assert self.dut.clk_out.value == self.dut.clk_in.value, \
                "Clock should be enabled but was gated"
        else:
            assert self.dut.clk_out.value == 0, \
                "Clock should be gated but was enabled"

    async def verify_idle_status(self, expected_idle):
        """Verify the idle status output"""
        assert self.dut.o_idle.value == expected_idle, \
            f"Idle status mismatch. Expected: {expected_idle}, Got: {self.dut.o_idle.value}"

    async def test_valid_signal_response(self):
        """Test clock gating response to valid signals"""
        self.log.info("Starting valid signal response test")
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_idle_count.value = self.max_count

        # Test all combinations of user_valid and axi_valid
        for user_valid, axi_valid in product([0, 1], repeat=2):
            self.log.info(f"Testing user_valid={user_valid}, axi_valid={axi_valid}")
            self.dut.i_user_valid.value = user_valid
            self.dut.i_axi_valid.value = axi_valid

            # Clock should be enabled if any valid is high
            expected_enabled = (user_valid == 1 or axi_valid == 1)
            await self.verify_clock_gating(self.max_count+1, expected_enabled)

    async def test_idle_counter_behavior(self):
        """Test idle counter with AXI-specific conditions"""
        self.log.info("Starting idle counter behavior test")
        self.dut.i_cfg_cg_enable.value = 1

        test_values = [
            self.max_count,
            self.max_count * 3 // 4,
            self.max_count // 2
        ]

        # Test all combinations of counter values and valid signals
        for count, (user_valid, axi_valid) in product(
            test_values, 
            product([0, 1], repeat=2)  # All combinations of user_valid and axi_valid
        ):
            self.log.info(f"Testing idle count: {count}, user_valid: {user_valid}, axi_valid: {axi_valid}")
            self.dut.i_cfg_idle_count.value = count

            # Set initial valid signals
            self.dut.i_user_valid.value = user_valid
            self.dut.i_axi_valid.value = axi_valid
            
            await self.wait_clocks('clk_in', 2)

            # Drop valid signals to start idle counter
            self.dut.i_user_valid.value = 0
            self.dut.i_axi_valid.value = 0

            # Clock should remain enabled until it hits zero
            r_idle_counter = int(self.dut.u_clock_gate_ctrl.r_idle_counter.value)
            while r_idle_counter > 2:
                r_idle_counter = int(self.dut.u_clock_gate_ctrl.r_idle_counter.value)
                await self.wait_clocks('clk_in', 1)

            await self.verify_clock_gating(1, True)
            
            # After count cycles, clock should be gated
            await self.verify_clock_gating(5, False)
            
            # Verify idle is asserted
            await self.verify_idle_status(1)
            
            # Test wake-up response
            self.dut.i_user_valid.value = user_valid
            self.dut.i_axi_valid.value = axi_valid
            
            # Verify clock enables immediately on any valid
            if user_valid or axi_valid:
                await self.verify_clock_gating(5, True)
                await self.verify_idle_status(0)
            
            # Clean up for next iteration
            self.dut.i_user_valid.value = 0
            self.dut.i_axi_valid.value = 0
            await self.wait_clocks('clk_in', 5)

    async def monitor_clock_output(self):
        """Monitor clock output and log transitions"""
        prev_clk = 0
        edges_count = 0

        while True:
            await self.wait_clocks('clk_in', 1)
            curr_clk = self.dut.clk_out.value

            if prev_clk != curr_clk:
                edges_count += 1
                self.log.debug(f"Clock output changed to {curr_clk} at {edges_count}")
                r_idle_counter = self.dut.u_clock_gate_ctrl.r_idle_counter.value
                self.log.debug(f"     {r_idle_counter}")

            prev_clk = curr_clk

    async def run_test(self):
        # Start clock monitoring
        cocotb.start_soon(self.monitor_clock_output())

        # Run AXI-specific tests
        await self.test_valid_signal_response()
        await self.test_idle_counter_behavior()

@cocotb.test()
async def axi_clock_gate_ctrl_test(dut):
    """Test the AXI clock gate control block"""
    tb = AXIClockGateCtrlTB(dut)

    # Set random seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    tb.log.info(f'Using seed: {seed}')

    # Start clock and initialize
    await tb.start_clock('clk_in', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('clk_in', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('clk_in', 5)

    # Run the test
    await tb.run_test()

def test_axi_clock_gate_ctrl(request):
    dut_name = "axi_clock_gate_ctrl"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    # Get repository root and directories
    repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
    tests_dir = os.path.abspath(os.path.dirname(__file__))
    rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl', 'common'))
    axi_rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl', 'axi'))

    verilog_sources = [
        os.path.join(rtl_dir, "icg.sv"),
        os.path.join(rtl_dir, "clock_gate_ctrl.sv"),
        os.path.join(axi_rtl_dir, f"{dut_name}.sv")
    ]

    parameters = {
        'N': 4
    }
    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    sim_build = os.path.join(repo_root, 'val', 'unit_axi', 'local_sim_build', 
                            request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=[],
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True
    )
