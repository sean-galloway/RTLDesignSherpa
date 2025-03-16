import os
import subprocess
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.TBClasses.tbbase import TBBase
from CocoTBFramework.Components.constrained_random import ConstrainedRandom


class ClockGateCtrlTB(TBBase):
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
        
        self.wait_cycles_gen = ConstrainedRandom(
            constraints=[(1, 10), (20, 30)],
            weights=[8, 2],
            is_integer=True
        )


    def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.i_cfg_cg_enable.value = 0
        self.dut.i_cfg_cg_idle_count.value = self.max_count
        self.last_idle_count = self.max_count
        self.dut.i_wakeup.value = 0
        self.log.info('Assert reset done.')

    def deassert_reset(self):
        self.dut.aresetn.value = 1
        self.log.info("Reset complete.")

    async def verify_clock_gating(self, cycles, expected_enabled):
        """Verify clock gating behavior for specified cycles"""
        await self.wait_clocks('clk_in', cycles)
        if expected_enabled:
            assert self.dut.clk_out.value == self.dut.clk_in.value, \
                "Clock should be enabled but was gated"
        else:
            assert self.dut.clk_out.value == 0, \
                "Clock should be gated but was enabled"

    async def systematic_enable_test(self):
        """Test all combinations of wake with cfg_enable=1"""
        self.log.info("Starting systematic enable test")
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = self.max_count  # Set max count to focus on wake

        # Test all combinations of wake
        for wake in range(2):
            msg = f"Testing wake={wake}"
            self.log.info(msg)
            self.dut.i_wakeup.value = wake
            
            # Clock should be enabled if wake=1
            expected_enabled = (wake == 1)
            await self.verify_clock_gating(30, expected_enabled)

    async def concurrent_wake_test(self):
        """Test concurrent assertion of wake signals"""
        self.log.info("Starting concurrent wake test")
        count = self.max_count
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = count  # Use smaller count for this test

        # Test concurrent assertion
        self.dut.i_wakeup.value = 1
        await self.verify_clock_gating(count, True)  # Wake should dominate

        # Deassert wake, verify counter starts
        self.dut.i_wakeup.value = 0
        await self.verify_clock_gating(self.max_count-2, True)  # Should still be enabled during countdown

    async def systematic_counter_test(self):
        """Test various idle counter values"""
        self.log.info("Starting systematic counter test")
        self.dut.i_cfg_cg_enable.value = 1
        test_values = [
            self.max_count,  # Max
            self.max_count * 3 // 4,  # Max-1/4
            self.max_count // 2,      # Max-1/2
            self.max_count // 4       # Max-3/4
        ]

        for count in test_values:
            msg = f"Testing idle count: {count}"
            self.log.info(msg)
            self.dut.i_cfg_cg_idle_count.value = count
            self.last_idle_count = count
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0

            # Verify clock runs for exactly count cycles
            await self.verify_clock_gating(count, True)
            await self.verify_clock_gating(self.max_count, False)  # Should be gated after timeout

    async def counter_timeout_sweep_test(self):
        """Test wakeup assertion around counter timeout"""
        self.log.info("Starting counter timeout sweep test")
        self.dut.i_cfg_cg_enable.value = 1
        timeout_value = self.max_count  # Use fixed timeout for sweep test
        self.dut.i_cfg_cg_idle_count.value = timeout_value
        
        # Test wakeup assertions from -5 to +5 cycles around timeout
        for offset in range(-5, 6):
            msg = f"Testing wakeup at timeout {offset:+d} cycles"
            self.log.info(msg)
            # Start countdown
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0
            
            # Wait until just before the test point
            await self.wait_clocks('clk_in', timeout_value + offset - 1)
            
            # Assert wakeup
            self.dut.i_wakeup.value = 1
            await self.verify_clock_gating(10, True)  # Should always be enabled after wakeup
            
            # Cleanup
            self.dut.i_wakeup.value = 0
            await self.wait_clocks('clk_in', 5)

    async def edge_case_test(self):
        """Test additional edge cases"""
        self.log.info("Starting edge case tests")
        
        # Test 1: Zero idle count behavior
        self.log.info("Testing zero idle count")
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = 0
        self.dut.i_wakeup.value = 1
        await self.wait_clocks('clk_in', 2)
        self.dut.i_wakeup.value = 0
        await self.verify_clock_gating(5, False)  # Should gate immediately
        
        # Test 2: Rapid wake toggles with minimum idle count
        self.log.info("Testing rapid toggles with min idle count")
        self.dut.i_cfg_cg_idle_count.value = 1
        for _ in range(5):
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 1)
            self.dut.i_wakeup.value = 0
            await self.wait_clocks('clk_in', 1)
            await self.wait_clocks('clk_in', 1)

    async def monitor_clock_output(self):
        """Monitor clock output and log transitions"""
        prev_clk = 0
        edges_count = 0
        
        while True:
            await self.wait_clocks('clk_in', 1)
            curr_clk = self.dut.clk_out.value
            
            if prev_clk != curr_clk:
                edges_count += 1
                msg = f"Clock output changed to {curr_clk} at {edges_count}"
                self.log.debug(msg)
            
            prev_clk = curr_clk

    async def check_gating_behavior(self):
        """Test various clock gating scenarios"""
        # Start clock monitoring
        cocotb.start_soon(self.monitor_clock_output())
        
        # Test Case 1: Basic Wake
        self.log.info("Test Case 1: Basic Wake Transition")
        await self.basic_wake_test()
        
        # Test Case 2: Idle Counter Behavior
        self.log.info("Test Case 2: Idle Counter Operation")
        await self.idle_counter_test()
        
        # Test Case 3: Quick Toggle Test
        self.log.info("Test Case 3: Quick Toggle Test")
        await self.quick_toggle_test()
        
        # Test Case 4: Global Enable/Disable
        self.log.info("Test Case 4: Global Enable/Disable")
        await self.global_enable_test()

    async def basic_wake_test(self):
        """Test basic wake transitions"""
        # Enable clock gating
        self.dut.i_cfg_cg_enable.value = 1
        
        # Wake up
        self.dut.i_wakeup.value = 1
        await self.wait_clocks('clk_in', 5)
        self.dut.i_wakeup.value = 0
        idle_count = self.idle_count_gen.next()
        self.dut.i_cfg_cg_idle_count.value = idle_count
        
        # Wait for idle count to expire
        await self.wait_clocks('clk_in', idle_count + 2)

    async def idle_counter_test(self):
        """Test idle counter behavior with various values"""
        for _ in range(3):  # Test with 3 different random values
            idle_count = self.idle_count_gen.next()
            msg = f"Testing idle count: {idle_count}"
            self.log.info(msg)
            
            # Set up test conditions
            self.dut.i_cfg_cg_enable.value = 1
            self.dut.i_cfg_cg_idle_count.value = idle_count
            self.dut.i_wakeup.value = 1
            
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0
            
            # Wait for counter expiration
            await self.wait_clocks('clk_in', idle_count + 2)
            
            await self.wait_clocks('clk_in', 5)

    async def quick_toggle_test(self):
        """Test rapid toggling of wake signals"""
        self.dut.i_cfg_cg_enable.value = 1
        idle_count = 4  # Use a fixed small value for quick toggle test
        self.dut.i_cfg_cg_idle_count.value = idle_count
        
        for _ in range(5):  # Do 5 quick toggles
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0
            await self.wait_clocks('clk_in', 2)
            await self.wait_clocks('clk_in', 1)

    async def global_enable_test(self):
        """Test global enable/disable functionality"""
        # Disable clock gating
        self.dut.i_cfg_cg_enable.value = 0
        await self.wait_clocks('clk_in', 10)
        
        # Enable clock gating
        self.dut.i_cfg_cg_enable.value = 1
        await self.wait_clocks('clk_in', 10)
        
        # Verify clock is gated

    async def run_test(self):
        # Run systematic tests first
        await self.systematic_enable_test()
        await self.concurrent_wake_test()
        await self.systematic_counter_test()
        await self.counter_timeout_sweep_test()
        await self.edge_case_test()
        
        # Run original randomized tests
        await self.check_gating_behavior()

@cocotb.test(timeout_time=1, timeout_unit="ms")
async def clock_gate_ctrl_test(dut):
    """Test the clock gate control block"""
    tb = ClockGateCtrlTB(dut)
    
    # Set random seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    msg = f'Using seed: {seed}'
    tb.log.info(msg)
    
    # Start clock and initialize
    await tb.start_clock('clk_in', 10, 'ns')
    tb.assert_reset()
    await tb.wait_clocks('clk_in', 5)
    tb.deassert_reset()
    await tb.wait_clocks('clk_in', 5)
    
    # Run the test
    await tb.run_test()

# Test configuration
def test_clock_gate_ctrl(request):
    dut_name = "clock_gate_ctrl"
    module = os.path.splitext(os.path.basename(__file__))[0]
    toplevel = dut_name

    # Get repository root and directories
    repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
    tests_dir = os.path.abspath(os.path.dirname(__file__))
    rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl', 'common'))

    verilog_sources = [
        os.path.join(rtl_dir, "icg.sv"),
        os.path.join(rtl_dir, f"{dut_name}.sv")
    ]

    parameters = {'N': 4}  # Default counter width
    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}
    
    sim_build = os.path.join(repo_root, 'val', 'unit_common', 'local_sim_build', 
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
