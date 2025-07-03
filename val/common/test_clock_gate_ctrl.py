import os
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.shared.constrained_random import ConstrainedRandom


class ClockGateCtrlConfig:
    """Configuration class for clock gate controller tests"""
    def __init__(self, name, counter_width):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            counter_width: Counter width in bits
        """
        self.name = name
        self.counter_width = counter_width


class ClockGateCtrlTB(TBBase):
    """
    Testbench for the clock_gate_ctrl module
    Features:
    - Clock gating behavior verification
    - Counter timeout testing
    - Enable/disable functionality
    - Wake signal handling
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '4'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Derived parameters
        self.max_count = (2**self.N) - 1
        self.last_idle_count = self.max_count

        # Clock and reset signals
        self.clock = self.dut.clk_in
        self.reset_n = self.dut.aresetn

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

        # Log configuration
        self.log.info(f"Clock Gate Ctrl TB initialized with N={self.N}")
        self.log.info(f"SEED={self.SEED}")

    def assert_reset(self):
        """Reset the DUT to known state"""
        self.reset_n.value = 0
        self.dut.i_cfg_cg_enable.value = 0
        self.dut.i_cfg_cg_idle_count.value = self.max_count
        self.last_idle_count = self.max_count
        self.dut.i_wakeup.value = 0
        self.log.info('Assert reset done.')

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.assert_reset()

        # Hold reset for multiple cycles
        await self.wait_clocks('clk_in', 5)

        # Release reset
        self.reset_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk_in', 5)

        self.log.debug('Ending reset_dut')

    async def verify_clock_gating(self, cycles, expected_enabled, description=None):
        """
        Verify clock gating behavior for specified cycles

        Args:
            cycles: Number of cycles to verify
            expected_enabled: Expected clock enable state
            description: Optional description for logging
        """
        msg_prefix = f"{description}: " if description else ""
        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Verifying clock for {cycles} cycles, expected enabled: {expected_enabled} @ {time_ns}ns")

        failures = 0
        for i in range(cycles):
            await self.wait_clocks('clk_in', 1)

            if expected_enabled:
                # When enabled, clock output should match input on rising edge
                if self.dut.clk_in.value == 1 and self.dut.clk_out.value != 1:
                    failures += 1
                    self.log.warning(f"{msg_prefix}Cycle {i}: Clock should be enabled but was gated @ {get_sim_time('ns')}ns")
            else:
                # When gated, clock output should always be 0
                if self.dut.clk_out.value != 0:
                    failures += 1
                    self.log.warning(f"{msg_prefix}Cycle {i}: Clock should be gated but was enabled @ {get_sim_time('ns')}ns")

            # Only assert after all cycles checked, to collect comprehensive failure data
            if failures > 3:  # Limit excessive logging
                self.log.error(f"{msg_prefix}Too many failures, aborting verification @ {get_sim_time('ns')}ns")
                assert False, f"{msg_prefix}Clock gating verification failed in {failures} cycles"

        if failures > 0:
            assert False, f"{msg_prefix}Clock gating verification failed in {failures} cycles"

        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Clock verification passed @ {time_ns}ns")

    async def wait_for_counter_expiration(self, count_value, description=None):
        """
        Wait for the idle counter to expire

        Args:
            count_value: Value to count down from
            description: Optional description for logging
        """
        msg_prefix = f"{description}: " if description else ""
        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Waiting for counter to expire from {count_value} @ {time_ns}ns")

        # Add a small margin to account for any initialization delays
        wait_cycles = count_value + 2
        await self.wait_clocks('clk_in', wait_cycles)

        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Counter should have expired @ {time_ns}ns")

    async def run_systematic_enable_test(self):
        """Test all combinations of wake with cfg_enable=1"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting systematic enable test @ {time_ns}ns")

        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = self.max_count  # Set max count to focus on wake

        # Test wake=1 scenario (clock should be enabled immediately)
        self.log.info(f"Testing wake=1 @ {get_sim_time('ns')}ns")
        self.dut.i_wakeup.value = 1
        await self.verify_clock_gating(10, True, "Wake=1")

        # Test wake=0 scenario (clock should be gated after counter expires)
        self.log.info(f"Testing wake=0 @ {get_sim_time('ns')}ns")
        self.dut.i_wakeup.value = 0

        # First verify clock remains active during countdown
        await self.verify_clock_gating(5, True, "Wake=0 during countdown")

        # Wait for counter to expire (max_count cycles plus margin)
        self.log.info(f"Waiting for counter to expire (max_count={self.max_count}) @ {get_sim_time('ns')}ns")
        await self.wait_for_counter_expiration(self.max_count, "Wake=0")

        # Verify clock is now gated
        await self.verify_clock_gating(10, False, "Wake=0 after expiration")

        time_ns = get_sim_time('ns')
        self.log.info(f"Systematic enable test completed @ {time_ns}ns")

    async def run_concurrent_wake_test(self):
        """Test concurrent assertion of wake signals"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting concurrent wake test @ {time_ns}ns")

        count = self.max_count // 2  # Use smaller count for this test
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = count

        # Test concurrent assertion
        self.dut.i_wakeup.value = 1
        await self.verify_clock_gating(10, True, "Concurrent wake")  # Wake should dominate

        # Deassert wake, verify counter starts
        self.dut.i_wakeup.value = 0
        # Verify clock remains enabled during countdown
        await self.verify_clock_gating(count-2, True, "After wake, during countdown")

        # Wait for a few more cycles to ensure counter expires
        await self.wait_clocks('clk_in', 5)

        # After counter expires, clock should be gated
        await self.verify_clock_gating(10, False, "After counter expires")

        time_ns = get_sim_time('ns')
        self.log.info(f"Concurrent wake test completed @ {time_ns}ns")

    async def run_systematic_counter_test(self):
        """Test various idle counter values"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting systematic counter test @ {time_ns}ns")

        self.dut.i_cfg_cg_enable.value = 1
        test_values = [
            self.max_count,                # Max
            self.max_count * 3 // 4,       # Max-1/4
            self.max_count // 2,           # Max-1/2
            self.max_count // 4            # Max-3/4
        ]

        for count in test_values:
            time_ns = get_sim_time('ns')
            msg = f"Testing idle count: {count} @ {time_ns}ns"
            self.log.info(msg)

            self.dut.i_cfg_cg_idle_count.value = count
            self.last_idle_count = count

            # Trigger wake
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0

            # Verify clock runs for exactly count cycles (with small margin for timing)
            await self.verify_clock_gating(count - 3, True, f"Count={count} active")

            # Wait a few more cycles to ensure counter expired
            await self.wait_clocks('clk_in', 5)

            # Verify clock is gated after timeout
            await self.verify_clock_gating(10, False, f"Count={count} gated")

            # Add a brief pause between iterations
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 5)

        time_ns = get_sim_time('ns')
        self.log.info(f"Systematic counter test completed @ {time_ns}ns")

    async def run_counter_timeout_sweep_test(self):
        """Test wakeup assertion around counter timeout"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting counter timeout sweep test @ {time_ns}ns")

        timeout_value = self.max_count // 2  # Use fixed timeout for sweep test
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = timeout_value

        # Test wakeup assertions from -5 to +5 cycles around timeout
        for offset in range(-5, 6):
            time_ns = get_sim_time('ns')
            msg = f"Testing wakeup at timeout {offset:+d} cycles @ {time_ns}ns"
            self.log.info(msg)

            # Start countdown
            self.dut.i_wakeup.value = 1
            await self.wait_clocks('clk_in', 2)
            self.dut.i_wakeup.value = 0

            # Wait until just before the test point
            if offset < 0:
                # For negative offsets, assert wakeup before timeout
                await self.wait_clocks('clk_in', timeout_value + offset - 1)
                self.dut.i_wakeup.value = 1
                await self.verify_clock_gating(10, True, f"Offset={offset}")
            else:
                # For zero or positive offsets, wait for timeout then assert wakeup
                await self.wait_for_counter_expiration(timeout_value, f"Offset={offset}")
                # For positive offsets, wait additional cycles after timeout
                if offset > 0:
                    # Verify clock is gated after timeout
                    await self.verify_clock_gating(2, False, f"Offset={offset} (gated)")
                    # Wait additional offset cycles
                    await self.wait_clocks('clk_in', offset - 1)
                # Assert wakeup and verify clock becomes enabled
                self.dut.i_wakeup.value = 1
                await self.verify_clock_gating(5, True, f"Offset={offset} (rewake)")

            # Cleanup
            self.dut.i_wakeup.value = 0
            await self.wait_clocks('clk_in', 5)

        time_ns = get_sim_time('ns')
        self.log.info(f"Counter timeout sweep test completed @ {time_ns}ns")

    async def run_edge_case_test(self):
        """Test additional edge cases"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting edge case tests @ {time_ns}ns")

        # Test 1: Zero idle count behavior
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing zero idle count @ {time_ns}ns")
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_cfg_cg_idle_count.value = 0

        # First, make sure clock is running with wake=1
        self.dut.i_wakeup.value = 1
        await self.verify_clock_gating(2, True, "Zero count, wake=1")

        # Then, deassert wake and check gating behavior
        self.dut.i_wakeup.value = 0
        # With zero count, gating should happen on next cycle, but allow a cycle for propagation
        await self.wait_clocks('clk_in', 2)
        await self.verify_clock_gating(5, False, "Zero count, wake=0")

        # Test 2: Rapid wake toggles with minimum idle count
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing rapid toggles with min idle count @ {time_ns}ns")
        self.dut.i_cfg_cg_idle_count.value = 1

        for i in range(5):
            time_ns = get_sim_time('ns')
            self.log.debug(f"Toggle {i} @ {time_ns}ns")

            # Assert wake, verify clock enabled
            self.dut.i_wakeup.value = 1
            await self.verify_clock_gating(1, True, f"Toggle {i}, wake=1")

            # Deassert wake, verify clock stays enabled for 1 cycle
            self.dut.i_wakeup.value = 0
            await self.verify_clock_gating(1, True, f"Toggle {i}, wake=0, counting")

            # Wait one more cycle and verify clock gating
            await self.wait_clocks('clk_in', 1)
            await self.verify_clock_gating(1, False, f"Toggle {i}, wake=0, gated")

        time_ns = get_sim_time('ns')
        self.log.info(f"Edge case tests completed @ {time_ns}ns")

    async def run_global_enable_test(self):
        """Test global enable/disable functionality"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting global enable test @ {time_ns}ns")

        # Verify clock enabled when global enable is off
        self.dut.i_cfg_cg_enable.value = 0
        self.dut.i_wakeup.value = 0
        await self.verify_clock_gating(10, True, "Enable=0")

        # Configure idle count with global enable OFF
        self.dut.i_cfg_cg_idle_count.value = 5
        await self.wait_clocks('clk_in', 2)  # Wait for value to settle

        # Verify wake still works when global enable is on
        self.dut.i_cfg_cg_enable.value = 1
        self.dut.i_wakeup.value = 1
        await self.verify_clock_gating(10, True, "Enable=1, Wake=1")

        # Turn off wake signal to start countdown
        self.dut.i_wakeup.value = 0

        # Verify clock remains enabled during countdown (5 cycles)
        await self.verify_clock_gating(4, True, "Enable=1, During Countdown")

        # Wait a bit more to ensure counter expires
        await self.wait_clocks('clk_in', 3)

        # Now verify the clock is gated after counter expires
        await self.verify_clock_gating(5, False, "Enable=1, After Expiration")

        # Verify clock immediately enabled when global enable turned off
        self.dut.i_cfg_cg_enable.value = 0
        await self.verify_clock_gating(10, True, "Enable=0 after gating")

        time_ns = get_sim_time('ns')
        self.log.info(f"Global enable test completed @ {time_ns}ns")

    async def monitor_clock_output(self):
        """Monitor clock output and log transitions"""
        prev_clk = 0
        edges_count = 0

        while True:
            await self.wait_clocks('clk_in', 1)
            curr_clk = int(self.dut.clk_out.value)

            if prev_clk != curr_clk:
                edges_count += 1
                time_ns = get_sim_time('ns')
                msg = f"Clock output changed to {curr_clk} at edge {edges_count} @ {time_ns}ns"
                self.log.debug(msg)

            prev_clk = curr_clk

    async def monitor_idle_counter(self):
        """Monitor idle counter value for debugging"""
        prev_count = 0

        while True:
            await self.wait_clocks('clk_in', 1)
            curr_count = int(self.dut.r_idle_counter.value)

            if prev_count != curr_count:
                time_ns = get_sim_time('ns')
                msg = f"Idle counter changed to 0x{curr_count:X} @ {time_ns}ns"
                self.log.debug(msg)

            prev_count = curr_count

    async def run_test(self):
        """Run all test sequences"""
        # Start monitoring functions
        cocotb.start_soon(self.monitor_clock_output())
        cocotb.start_soon(self.monitor_idle_counter())

        # Run all test sequences
        await self.run_systematic_enable_test()
        await self.run_concurrent_wake_test()
        await self.run_systematic_counter_test()
        await self.run_counter_timeout_sweep_test()
        await self.run_edge_case_test()
        await self.run_global_enable_test()

        # Wait for any pending operations
        await self.wait_clocks('clk_in', 20)

        time_ns = get_sim_time('ns')
        self.log.info(f"All test sequences completed successfully @ {time_ns}ns")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def clock_gate_ctrl_test(dut):
    """Test the clock gate control block"""
    tb = ClockGateCtrlTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'Using seed: {seed}'
    tb.log.info(msg)

    # Start the clock
    await tb.start_clock('clk_in', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run all test sequences
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting clock gate controller tests @ {time_ns}ns ===")
        await tb.run_test()

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('clk_in', 10)


@pytest.mark.parametrize("counter_width", [4, 8])
def test_clock_gate_ctrl(request, counter_width):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    })

    dut_name = "clock_gate_ctrl"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Create a human readable test identifier
    n_str = TBBase.format_dec(counter_width, 2)
    test_name_plus_params = f"test_{dut_name}_n{n_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    parameters = {'N': counter_width}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add parameter values to environment variables
    # sourcery skip: no-loop-in-tests
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    sim_args = [
                "--trace-fst",  # Tell Verilator to use FST
                "--trace-structs",
                "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
