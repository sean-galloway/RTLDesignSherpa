"""
Generic Counter Test with Parameterized Test Levels and Configuration

This test uses max_value and test_level as parameters for maximum flexibility:

CONFIGURATION:
    max_value:   Maximum count value (32, 255, 1023, 32767)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - max_value: [32, 255, 1023, 32767]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_MAX_VALUE: Maximum count value for counter

COUNTER BEHAVIOR:
    For MAX=255: Counter counts 0→1→2→...→255, then tick=1 when count==255
    Expected cycles before tick: MAX+1 (e.g., 256 cycles for MAX=255)
"""

import os
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd


class CounterTB(TBBase):
    """Testbench for Generic Counter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.MAX_VALUE = self.convert_to_int(os.environ.get('TEST_MAX_VALUE', '32767'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Counter TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"MAX_VALUE={self.MAX_VALUE}")
        self.log.info(f"Expected cycles before tick: {self.MAX_VALUE}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.tick = self.dut.tick

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    async def wait_for_tick(self, timeout_cycles=None):
        """Wait for tick signal to go high"""
        if timeout_cycles is None:
            timeout_cycles = self.MAX_VALUE + 20

        cycle_count = 0
        while cycle_count < timeout_cycles:
            cycle_count += 1
            await RisingEdge(self.clk)
            if self.tick.value == 1:
                return cycle_count
        
        raise TimeoutError(f"Tick not received within {timeout_cycles} cycles")

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'basic':
            num_cycles = 2  # Test 2 complete cycles
        elif self.TEST_LEVEL == 'medium':
            num_cycles = 5  # Test 5 complete cycles
        else:  # full
            num_cycles = 10  # Test 10 complete cycles

        all_passed = True
        expected_cycles = self.MAX_VALUE  # Continuous cycles should also be MAX  # After reset, counter takes MAX cycles to reach MAX  # RTL takes exactly MAX cycles to go from 0 to MAX

        for cycle in range(num_cycles):
            self.log.debug(f"Starting cycle {cycle + 1}")
            
            # Wait for tick
            try:
                cycles_to_tick = await self.wait_for_tick()
                
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"Cycle {cycle + 1}: Expected {expected_cycles} cycles, got {cycles_to_tick}")
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        break
                else:
                    self.log.debug(f"Cycle {cycle + 1}: Correct timing - {cycles_to_tick} cycles{self.get_time_ns_str()}")

                # Verify tick is only high for one cycle
                await RisingEdge(self.clk)
                if self.tick.value != 0:
                    self.log.error(f"Cycle {cycle + 1}: Tick should be low after one cycle")
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        break

            except TimeoutError as e:
                self.log.error(f"Cycle {cycle + 1}: {str(e)}{self.get_time_ns_str()}")
                all_passed = False
                break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle + 1,
                'expected_cycles': expected_cycles,
                'actual_cycles': cycles_to_tick if 'cycles_to_tick' in locals() else -1,
                'success': cycles_to_tick == expected_cycles if 'cycles_to_tick' in locals() else False
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        expected_cycles = self.MAX_VALUE

        # Count partway through cycle
        partial_count = self.MAX_VALUE // 2 if self.MAX_VALUE > 4 else 2
        
        for i in range(partial_count):
            await RisingEdge(self.clk)
            if self.tick.value == 1:
                self.log.error(f"Unexpected tick at cycle {i}")
                all_passed = False
                break

        # Apply reset
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

        # Now count full cycle and verify timing
        try:
            cycles_to_tick = await self.wait_for_tick()
            if cycles_to_tick != expected_cycles:
                self.log.error(f"After reset: Expected {expected_cycles} cycles, got {cycles_to_tick}")
                all_passed = False
            else:
                self.log.debug(f"After reset: Correct timing - {cycles_to_tick} cycles{self.get_time_ns_str()}")
        except TimeoutError as e:
            self.log.error(f"After reset: {str(e)}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'expected_cycles': expected_cycles,
            'actual_cycles': cycles_to_tick if 'cycles_to_tick' in locals() else -1,
            'success': cycles_to_tick == expected_cycles if 'cycles_to_tick' in locals() else False
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_continuous_operation(self):
        """Test continuous operation over multiple cycles"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping continuous operation test{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing continuous operation{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test multiple cycles
        if self.TEST_LEVEL == 'medium':
            num_cycles = 3
        else:  # full
            num_cycles = 5

        all_passed = True
        cycle_times = []
        expected_cycles = self.MAX_VALUE\
        

        for cycle in range(num_cycles):
            if cycle > 0:
                expected_cycles = self.MAX_VALUE+1
            try:
                cycles_to_tick = await self.wait_for_tick()
                cycle_times.append(cycles_to_tick)
                
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"Continuous cycle {cycle + 1}: Expected {expected_cycles}, got {cycles_to_tick}")
                    all_passed = False
                    break
                    
            except TimeoutError as e:
                self.log.error(f"Continuous cycle {cycle + 1}: {str(e)}")
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'continuous_operation',
            'num_cycles': len(cycle_times),
            'cycle_times': cycle_times,
            'success': all_passed and len(cycle_times) == num_cycles
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_edge_cases(self):
        """Test edge cases and boundary conditions"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping edge case tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()
        
        all_passed = True
        expected_cycles = self.MAX_VALUE  # Edge case should also expect MAX cycles

        # Test multiple rapid resets
        for reset_test in range(3):
            await self.reset_dut()
            
            # Count a few cycles
            for i in range(min(5, self.MAX_VALUE // 4)):
                await RisingEdge(self.clk)
                if self.tick.value == 1 and i < expected_cycles - 1:
                    self.log.error(f"Unexpected early tick in reset test {reset_test}")
                    all_passed = False
                    break

            if not all_passed:
                break

        # Test reset during tick
        if all_passed:
            await self.reset_dut()
            
            # Wait until just before tick
            for i in range(expected_cycles - 1):
                await RisingEdge(self.clk)
            
            # Reset during the cycle that should produce tick
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            
            # Tick should not occur
            if self.tick.value == 1:
                self.log.error("Tick occurred during reset")
                all_passed = False
            
            self.rst_n.value = 1
            await RisingEdge(self.clk)
            
            # Now should start counting from 0 again
            try:
                cycles_to_tick = await self.wait_for_tick()
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"After reset during tick: Expected {expected_cycles}, got {cycles_to_tick}")
                    all_passed = False
            except TimeoutError:
                all_passed = False

        # Store result
        result = {
            'test_type': 'edge_cases',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running COUNTER tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_continuous_operation, "Continuous operation"),
            (self.test_edge_cases, "Edge cases")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}{self.get_time_ns_str()}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}{self.get_time_ns_str()}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall COUNTER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_test(dut):
    """Test for Generic Counter module"""
    tb = CounterTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    max_values = [32, 255, 1023, 32767]  # Different maximum count values
    test_levels = ['basic', 'medium', 'full']  # Test levels

    valid_params = []
    for max_value, test_level in product(max_values, test_levels):
        valid_params.append((max_value, test_level))

    # For debugging, uncomment one of these:
    # return [(32, 'full')]  # Single test
    return [(255, 'medium'), (1023, 'medium')]  # Just specific configurations

    # return valid_params


params = generate_params()


@pytest.mark.parametrize("max_value, test_level", params)
def test_counter(request, max_value, test_level):
    """
    Parameterized Generic Counter test with configurable max value and test level.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    
    Counter behavior: For MAX=N, counter counts 0→1→2→...→N, tick occurs when count==N
    Expected cycles: MAX (e.g., 32 cycles for MAX=32)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "counter"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    max_str = TBBase.format_dec(max_value, 5)
    test_name_plus_params = f"test_counter_max{max_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'MAX': str(max_value)
    }

    # Adjust timeout based on test level and max value
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    max_factor = max(1.0, max_value / 1000.0)  # Larger max values take more time
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_MAX_VALUE': str(max_value),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs", 
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: max_value={max_value}")
    print(f"Expected cycles before tick: {max_value}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: max_value={max_value}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
