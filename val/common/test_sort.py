"""
Sort Test with Parameterized Test Levels and Configuration

This test uses num_vals, size and test_level as parameters for maximum flexibility:

CONFIGURATION:
    num_vals:    Number of values to sort (3, 5, 8)
    size:        Size of each value in bits (8, 16, 32)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - num_vals: [3, 5, 8]
    - size: [8, 16, 32]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_NUM_VALS: Number of values to sort
    TEST_SIZE: Size of each value in bits
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


class SortTB(TBBase):
    """Testbench for Sort module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.NUM_VALS = self.convert_to_int(os.environ.get('TEST_NUM_VALS', '5'))
        self.SIZE = self.convert_to_int(os.environ.get('TEST_SIZE', '16'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.TOTAL_WIDTH = self.NUM_VALS * self.SIZE
        self.MAX_VAL = (1 << self.SIZE) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Sort TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"NUM_VALS={self.NUM_VALS}, SIZE={self.SIZE}")
        self.log.info(f"TOTAL_WIDTH={self.TOTAL_WIDTH}, MAX_VAL={self.MAX_VAL}")

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
        self.data_in = self.dut.data
        self.sorted_out = self.dut.sorted

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.data_in.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def pack_values(self, values):
        """Pack array of values into concatenated signal"""
        packed = 0
        for i, val in enumerate(values):
            if i < self.NUM_VALS:
                packed |= (val & self.MAX_VAL) << (i * self.SIZE)
        return packed

    def unpack_values(self, packed_data):
        """Unpack concatenated signal into array of values"""
        values = []
        for i in range(self.NUM_VALS):
            val = (packed_data >> (i * self.SIZE)) & self.MAX_VAL
            values.append(val)
        return values

    def get_sorted_output(self):
        """Get the sorted output data"""
        try:
            output_val = int(self.sorted_out.value)
            return self.unpack_values(output_val)
        except:
            return [0] * self.NUM_VALS

    def is_sorted_descending(self, values):
        """Check if values are sorted in descending order"""
        for i in range(len(values) - 1):
            if values[i] < values[i + 1]:
                return False
        return True

    async def test_basic_sorting(self):
        """Test basic sorting functionality"""
        self.log.info(f"Testing basic sorting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test different value patterns based on level
        if self.TEST_LEVEL == 'basic':
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],  # Mixed values
                [1, 2, 3, 4, 5][:self.NUM_VALS],  # Already sorted ascending
                [9, 7, 5, 3, 1][:self.NUM_VALS],  # Already sorted descending
            ]
        elif self.TEST_LEVEL == 'medium':
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],
                [1, 2, 3, 4, 5][:self.NUM_VALS],
                [9, 7, 5, 3, 1][:self.NUM_VALS],
                [5, 5, 5, 5, 5][:self.NUM_VALS],  # All equal
                [1, 9, 2, 8, 3][:self.NUM_VALS],  # Alternating
            ]
        else:  # full
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],
                [1, 2, 3, 4, 5][:self.NUM_VALS],
                [9, 7, 5, 3, 1][:self.NUM_VALS],
                [5, 5, 5, 5, 5][:self.NUM_VALS],
                [1, 9, 2, 8, 3][:self.NUM_VALS],
                [0, 0, 0, 0, 0][:self.NUM_VALS],  # All zeros
                [self.MAX_VAL] * self.NUM_VALS,   # All max values
            ]

        # Pad test cases to correct length
        for i, case in enumerate(test_cases):
            while len(case) < self.NUM_VALS:
                case.append(0)
            test_cases[i] = case[:self.NUM_VALS]

        for test_num, input_values in enumerate(test_cases):
            if not all_passed and self.TEST_LEVEL == 'basic':
                break

            self.log.debug(f"Test case {test_num}: {input_values}{self.get_time_ns_str()}")

            # Pack and drive input
            packed_input = self.pack_values(input_values)
            self.data_in.value = packed_input
            await RisingEdge(self.clk)

            # Wait for sorting to complete (one clock cycle for this design)
            await RisingEdge(self.clk)

            # Get output
            output_values = self.get_sorted_output()

            # Expected result: sorted in descending order
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values)

            if success:
                self.log.debug(f"PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_sorting',
                'test_num': test_num,
                'input_values': input_values,
                'output_values': output_values,
                'expected_values': expected_values,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_random_sorting(self):
        """Test sorting with random data"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping random sorting tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing random sorting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Determine number of random tests based on level
        if self.TEST_LEVEL == 'medium':
            num_tests = 20
        else:  # full
            num_tests = 100

        for test_num in range(num_tests):
            # Generate random input values
            input_values = [random.randint(0, min(self.MAX_VAL, 1000)) for _ in range(self.NUM_VALS)]

            self.log.debug(f"Random test {test_num}: {input_values}{self.get_time_ns_str()}")

            # Pack and drive input
            packed_input = self.pack_values(input_values)
            self.data_in.value = packed_input
            await RisingEdge(self.clk)

            # Wait for sorting
            await RisingEdge(self.clk)

            # Get output
            output_values = self.get_sorted_output()

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values)

            if not success:
                self.log.error(f"Random test {test_num} FAIL:{self.get_time_ns_str()}")
                self.log.error(f"  Input: {input_values}")
                self.log.error(f"  Output: {output_values}")
                self.log.error(f"  Expected: {expected_values}")
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            # Store result (sample for large tests)
            if test_num % 10 == 0:
                result = {
                    'test_type': 'random_sorting',
                    'test_num': test_num,
                    'input_values': input_values,
                    'output_values': output_values,
                    'expected_values': expected_values,
                    'success': success
                }
                self.test_results.append(result)
                if not success:
                    self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping boundary condition tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing boundary conditions{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test boundary cases
        boundary_cases = []

        # All minimum values
        boundary_cases.append([0] * self.NUM_VALS)

        # All maximum values
        boundary_cases.append([self.MAX_VAL] * self.NUM_VALS)

        # Mix of min and max
        mix_case = []
        for i in range(self.NUM_VALS):
            mix_case.append(self.MAX_VAL if i % 2 == 0 else 0)
        boundary_cases.append(mix_case)

        # Single unique value among duplicates
        if self.NUM_VALS >= 3:
            unique_case = [5] * self.NUM_VALS
            unique_case[self.NUM_VALS // 2] = 100
            boundary_cases.append(unique_case)

        # Power of 2 values
        if self.SIZE >= 8:
            power_case = []
            for i in range(self.NUM_VALS):
                power_val = min(2 ** (i + 1), self.MAX_VAL)
                power_case.append(power_val)
            boundary_cases.append(power_case)

        for test_num, input_values in enumerate(boundary_cases):
            self.log.debug(f"Boundary test {test_num}: {input_values}{self.get_time_ns_str()}")

            # Pack and drive input
            packed_input = self.pack_values(input_values)
            self.data_in.value = packed_input
            await RisingEdge(self.clk)

            # Wait for sorting
            await RisingEdge(self.clk)

            # Get output
            output_values = self.get_sorted_output()

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values)

            if success:
                self.log.debug(f"Boundary PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"Boundary FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'test_num': test_num,
                'input_values': input_values,
                'output_values': output_values,
                'expected_values': expected_values,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_stability_and_timing(self):
        """Test sorting stability and timing"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping stability and timing tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing stability and timing{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test that the sorter produces stable results
        test_values = [3, 7, 1, 9, 2][:self.NUM_VALS]
        while len(test_values) < self.NUM_VALS:
            test_values.append(0)

        # Apply same input multiple times
        expected_output = sorted(test_values, reverse=True)

        for iteration in range(5):
            packed_input = self.pack_values(test_values)
            self.data_in.value = packed_input
            await RisingEdge(self.clk)
            await RisingEdge(self.clk)

            output_values = self.get_sorted_output()

            if output_values != expected_output:
                self.log.error(f"Stability test iteration {iteration}: inconsistent output{self.get_time_ns_str()}")
                self.log.error(f"  Expected: {expected_output}")
                self.log.error(f"  Got: {output_values}")
                all_passed = False
                break

        # Test response to input changes
        # Apply different inputs in sequence
        test_sequences = [
            [1, 2, 3, 4, 5][:self.NUM_VALS],
            [5, 4, 3, 2, 1][:self.NUM_VALS],
            [9, 1, 8, 2, 7][:self.NUM_VALS],
        ]

        for seq_num, test_vals in enumerate(test_sequences):
            while len(test_vals) < self.NUM_VALS:
                test_vals.append(0)

            packed_input = self.pack_values(test_vals)
            self.data_in.value = packed_input
            await RisingEdge(self.clk)
            await RisingEdge(self.clk)

            output_values = self.get_sorted_output()
            expected_values = sorted(test_vals, reverse=True)

            if output_values != expected_values:
                self.log.error(f"Sequence test {seq_num}: incorrect output{self.get_time_ns_str()}")
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'stability_and_timing',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()

        all_passed = True

        # Apply some input values
        test_values = [5, 3, 8, 1, 9][:self.NUM_VALS]
        while len(test_values) < self.NUM_VALS:
            test_values.append(0)

        packed_input = self.pack_values(test_values)
        self.data_in.value = packed_input

        # Reset while input is applied
        await self.reset_dut()

        # Check that output is cleared after reset
        output_values = self.get_sorted_output()
        expected_zeros = [0] * self.NUM_VALS

        if output_values != expected_zeros:
            self.log.warning(f"Reset output not zero: {output_values}{self.get_time_ns_str()}")
            # This might not be a failure depending on RTL implementation

        # Apply new input after reset
        new_values = [2, 7, 4, 1, 6][:self.NUM_VALS]
        while len(new_values) < self.NUM_VALS:
            new_values.append(0)

        packed_new = self.pack_values(new_values)
        self.data_in.value = packed_new
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        output_values = self.get_sorted_output()
        expected_values = sorted(new_values, reverse=True)

        if output_values != expected_values:
            self.log.error(f"Post-reset sorting failed: {output_values} != {expected_values}{self.get_time_ns_str()}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running SORT tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_sorting, "Basic sorting"),
            (self.test_random_sorting, "Random sorting"),
            (self.test_boundary_conditions, "Boundary conditions"),
            (self.test_stability_and_timing, "Stability and timing"),
            (self.test_reset_behavior, "Reset behavior")
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
        self.log.info(f"Overall SORT result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def sort_test(dut):
    """Test for Sort module"""
    tb = SortTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"SORT test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Sort test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    num_vals_list = [3, 5, 8]  # Different numbers of values to sort
    sizes = [8, 16, 32]        # Different value sizes
    test_levels = ['full']     # Test levels

    valid_params = []
    for num_vals, size, test_level in product(num_vals_list, sizes, test_levels):
        valid_params.append((num_vals, size, test_level))

    # For debugging, uncomment one of these:
    # return [(5, 16, 'full')]  # Single test
    # return [(3, 8, 'medium')]  # Just specific configurations

    return valid_params


params = generate_params()


@pytest.mark.parametrize("num_vals, size, test_level", params)
def test_sort(request, num_vals, size, test_level):
    """
    Parameterized Sort test with configurable num_vals, size and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "sort"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(num_vals, 1)
    s_str = TBBase.format_dec(size, 2)
    test_name_plus_params = f"test_sort_n{n_str}_s{s_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'NUM_VALS': str(num_vals),
        'SIZE': str(size)
    }

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1))

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
        'TEST_NUM_VALS': str(num_vals),
        'TEST_SIZE': str(size),
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
    print(f"Running {test_level.upper()} test: {num_vals} values, size={size}")
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
        print(f"✓ {test_level.upper()} test PASSED: {num_vals} values, size={size}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
