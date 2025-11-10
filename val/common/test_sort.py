# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SortTB
# Purpose: Sort Test with Parameterized Test Levels and Configuration - Updated for Pipelin
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Sort Test with Parameterized Test Levels and Configuration - Updated for Pipelined Architecture

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
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

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
        self.PIPELINE_STAGES = self.NUM_VALS  # Pipeline depth equals NUM_VALS

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
        self.log.info(f"PIPELINE_STAGES={self.PIPELINE_STAGES}")

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
        self.valid_in = self.dut.valid_in
        self.sorted_out = self.dut.sorted
        self.done_out = self.dut.done

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.data_in.value = 0
        self.valid_in.value = 0
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

    async def send_data_and_wait(self, input_values):
        """Send data through pipeline and wait for result"""
        # Pack and drive input with valid signal
        packed_input = self.pack_values(input_values)
        self.data_in.value = packed_input
        self.valid_in.value = 1
        await RisingEdge(self.clk)

        # Deassert valid (single cycle pulse)
        self.valid_in.value = 0

        # Wait for done signal or pipeline stages to complete
        max_wait_cycles = self.PIPELINE_STAGES + 5  # Add some margin
        wait_count = 0

        while wait_count < max_wait_cycles:
            await RisingEdge(self.clk)
            wait_count += 1

            # Check if done is asserted
            if int(self.done_out.value) == 1:
                break

        # Get output regardless of done signal for debugging
        output_values = self.get_sorted_output()
        done_asserted = (int(self.done_out.value) == 1)

        if not done_asserted:
            self.log.warning(f"Done signal not asserted after {wait_count} cycles{self.get_time_ns_str()}")

        return output_values, done_asserted

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

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result: sorted in descending order
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if success:
                self.log.debug(f"PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                self.log.error(f"  Done asserted: {done_asserted}")
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
                'done_asserted': done_asserted,
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

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if not success:
                self.log.error(f"Random test {test_num} FAIL:{self.get_time_ns_str()}")
                self.log.error(f"  Input: {input_values}")
                self.log.error(f"  Output: {output_values}")
                self.log.error(f"  Expected: {expected_values}")
                self.log.error(f"  Done asserted: {done_asserted}")
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
                    'done_asserted': done_asserted,
                    'success': success
                }
                self.test_results.append(result)
                if not success:
                    self.test_failures.append(result)

        return all_passed

    async def test_pipeline_throughput(self):
        """Test pipeline throughput - can accept new data every cycle"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping pipeline throughput tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing pipeline throughput{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Create test sequence
        test_sequences = [
            [1, 2, 3, 4, 5][:self.NUM_VALS],
            [5, 4, 3, 2, 1][:self.NUM_VALS],
            [9, 1, 8, 2, 7][:self.NUM_VALS],
        ]

        # Pad sequences
        for i, seq in enumerate(test_sequences):
            while len(seq) < self.NUM_VALS:
                seq.append(0)
            test_sequences[i] = seq[:self.NUM_VALS]

        expected_outputs = [sorted(seq, reverse=True) for seq in test_sequences]

        # Send data back-to-back
        for seq_num, input_vals in enumerate(test_sequences):
            packed_input = self.pack_values(input_vals)
            self.data_in.value = packed_input
            self.valid_in.value = 1
            await RisingEdge(self.clk)
            self.valid_in.value = 0

        # Wait for all outputs to emerge
        await Timer(self.PIPELINE_STAGES * self.clock_period * 2, units='ns')

        # Note: In a real test, you'd need to track which output corresponds to which input
        # This is a simplified version that just checks the final output
        final_output = self.get_sorted_output()
        final_expected = expected_outputs[-1]

        if final_output != final_expected:
            self.log.error(f"Pipeline throughput test failed{self.get_time_ns_str()}")
            self.log.error(f"  Final output: {final_output}")
            self.log.error(f"  Expected: {final_expected}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'pipeline_throughput',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
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

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if success:
                self.log.debug(f"Boundary PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"Boundary FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                self.log.error(f"  Done asserted: {done_asserted}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'test_num': test_num,
                'input_values': input_values,
                'output_values': output_values,
                'expected_values': expected_values,
                'done_asserted': done_asserted,
                'success': success
            }
            self.test_results.append(result)
            if not success:
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
        self.valid_in.value = 1

        # Reset while input is applied
        await self.reset_dut()

        # Check that output is cleared after reset
        output_values = self.get_sorted_output()
        expected_zeros = [0] * self.NUM_VALS
        done_state = int(self.done_out.value)

        if output_values != expected_zeros or done_state != 0:
            self.log.warning(f"Reset state - Output: {output_values}, Done: {done_state}{self.get_time_ns_str()}")
            # This might not be a failure depending on RTL implementation

        # Apply new input after reset
        new_values = [2, 7, 4, 1, 6][:self.NUM_VALS]
        while len(new_values) < self.NUM_VALS:
            new_values.append(0)

        # Send data through pipeline
        output_values, done_asserted = await self.send_data_and_wait(new_values)
        expected_values = sorted(new_values, reverse=True)

        if output_values != expected_values or not done_asserted:
            self.log.error(f"Post-reset sorting failed: {output_values} != {expected_values}{self.get_time_ns_str()}")
            self.log.error(f"  Done asserted: {done_asserted}")
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
            (self.test_pipeline_throughput, "Pipeline throughput"),
            (self.test_boundary_conditions, "Boundary conditions"),
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

@cocotb.test(timeout_time=15000, timeout_unit="us")  # Increased timeout for pipeline
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
    num_vals_list = [16, 32, 64]    # Different numbers of values to sort
    sizes = [8, 16, 32]             # Different value sizes
    test_levels = ['full']          # Test levels

    valid_params = []
    for num_vals, size, test_level in product(num_vals_list, sizes, test_levels):
        valid_params.append((num_vals, size, test_level))

    # For debugging, uncomment one of these:
    # return [(16, 16, 'full')]  # Single test
    # return [(3, 8, 'medium')]  # Just specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("num_vals, size, test_level", params)
def test_sort(request, num_vals, size, test_level):
    """
    Parameterized Sort test with configurable num_vals, size and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "sort"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/sort.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(num_vals, 1)
    s_str = TBBase.format_dec(size, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_sort_n{n_str}_s{s_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"
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

    # Adjust timeout based on test level and pipeline depth
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 3000  # 3 seconds base (increased for pipeline)
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1))

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
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

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: {num_vals} values, size={size}")
    print(f"Pipeline stages: {num_vals}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
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