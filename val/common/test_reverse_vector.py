# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ReverseVectorTB
# Purpose: Reverse Vector Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Reverse Vector Test with Parameterized Test Levels and Configuration

This test uses width and test_level as parameters for maximum flexibility:

CONFIGURATION:
    width:       Vector width (8, 16, 32, 64)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - width: [8, 16, 32, 64]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Vector width

RTL Interface:
    Input:  vector[WIDTH-1:0]      - Input vector to be reversed
    Output: vector_rev[WIDTH-1:0]  - Bit-reversed output vector
"""

import os
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class ReverseVectorTB(TBBase):
    """Testbench for Reverse Vector module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '32'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.MAX_VALUE = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Reverse Vector TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX_VALUE=0x{self.MAX_VALUE:x}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.vector_in = self.dut.vector_in
        self.vector_out = self.dut.vector_rev

    def _calculate_expected_reverse(self, input_value):
        """Calculate expected reversed vector"""
        input_value = input_value & self.MAX_VALUE
        reversed_value = 0

        for i in range(self.WIDTH):
            bit = (input_value >> i) & 1
            reversed_value |= bit << (self.WIDTH - 1 - i)

        return reversed_value

    async def test_basic_patterns(self):
        """Test basic bit patterns"""
        self.log.info("Testing basic patterns")

        # Define test patterns based on level
        test_patterns = []

        # Always test these basic cases
        test_patterns.extend([0, self.MAX_VALUE])

        # Single bit patterns
        if self.TEST_LEVEL == 'basic':
            # Test a few single bits
            bit_positions = [0, 1, self.WIDTH - 1] if self.WIDTH > 2 else [0, 1]
        elif self.TEST_LEVEL == 'medium':
            # Test more single bits
            bit_positions = [0, 1, 2, self.WIDTH // 2, self.WIDTH - 2, self.WIDTH - 1]
        else:  # full
            # Test all single bits
            bit_positions = list(range(self.WIDTH))

        # Add single bit patterns
        for pos in bit_positions:
            if pos < self.WIDTH:
                test_patterns.append(1 << pos)

        # Add some multi-bit patterns
        if self.TEST_LEVEL != 'basic':
            if self.WIDTH >= 8:
                test_patterns.extend([0x55555555 & self.MAX_VALUE, 0xAAAAAAAA & self.MAX_VALUE])
            test_patterns.extend([3, 7, 15])  # Small patterns

        if self.TEST_LEVEL == 'full':
            # Add more complex patterns
            test_patterns.extend([
                self.MAX_VALUE >> 1,  # All bits except MSB
                self.MAX_VALUE >> 2,  # All bits except 2 MSBs
                0xF0F0F0F0 & self.MAX_VALUE,  # Alternating nibbles
                0xFF00FF00 & self.MAX_VALUE,  # Alternating bytes
            ])

        # Remove duplicates and filter valid values
        test_patterns = sorted(list(set([v & self.MAX_VALUE for v in test_patterns])))

        all_passed = True

        for input_value in test_patterns:
            expected_output = self._calculate_expected_reverse(input_value)

            # Drive input
            self.vector_in.value = input_value
            await Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.vector_out.value)

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: 0x{input_value:0{(self.WIDTH+3)//4}x} → 0x{actual_output:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"FAIL: 0x{input_value:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected: 0x{expected_output:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Actual:   0x{actual_output:0{(self.WIDTH+3)//4}x}")
                await self._dump_reverse_debug_info(input_value, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_patterns',
                'input_value': input_value,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_random_patterns(self):
        """Test random bit patterns"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping random pattern tests")
            return True

        self.log.info("Testing random patterns")

        # Determine number of random tests based on level
        if self.TEST_LEVEL == 'medium':
            num_tests = min(100, 2 ** min(self.WIDTH, 10))
        else:  # full
            num_tests = min(500, 2 ** min(self.WIDTH, 12))

        all_passed = True

        for test_num in range(num_tests):
            input_value = random.randint(0, self.MAX_VALUE)
            expected_output = self._calculate_expected_reverse(input_value)

            # Drive input
            self.vector_in.value = input_value
            await Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.vector_out.value)

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"Random {test_num}: PASS 0x{input_value:0{(self.WIDTH+3)//4}x} → 0x{actual_output:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"Random {test_num}: FAIL 0x{input_value:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected: 0x{expected_output:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Actual:   0x{actual_output:0{(self.WIDTH+3)//4}x}")
                await self._dump_reverse_debug_info(input_value, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            # Store result (sample for large tests)
            if test_num % max(1, num_tests // 20) == 0:
                result = {
                    'test_type': 'random_patterns',
                    'test_num': test_num,
                    'input_value': input_value,
                    'expected_output': expected_output,
                    'actual_output': actual_output,
                    'success': success
                }
                self.test_results.append(result)
                if not success:
                    self.test_failures.append(result)

        return all_passed

    async def test_exhaustive_small_widths(self):
        """Test all possible values for small widths"""
        if self.TEST_LEVEL != 'full' or self.WIDTH > 16:
            self.log.info("Skipping exhaustive small width tests")
            return True

        self.log.info(f"Testing all {2**self.WIDTH} possible values")

        all_passed = True

        for input_value in range(2**self.WIDTH):
            expected_output = self._calculate_expected_reverse(input_value)

            # Drive input
            self.vector_in.value = input_value
            await Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.vector_out.value)

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Exhaustive: FAIL 0x{input_value:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected: 0x{expected_output:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Actual:   0x{actual_output:0{(self.WIDTH+3)//4}x}")
                await self._dump_reverse_debug_info(input_value, expected_output, actual_output)
                all_passed = False
                break
            else:
                if input_value % (2**(self.WIDTH-4)) == 0:  # Log progress
                    self.log.debug(f"Exhaustive: {input_value}/{2**self.WIDTH} completed")

            # Store result (sample for large tests)
            if input_value % max(1, 2**(self.WIDTH-8)) == 0:
                result = {
                    'test_type': 'exhaustive',
                    'input_value': input_value,
                    'expected_output': expected_output,
                    'actual_output': actual_output,
                    'success': success
                }
                self.test_results.append(result)

        return all_passed

    async def test_symmetry_property(self):
        """Test that reversing twice gives original value"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping symmetry property tests")
            return True

        self.log.info("Testing symmetry property (reverse twice = original)")

        all_passed = True

        # Test patterns for symmetry
        if self.TEST_LEVEL == 'medium':
            test_values = [0, 1, self.MAX_VALUE] + [random.randint(0, self.MAX_VALUE) for _ in range(10)]
        else:  # full
            test_values = [0, 1, self.MAX_VALUE] + [random.randint(0, self.MAX_VALUE) for _ in range(50)]

        for input_value in test_values:
            input_value = input_value & self.MAX_VALUE

            # First reverse
            first_reverse = self._calculate_expected_reverse(input_value)

            # Second reverse (should equal original)
            second_reverse = self._calculate_expected_reverse(first_reverse)

            success = (second_reverse == input_value)

            if success:
                self.log.debug(f"Symmetry PASS: 0x{input_value:0{(self.WIDTH+3)//4}x} → 0x{first_reverse:0{(self.WIDTH+3)//4}x} → 0x{second_reverse:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"Symmetry FAIL: 0x{input_value:0{(self.WIDTH+3)//4}x} → 0x{first_reverse:0{(self.WIDTH+3)//4}x} → 0x{second_reverse:0{(self.WIDTH+3)//4}x}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'symmetry_property',
                'input_value': input_value,
                'first_reverse': first_reverse,
                'second_reverse': second_reverse,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test specific boundary cases
        boundary_cases = [
            (0, "All zeros"),
            (self.MAX_VALUE, "All ones"),
            (1, "LSB only"),
            (1 << (self.WIDTH - 1), "MSB only"),
        ]

        # Add more boundary cases for larger widths
        if self.WIDTH > 8:
            boundary_cases.extend([
                (0x80000001 & self.MAX_VALUE, "MSB and LSB"),
                ((1 << (self.WIDTH // 2)) - 1, "Lower half ones"),
                (self.MAX_VALUE ^ ((1 << (self.WIDTH // 2)) - 1), "Upper half ones"),
            ])

        for input_value, description in boundary_cases:
            input_value = input_value & self.MAX_VALUE
            expected_output = self._calculate_expected_reverse(input_value)

            # Drive input
            self.vector_in.value = input_value
            await Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.vector_out.value)

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"Boundary {description}: PASS 0x{input_value:0{(self.WIDTH+3)//4}x} → 0x{actual_output:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"Boundary {description}: FAIL 0x{input_value:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected: 0x{expected_output:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Actual:   0x{actual_output:0{(self.WIDTH+3)//4}x}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'description': description,
                'input_value': input_value,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def _dump_reverse_debug_info(self, input_value, expected_output, actual_output):
        """Dump debug information for reverse failures"""
        self.log.error("="*80)
        self.log.error("REVERSE VECTOR FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input:    0x{input_value:0{(self.WIDTH+3)//4}x} ({input_value:0{self.WIDTH}b})")
        self.log.error(f"Expected: 0x{expected_output:0{(self.WIDTH+3)//4}x} ({expected_output:0{self.WIDTH}b})")
        self.log.error(f"Actual:   0x{actual_output:0{(self.WIDTH+3)//4}x} ({actual_output:0{self.WIDTH}b})")

        # Show bit-by-bit mapping
        self.log.error("Bit mapping analysis:")
        for i in range(self.WIDTH):
            input_bit = (input_value >> i) & 1
            expected_bit = (expected_output >> (self.WIDTH - 1 - i)) & 1
            actual_bit = (actual_output >> (self.WIDTH - 1 - i)) & 1
            match = "✓" if expected_bit == actual_bit else "✗"
            self.log.error(f"  Bit {i:2d} → Bit {self.WIDTH-1-i:2d}: {input_bit} → expected {expected_bit}, actual {actual_bit} {match}")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running REVERSE_VECTOR tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_patterns, "Basic patterns"),
            (self.test_random_patterns, "Random patterns"),
            (self.test_exhaustive_small_widths, "Exhaustive small widths"),
            (self.test_symmetry_property, "Symmetry property"),
            (self.test_boundary_conditions, "Boundary conditions")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}")
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
        self.log.info(f"Overall REVERSE_VECTOR result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def reverse_vector_test(dut):
    """Test for Reverse Vector module"""
    tb = ReverseVectorTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"REVERSE_VECTOR test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Reverse Vector test FAILED - {len(tb.test_failures)} failures detected"

    return passed


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    widths = [8, 16, 32, 64]  # Different vector widths
    test_levels = ['full']  # Test levels

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    # For debugging, uncomment one of these:
    # return [(8, 'full')]  # Single test
    # return [(16, 'medium')]  # Just specific configurations

    return valid_params


params = generate_params()


@pytest.mark.parametrize("width, test_level", params)
def test_reverse_vector(request, width, test_level):
    """
    Parameterized Reverse Vector test with configurable width and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "reverse_vector"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(width, 2)
    test_name_plus_params = f"test_reverse_vector_w{w_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width)
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, width / 32.0)  # Larger widths may take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

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
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}")
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
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
