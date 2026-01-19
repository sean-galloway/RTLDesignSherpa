# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FindLastSetTB
# Purpose: Find Last Set Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Find Last Set Test

This test verifies the find last set functionality:

CONFIGURATION:
    WIDTH: Bit width of the input vector (8, 16, 32, 64)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - WIDTH: [8, 16, 32, 64]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Bit width for input vector

FIND LAST SET BEHAVIOR:
    Finds the position of the last (most significant) set bit
    Returns WIDTH-1 if MSB is set, WIDTH-2 if second MSB is set, etc.
    Behavior when no bits are set depends on implementation
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from conftest import get_coverage_compile_args

class FindLastSetTB(TBBase):
    """Testbench for Find Last Set module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"FindLastSet TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_value = (1 << self.WIDTH) - 1
        self.index_width = math.ceil(math.log2(self.WIDTH)) if self.WIDTH > 1 else 1

    def _setup_signals(self):
        """Setup signal mappings"""
        self.data = self.dut.data
        self.index = self.dut.index

    def find_last_set_reference(self, data_val):
        """Reference implementation of find last set"""
        if data_val == 0:
            return 0  # Default when no bits are set

        for i in range(self.WIDTH - 1, -1, -1):
            if (data_val >> i) & 1:
                return i

        return 0  # Should not reach here if data_val != 0

    async def check_find_last_set(self, data_val):
        """Check a single find last set operation"""
        self.data.value = data_val
        await Timer(1, units='ns')  # Allow combinational logic to settle

        actual_index = int(self.index.value)
        expected_index = self.find_last_set_reference(data_val)

        success = actual_index == expected_index

        if not success or self.DEBUG:
            self.log.info(f"Data: 0x{data_val:0{(self.WIDTH+3)//4}X} "
                            f"-> Index: {actual_index} "
                            f"(Expected: {expected_index}) "
                            f"{'✓' if success else '✗'}")

        return success, actual_index, expected_index

    async def test_exhaustive(self):
        """Test all possible values (for small widths)"""
        if self.WIDTH > 20:
            self.log.info(f"Skipping exhaustive test for WIDTH={self.WIDTH} (too large)")
            return True

        self.log.info(f"Testing exhaustive find last set for WIDTH={self.WIDTH}")

        all_passed = True
        failed_count = 0

        for data_val in range(self.max_value + 1):
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'exhaustive',
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 5:
                    break

        # Store summary result
        result = {
            'test_type': 'exhaustive',
            'total_tests': min(self.max_value + 1, data_val + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Exhaustive test: {result['total_tests']} tests, "
                        f"{failed_count} failures")

        return all_passed

    async def test_random_values(self):
        """Test random values for larger widths"""
        self.log.info(f"Testing random find last set for WIDTH={self.WIDTH}")

        # Determine number of tests based on level
        if self.TEST_LEVEL == 'basic':
            num_tests = min(100, self.max_value + 1)
        elif self.TEST_LEVEL == 'medium':
            num_tests = min(1000, self.max_value + 1)
        else:  # full
            num_tests = min(10000, self.max_value + 1)

        all_passed = True
        failed_count = 0

        # Always test corner cases
        corner_cases = [0, 1, self.max_value, self.max_value - 1]

        # Add single bit patterns
        for i in range(self.WIDTH):
            corner_cases.append(1 << i)

        # Add patterns with multiple bits
        if self.WIDTH >= 4:
            corner_cases.extend([
                0b1010101010101010 & self.max_value,  # Alternating pattern
                0b0111111111111111 & self.max_value,  # All but MSB
                0b1111111111111110 & self.max_value,  # All but LSB
            ])

        # Remove duplicates and ensure within range
        corner_cases = list(set([val for val in corner_cases if val <= self.max_value]))

        test_values = corner_cases.copy()

        # Add random values
        while len(test_values) < num_tests:
            val = random.randint(0, self.max_value)
            if val not in test_values:
                test_values.append(val)

        test_values = test_values[:num_tests]

        for i, data_val in enumerate(test_values):
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random',
                    'test_index': i,
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 10:
                    break

        # Store summary result
        result = {
            'test_type': 'random',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'corner_cases_tested': len([v for v in corner_cases if v in test_values]),
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Random test: {result['total_tests']} tests, "
                        f"{failed_count} failures, "
                        f"{result['corner_cases_tested']} corner cases")

        return all_passed

    async def test_single_bit_patterns(self):
        """Test single bit patterns specifically"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping single bit pattern test")
            return True

        self.log.info(f"Testing single bit patterns")

        all_passed = True
        failed_count = 0

        # Test each bit position individually
        for bit_pos in range(self.WIDTH):
            data_val = 1 << bit_pos
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                self.log.error(f"Single bit test failed: bit_pos={bit_pos}, "
                                f"data=0x{data_val:X}, expected={expected}, actual={actual}")

                # Store failure
                result = {
                    'test_type': 'single_bit',
                    'bit_position': bit_pos,
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'single_bit_patterns',
            'total_tests': self.WIDTH,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Single bit pattern test: {self.WIDTH} tests, {failed_count} failures")

        return all_passed

    async def test_priority_behavior(self):
        """Test that the function correctly prioritizes higher bits"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping priority behavior test")
            return True

        self.log.info(f"Testing priority behavior")

        all_passed = True
        failed_count = 0

        # Test patterns where multiple bits are set
        test_patterns = []

        # For each bit position, test with lower bits also set
        for last_bit in range(min(self.WIDTH, 8), 0, -1):  # Start from higher bits
            for num_lower_bits in range(1, min(4, last_bit)):
                # Create pattern with last_bit set and some lower bits set
                pattern = 1 << (last_bit - 1)
                for i in range(num_lower_bits):
                    if last_bit - 2 - i >= 0:
                        pattern |= 1 << (last_bit - 2 - i)

                test_patterns.append((pattern, last_bit - 1))

        # Also test some specific patterns
        if self.WIDTH >= 8:
            test_patterns.extend([
                (0b01111111, self.WIDTH - 2 if self.WIDTH > 7 else 6),  # All bits set except MSB
                (0b00111111, self.WIDTH - 3 if self.WIDTH > 6 else 5),  # All bits set except top 2
                (0b00001111, 3),  # Lower nibble set
            ])

        for i, (pattern, expected_last_bit) in enumerate(test_patterns):
            if pattern > self.max_value:
                # Adjust pattern to fit within width
                pattern = pattern & self.max_value
                # Recalculate expected last bit
                expected_last_bit = self.find_last_set_reference(pattern)

            success, actual, expected = await self.check_find_last_set(pattern)

            # Verify the expected matches our test expectation
            if expected != expected_last_bit:
                self.log.error(f"Test setup error: pattern=0x{pattern:X}, "
                                f"expected_last_bit={expected_last_bit}, "
                                f"reference_result={expected}")
                continue

            if not success:
                failed_count += 1
                all_passed = False

                self.log.error(f"Priority test failed: pattern=0x{pattern:X}, "
                                f"expected_last_bit={expected_last_bit}, "
                                f"actual={actual}")

                # Store failure
                result = {
                    'test_type': 'priority_behavior',
                    'test_index': i,
                    'pattern': pattern,
                    'expected_last_bit': expected_last_bit,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'priority_behavior',
            'total_tests': len([p for p, _ in test_patterns if p <= self.max_value]),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Priority behavior test: {result['total_tests']} tests, {failed_count} failures")

        return all_passed

    async def test_complementary_with_ffs(self):
        """Test relationship with find_first_set for symmetric patterns"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping complementary FFS test")
            return True

        self.log.info(f"Testing complementary behavior with find_first_set")

        all_passed = True
        failed_count = 0

        # Test symmetric patterns
        num_tests = min(100, self.max_value + 1)

        for i in range(num_tests):
            # Test with single bit patterns
            if i < self.WIDTH:
                pattern = 1 << i

                # Find last set should return the bit position
                success, fls_result, fls_expected = await self.check_find_last_set(pattern)

                if not success:
                    failed_count += 1
                    all_passed = False
                    continue

                # For single bit, FLS should return the bit position
                if fls_result != i:
                    failed_count += 1
                    all_passed = False

                    self.log.error(f"Single bit FLS test failed: bit={i}, "
                                    f"pattern=0x{pattern:X}, result={fls_result}")

            # Test with random patterns
            else:
                pattern = random.randint(1, self.max_value)  # Avoid 0

                success, actual, expected = await self.check_find_last_set(pattern)

                if not success:
                    failed_count += 1
                    all_passed = False

        # Store summary result
        result = {
            'test_type': 'complementary_ffs',
            'total_tests': num_tests,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Complementary FFS test: {num_tests} tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running FIND_LAST_SET tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = []

        # Choose appropriate test strategy based on width
        if self.WIDTH <= 20:
            test_functions.append((self.test_exhaustive, "Exhaustive find last set"))
        else:
            test_functions.append((self.test_random_values, "Random value find last set"))

        if self.TEST_LEVEL in ['medium', 'full']:
            test_functions.append((self.test_single_bit_patterns, "Single bit patterns"))

        if self.TEST_LEVEL == 'full':
            test_functions.append((self.test_priority_behavior, "Priority behavior"))
            test_functions.append((self.test_complementary_with_ffs, "Complementary with FFS"))

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
        self.log.info(f"Overall FIND_LAST_SET result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=60000, timeout_unit="us")
async def find_last_set_test(dut):
    """Test for Find Last Set module"""
    tb = FindLastSetTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"FIND_LAST_SET test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"FindLastSet test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Minimal - just 8-bit
        widths = [8]
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        widths = [8, 16]
    else:  # FULL
        # FULL: All widths
        widths = [8, 16, 32, 64]

    test_levels = ['full']

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_find_last_set(request, width, test_level):
    """
    Parameterized Find Last Set test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "find_last_set"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/find_last_set.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_find_last_set_w{width_str}_{test_level}_{reg_level}"

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
        'WIDTH': str(width),
        'INSTANCE_NAME': f'"FLS_W{width}"'
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    width_factor = max(1.0, (1 << width) / 100000.0) if width <= 20 else max(1.0, width / 16.0)
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

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
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '0',
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}")
    print(f"Max values to test: {min(2**width, 10000) if width <= 20 else 10000}")
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
            includes=[],
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
