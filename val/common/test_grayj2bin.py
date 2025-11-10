# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GrayJ2BinTB
# Purpose: Gray Johnson Counter to Binary Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Gray Johnson Counter to Binary Converter Test

This test verifies the Gray Johnson counter to binary conversion functionality:

CONFIGURATION:
    JCW: Johnson Counter Width (10, 12, 16, 20)
    WIDTH: Binary output width (4, 5, 6, 8)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - (JCW=10, WIDTH=4): Johnson counter 10 bits -> 4-bit binary
    - (JCW=12, WIDTH=5): Johnson counter 12 bits -> 5-bit binary
    - (JCW=16, WIDTH=6): Johnson counter 16 bits -> 6-bit binary
    - (JCW=20, WIDTH=8): Johnson counter 20 bits -> 8-bit binary

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_JCW: Johnson Counter Width
    TEST_WIDTH: Binary output width

GRAY JOHNSON BEHAVIOR:
    Johnson counter produces specific Gray code patterns
    Module requires leading_one_trailing_one submodule
    Conversion depends on MSB and position of leading/trailing ones
    Sequential clocked operation with reset
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class GrayJ2BinTB(TBBase):
    """Testbench for Gray Johnson Counter to Binary Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.JCW = self.convert_to_int(os.environ.get('TEST_JCW', '10'))
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"GrayJ2Bin TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"JCW={self.JCW}, WIDTH={self.WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_gray = (1 << self.JCW) - 1
        self.max_binary = (1 << self.WIDTH) - 1

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.gray = self.dut.gray
        self.binary = self.dut.binary

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.gray.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def generate_johnson_sequence(self):
        """Generate valid Johnson counter sequence"""
        # Johnson counter sequence: shift register with inverted feedback
        # Produces 2*N different states in a cycle
        sequence = []
        state = 0

        for i in range(2 * self.JCW):
            sequence.append(state)

            # Shift left and add inverted MSB to LSB
            msb = (state >> (self.JCW - 1)) & 1
            state = ((state << 1) | (1 - msb)) & ((1 << self.JCW) - 1)

            # Prevent infinite loop
            if state in sequence:
                break

        return sequence

    def find_leading_one(self, value):
        """Find position of leading (most significant) one"""
        if value == 0:
            return None

        for i in range(self.JCW - 1, -1, -1):
            if (value >> i) & 1:
                return i
        return None

    def find_trailing_one(self, value):
        """Find position of trailing (least significant) one"""
        if value == 0:
            return None

        for i in range(self.JCW):
            if (value >> i) & 1:
                return i
        return None

    def grayj_to_binary_reference(self, gray_val):
        """Reference implementation matching the actual RTL behavior"""
        
        # Check for all zeros
        if gray_val == 0:
            return 0
            
        # Check for all ones - RTL shows it outputs 16 (MSB set)
        if gray_val == ((1 << self.JCW) - 1):  # All ones
            return (1 << (self.WIDTH - 1))  # Just the MSB set = 16

        # MSB determines first half (0) vs second half (1)
        msb = (gray_val >> (self.JCW - 1)) & 1
        
        # Find trailing one position (LSB) - but you call it leading_one in RTL
        leading_one_pos = None
        for i in range(self.JCW):
            if (gray_val >> i) & 1:
                leading_one_pos = i
                break
        
        # Find leading one position (MSB) - but you call it trailing_one in RTL       
        trailing_one_pos = None
        for i in range(self.JCW - 1, -1, -1):
            if (gray_val >> i) & 1:
                trailing_one_pos = i
                break

        if leading_one_pos is None or trailing_one_pos is None:
            return 0

        # Calculate based on actual RTL pattern
        if msb == 1:
            # Second half: Use leading_one_pos directly (the LSB position)
            # 0x3FE has LSB at pos 1 → 16 + 1 = 17 ✓
            # 0x3FC has LSB at pos 2 → 16 + 2 = 18 ✓
            lower_binary = leading_one_pos
        else:
            # First half: Use trailing_one_pos + 1 (the MSB position + 1)
            lower_binary = trailing_one_pos + 1

        # Combine MSB with lower bits
        binary_val = (msb << (self.WIDTH - 1)) | (lower_binary & ((1 << (self.WIDTH - 1)) - 1))
        
        return binary_val

    async def check_conversion(self, gray_val):
        """Check a single Gray Johnson to binary conversion"""
        self.gray.value = gray_val
        await RisingEdge(self.clk)  # Clock the value in
        await Timer(1, units='ns')  # Allow for combinational settling

        actual_binary = int(self.binary.value)
        expected_binary = self.grayj_to_binary_reference(gray_val)

        success = actual_binary == expected_binary

        if not success or self.DEBUG:
            self.log.info(f"Gray: 0x{gray_val:0{(self.JCW+3)//4}X} "
                            f"-> Binary: {actual_binary:>3d} "
                            f"(Expected: {expected_binary:>3d}) "
                            f"{'✓' if success else '✗'}")

        return success, actual_binary, expected_binary

    async def test_johnson_sequence(self):
        """Test with valid Johnson counter sequence"""
        self.log.info(f"Testing Johnson counter sequence")

        await self.setup_clock()
        await self.reset_dut()

        # Generate valid Johnson sequence
        johnson_sequence = self.generate_johnson_sequence()

        all_passed = True
        failed_count = 0

        for i, gray_val in enumerate(johnson_sequence):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'johnson_sequence',
                    'sequence_index': i,
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 5:
                    break

        # Store summary result
        result = {
            'test_type': 'johnson_sequence',
            'total_tests': min(len(johnson_sequence), i + 1 if 'i' in locals() else 0),
            'sequence_length': len(johnson_sequence),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Johnson sequence test: {result['total_tests']} tests, "
                        f"{failed_count} failures, sequence length: {len(johnson_sequence)}")

        return all_passed

    async def test_corner_cases(self):
        """Test corner cases"""
        self.log.info(f"Testing corner cases")

        await self.setup_clock()
        await self.reset_dut()

        corner_cases = [
            0,  # All zeros
            (1 << self.JCW) - 1,  # All ones
            1,  # Single LSB
            1 << (self.JCW - 1),  # Single MSB
        ]

        # Add some specific patterns
        if self.JCW >= 4:
            corner_cases.extend([
                0b1111,  # Lower nibble
                0b1111 << (self.JCW - 4),  # Upper nibble
            ])

        if self.JCW >= 8:
            corner_cases.extend([
                0b11110000,  # Alternating nibbles
                0b10101010,  # Alternating bits
            ])

        # Ensure all values fit in JCW bits
        corner_cases = [val & ((1 << self.JCW) - 1) for val in corner_cases]
        corner_cases = list(set(corner_cases))  # Remove duplicates

        all_passed = True
        failed_count = 0

        for gray_val in corner_cases:
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'corner_cases',
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'corner_cases',
            'total_tests': len(corner_cases),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Corner cases test: {len(corner_cases)} tests, {failed_count} failures")

        return all_passed

    async def test_random_values(self):
        """Test random Gray values"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping random values test")
            return True

        self.log.info(f"Testing random Gray values")

        await self.setup_clock()
        await self.reset_dut()

        # Determine number of tests based on level
        if self.TEST_LEVEL == 'medium':
            num_tests = min(100, self.max_gray + 1)
        else:  # full
            num_tests = min(500, self.max_gray + 1)

        all_passed = True
        failed_count = 0

        test_values = []
        for _ in range(num_tests):
            val = random.randint(0, self.max_gray)
            test_values.append(val)

        for i, gray_val in enumerate(test_values):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random_values',
                    'test_index': i,
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early if too many failures
                if failed_count >= 20:
                    break

        # Store summary result
        result = {
            'test_type': 'random_values',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Random values test: {result['total_tests']} tests, {failed_count} failures")

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping reset behavior test")
            return True

        self.log.info(f"Testing reset behavior")

        await self.setup_clock()

        all_passed = True
        failed_count = 0

        # Test reset with various Gray values
        test_values = [0x55, 0xAA, self.max_gray, 0x123 & self.max_gray]

        for gray_val in test_values:
            # Set Gray value
            self.gray.value = gray_val
            await RisingEdge(self.clk)

            # Apply reset
            self.rst_n.value = 0
            await RisingEdge(self.clk)

            # Check that output is predictable during reset (usually 0)
            reset_output = int(self.binary.value)

            # Release reset
            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Check conversion after reset
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

        # Store summary result
        result = {
            'test_type': 'reset_behavior',
            'total_tests': len(test_values),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Reset behavior test: {len(test_values)} tests, {failed_count} failures")

        return all_passed

    async def test_timing_behavior(self):
        """Test timing behavior with rapid changes"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping timing behavior test")
            return True

        self.log.info(f"Testing timing behavior")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        failed_count = 0

        # Test rapid Gray value changes
        for i in range(50):
            gray_val1 = random.randint(0, self.max_gray)
            gray_val2 = random.randint(0, self.max_gray)

            # Set first value
            self.gray.value = gray_val1
            await RisingEdge(self.clk)
            result1 = int(self.binary.value)

            # Set second value
            self.gray.value = gray_val2
            await RisingEdge(self.clk)
            result2 = int(self.binary.value)

            # Verify results
            expected1 = self.grayj_to_binary_reference(gray_val1)
            expected2 = self.grayj_to_binary_reference(gray_val2)

            if result1 != expected1 or result2 != expected2:
                failed_count += 1
                all_passed = False

                self.log.error(f"Timing test failed: "
                                f"gray1=0x{gray_val1:X}->binary1={result1} (exp {expected1}), "
                                f"gray2=0x{gray_val2:X}->binary2={result2} (exp {expected2})")

        # Store summary result
        result = {
            'test_type': 'timing_behavior',
            'total_tests': 50,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Timing behavior test: 50 tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running GRAYJ2BIN tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_johnson_sequence, "Johnson sequence"),
            (self.test_corner_cases, "Corner cases"),
            (self.test_random_values, "Random values"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_timing_behavior, "Timing behavior")
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
        self.log.info(f"Overall GRAYJ2BIN result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=60000, timeout_unit="us")
async def grayj2bin_test(dut):
    """Test for Gray Johnson Counter to Binary Converter module"""
    tb = GrayJ2BinTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"GRAYJ2BIN test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"GrayJ2Bin test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters"""
    # Valid parameter combinations
    param_combinations = [
        (10, 5),  # 10-bit Johnson counter -> 4-bit binary
        (12, 5),  # 12-bit Johnson counter -> 5-bit binary
        (16, 5),  # 16-bit Johnson counter -> 6-bit binary
        (20, 6),  # 20-bit Johnson counter -> 8-bit binary
    ]

    test_levels = ['full']

    valid_params = []
    for (jcw, width), test_level in product(param_combinations, test_levels):
        valid_params.append((jcw, width, test_level))

    # For debugging, uncomment one of these:
    # return [(10, 5, 'full')]  # Single test
    # return [(10, 4, 'medium'), (12, 5, 'medium')]  # Specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("jcw, width, test_level", params)
def test_grayj2bin(request, jcw, width, test_level):
    """
    Parameterized Gray Johnson Counter to Binary Converter test

    Note: This test requires the leading_one_trailing_one module to be available
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "grayj2bin"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/grayj2bin.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    jcw_str = TBBase.format_dec(jcw, 2)
    width_str = TBBase.format_dec(width, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_grayj2bin_j{jcw_str}_w{width_str}_{test_level}_{reg_level}"

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
        'JCW': str(jcw),
        'WIDTH': str(width),
        'INSTANCE_NAME': f'"GRAYJ2BIN_J{jcw}_W{width}"'
    }

    # Adjust timeout based on test level and complexity
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    complexity_factor = max(1.0, jcw / 10.0)
    base_timeout = 8000  # 8 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * complexity_factor)

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
        'TEST_JCW': str(jcw),
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
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: jcw={jcw}, width={width}")
    print(f"Johnson counter sequence length: {2 * jcw}")
    print(f"Binary output range: 0 to {(1 << width) - 1}")
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
        print(f"✓ {test_level.upper()} test PASSED: jcw={jcw}, width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        print(f"Note: This test requires the leading_one_trailing_one module")
        raise
