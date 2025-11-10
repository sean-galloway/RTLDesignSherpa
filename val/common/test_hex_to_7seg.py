# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HexTo7SegTB
# Purpose: Hexadecimal to 7-Segment Display Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Hexadecimal to 7-Segment Display Converter Test

This test verifies the hex to 7-segment display conversion functionality:

CONFIGURATION:
    Fixed 4-bit hex input, 7-bit segment output

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility

7-SEGMENT DISPLAY BEHAVIOR:
    Converts 4-bit hex values (0x0-0xF) to 7-segment display patterns
    Segments are typically arranged as:
         a
       f   b
         g
       e   c
         d
    
    Output format: {g,f,e,d,c,b,a} where 0=on, 1=off (common anode)
"""

import os
import sys
import random
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

class HexTo7SegTB(TBBase):
    """Testbench for Hexadecimal to 7-Segment Display Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"HexTo7Seg TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Expected 7-segment patterns (common anode: 0=on, 1=off)
        # Format: {g,f,e,d,c,b,a}
        self.expected_patterns = {
            0x0: 0b1000000,  # 0
            0x1: 0b1111001,  # 1
            0x2: 0b0100100,  # 2
            0x3: 0b0110000,  # 3
            0x4: 0b0011001,  # 4
            0x5: 0b0010010,  # 5
            0x6: 0b0000010,  # 6
            0x7: 0b1111000,  # 7
            0x8: 0b0000000,  # 8
            0x9: 0b0011000,  # 9
            0xA: 0b0001000,  # A
            0xB: 0b0000011,  # b
            0xC: 0b1000110,  # C
            0xD: 0b0100001,  # d
            0xE: 0b0000110,  # E
            0xF: 0b0001110,  # F
        }

        # Segment names for debugging
        self.segment_names = ['a', 'b', 'c', 'd', 'e', 'f', 'g']

    def _setup_signals(self):
        """Setup signal mappings"""
        self.hex = self.dut.hex
        self.seg = self.dut.seg

    def format_7seg_pattern(self, pattern):
        """Format 7-segment pattern for display"""
        # Convert to binary string with segment labels
        segments = []
        for i, name in enumerate(self.segment_names):
            bit_val = (pattern >> i) & 1
            segments.append(f"{name}:{bit_val}")
        return f"0b{pattern:07b} ({', '.join(segments)})"

    def get_hex_char(self, hex_val):
        """Get character representation of hex value"""
        if hex_val < 10:
            return str(hex_val)
        else:
            return chr(ord('A') + hex_val - 10)

    async def check_conversion(self, hex_val):
        """Check a single hex to 7-segment conversion"""
        self.hex.value = hex_val
        await Timer(1, units='ns')  # Allow combinational logic to settle
        
        actual_seg = int(self.seg.value)
        expected_seg = self.expected_patterns.get(hex_val, 0b1111111)  # All off for invalid
        
        success = actual_seg == expected_seg
        
        if not success or self.DEBUG:
            hex_char = self.get_hex_char(hex_val)
            self.log.info(f"Hex: 0x{hex_val:X} ({hex_char}) "
                         f"-> 7-seg: {self.format_7seg_pattern(actual_seg)} "
                         f"(Expected: {self.format_7seg_pattern(expected_seg)}) "
                         f"{'✓' if success else '✗'}")
        
        return success, actual_seg, expected_seg

    async def test_all_hex_values(self):
        """Test all 16 hex values (0x0 to 0xF)"""
        self.log.info(f"Testing all hex values (0x0 to 0xF)")
        
        all_passed = True
        failed_count = 0
        
        for hex_val in range(16):
            success, actual, expected = await self.check_conversion(hex_val)
            
            if not success:
                failed_count += 1
                all_passed = False
                
                # Store failure
                result = {
                    'test_type': 'all_hex_values',
                    'hex_input': hex_val,
                    'expected_seg': expected,
                    'actual_seg': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'all_hex_values',
            'total_tests': 16,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"All hex values test: 16 tests, {failed_count} failures")
        
        return all_passed

    async def test_invalid_inputs(self):
        """Test behavior with invalid inputs (should not occur in practice)"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping invalid input test")
            return True

        self.log.info(f"Testing invalid inputs (if any)")
        
        all_passed = True
        failed_count = 0
        
        # Test values beyond 0xF (though 4-bit input should prevent this)
        # This tests the default case in the RTL
        invalid_values = []
        
        # If we somehow get values > 15, test the default case
        # In practice, this won't happen with 4-bit input, but tests the RTL robustness
        
        # For this module, all 4-bit values are valid, so this test passes trivially
        result = {
            'test_type': 'invalid_inputs',
            'total_tests': 0,
            'failures': 0,
            'success': True,
            'note': 'All 4-bit inputs are valid for hex to 7-segment'
        }
        self.test_results.append(result)

        self.log.info(f"Invalid input test: No invalid inputs for 4-bit hex")
        
        return True

    async def test_segment_patterns(self):
        """Test specific segment patterns for correctness"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping segment pattern analysis")
            return True

        self.log.info(f"Testing segment pattern correctness")
        
        all_passed = True
        failed_count = 0
        
        # Test specific characteristics of each display pattern
        pattern_tests = [
            # (hex_value, test_description, test_function)
            (0x0, "Digit 0 - all segments except g", lambda p: (p & 0b1000000) == 0b1000000 and (p & 0b0111111) == 0b0000000),
            (0x1, "Digit 1 - only b,c segments", lambda p: (p & 0b0000110) == 0b0000000 and (p & 0b1111001) == 0b1111001),
            (0x8, "Digit 8 - all segments on", lambda p: p == 0b0000000),
            (0xF, "Digit F - segments a,f,g,e on", lambda p: p == 0b0001110),  # Fixed: exact match
        ]
        
        for hex_val, description, test_func in pattern_tests:
            success, actual, expected = await self.check_conversion(hex_val)
            
            if not success:
                failed_count += 1
                all_passed = False
                continue
            
            # Run the specific pattern test
            pattern_valid = test_func(actual)
            
            if not pattern_valid:
                failed_count += 1
                all_passed = False
                
                self.log.error(f"Pattern test failed: {description}, "
                             f"hex=0x{hex_val:X}, pattern={self.format_7seg_pattern(actual)}")
                
                # Store failure
                result = {
                    'test_type': 'segment_patterns',
                    'hex_input': hex_val,
                    'description': description,
                    'actual_seg': actual,
                    'pattern_valid': pattern_valid,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'segment_patterns',
            'total_tests': len(pattern_tests),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Segment pattern test: {len(pattern_tests)} tests, {failed_count} failures")
        
        return all_passed

    async def test_repeated_inputs(self):
        """Test that repeated inputs give consistent outputs"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping repeated input test")
            return True

        self.log.info(f"Testing repeated inputs for consistency")
        
        all_passed = True
        failed_count = 0
        
        # Test each hex value multiple times
        num_repeats = 5 if self.TEST_LEVEL == 'medium' else 10
        
        for hex_val in range(16):
            first_result = None
            
            for repeat in range(num_repeats):
                success, actual, expected = await self.check_conversion(hex_val)
                
                if not success:
                    failed_count += 1
                    all_passed = False
                    break
                
                if first_result is None:
                    first_result = actual
                elif actual != first_result:
                    failed_count += 1
                    all_passed = False
                    
                    self.log.error(f"Inconsistent result for hex=0x{hex_val:X}, "
                                 f"repeat={repeat}, first={first_result:07b}, "
                                 f"current={actual:07b}")
                    
                    # Store failure
                    result = {
                        'test_type': 'repeated_inputs',
                        'hex_input': hex_val,
                        'repeat_number': repeat,
                        'first_result': first_result,
                        'current_result': actual,
                        'success': False
                    }
                    self.test_failures.append(result)
                    break

        # Store summary result
        result = {
            'test_type': 'repeated_inputs',
            'total_tests': 16 * num_repeats,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Repeated input test: {16 * num_repeats} tests, {failed_count} failures")
        
        return all_passed

    async def test_timing_characteristics(self):
        """Test timing characteristics (combinational delay)"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping timing characteristics test")
            return True

        self.log.info(f"Testing timing characteristics")
        
        all_passed = True
        failed_count = 0
        
        # Test rapid input changes
        for i in range(50):  # 50 rapid changes
            hex_val1 = random.randint(0, 15)
            hex_val2 = random.randint(0, 15)
            
            # Set first value
            self.hex.value = hex_val1
            await Timer(0.1, units='ns')  # Very short delay
            result1 = int(self.seg.value)
            
            # Change to second value
            self.hex.value = hex_val2
            await Timer(0.1, units='ns')  # Very short delay
            result2 = int(self.seg.value)
            
            # Check final result after settling
            await Timer(1, units='ns')
            final_result = int(self.seg.value)
            
            expected1 = self.expected_patterns.get(hex_val1, 0b1111111)
            expected2 = self.expected_patterns.get(hex_val2, 0b1111111)
            
            # Final result should match second input
            if final_result != expected2:
                failed_count += 1
                all_passed = False
                
                self.log.error(f"Timing test failed: hex1=0x{hex_val1:X}, "
                             f"hex2=0x{hex_val2:X}, final_result={final_result:07b}, "
                             f"expected={expected2:07b}")

        # Store summary result
        result = {
            'test_type': 'timing_characteristics',
            'total_tests': 50,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Timing characteristics test: 50 tests, {failed_count} failures")
        
        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running HEX_TO_7SEG tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_all_hex_values, "All hex values"),
            (self.test_invalid_inputs, "Invalid inputs"),
            (self.test_repeated_inputs, "Repeated inputs"),
            (self.test_segment_patterns, "Segment patterns"),
            (self.test_timing_characteristics, "Timing characteristics")
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
        self.log.info(f"Overall HEX_TO_7SEG result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=30, timeout_unit="us")
async def hex_to_7seg_test(dut):
    """Test for Hexadecimal to 7-Segment Display Converter module"""
    tb = HexTo7SegTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"HEX_TO_7SEG test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"HexTo7Seg test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters"""
    # Only test level varies for this module (fixed 4-bit input)
    test_levels = ['full']

    valid_params = []
    for test_level in test_levels:
        valid_params.append((test_level,))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("test_level", params)
def test_hex_to_7seg(request, test_level):
    """
    Parameterized Hexadecimal to 7-Segment Display Converter test
    """
    # Extract test_level from tuple
    if isinstance(test_level, tuple):
        test_level = test_level[0]
    
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "hex_to_7seg"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/hex_to_7seg.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    test_name_plus_params = f"test_hex_to_7seg_{test_level}_{reg_level}"

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

    # No RTL parameters needed for this module
    parameters = {}

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 3}
    base_timeout = 3000  # 3 seconds base
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
        'TEST_DEBUG': '1' if test_level == 'full' else '0',
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
    print(f"Running {test_level.upper()} test: hex_to_7seg")
    print(f"Testing all 16 hex values (0x0-0xF)")
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
        print(f"✓ {test_level.upper()} test PASSED: hex_to_7seg")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
