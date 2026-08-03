# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: HexTo7SegTB
# Purpose: Testbench for hex_to_7seg
# Subsystem: framework
#
# Extracted from val/common/test_hex_to_7seg.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.triggers import Timer
from TBClasses.shared.tbbase import TBBase


class HexTo7SegTB(TBBase):
    """Testbench for Hexadecimal to 7-Segment Display Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

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

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def deassert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def setup_clocks_and_reset(self):
        """Combinational DUT: no clock or reset to set up."""
        return

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
        if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping repeated input test")
            return True

        self.log.info(f"Testing repeated inputs for consistency")
        
        all_passed = True
        failed_count = 0
        
        # Test each hex value multiple times
        num_repeats = 5 if self.TEST_LEVEL == 'func' else 10
        
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
