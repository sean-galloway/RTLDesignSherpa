# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CountLeadingZerosTB
# Purpose: Testbench for count_leading_zeros
# Subsystem: framework
#
# Extracted from val/common/test_count_leading_zeros.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import math
from cocotb.triggers import Timer
from TBClasses.shared.tbbase import TBBase


class CountLeadingZerosTB(TBBase):
    """Testbench for Count Leading Zeros module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '32'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.OUTPUT_WIDTH = math.ceil(math.log2(self.WIDTH)) + 1 if self.WIDTH > 1 else 1
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Count Leading Zeros TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, OUTPUT_WIDTH={self.OUTPUT_WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

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
        self.data = self.dut.data
        self.count_leading_zeros = self.dut.clz

    def _calculate_expected_clz(self, data):
        """Count leading zeros: scan from the MSB down to the first set bit."""
        if data == 0:
            return self.WIDTH

        # Previously this modelled TRAILING zeros, because the RTL scanned from
        # bit 0 upward while being named count_leading_zeros. Both have been
        # corrected: the RTL now scans MSB-down, and count_trailing_zeros exists
        # as a separate module with its own test. Do not "fix" this back.
        clz = 0
        for i in range(self.WIDTH - 1, -1, -1):
            if (data >> i) & 1:
                break
            clz += 1
        return clz

    async def test_basic_patterns(self):
        """Test basic bit patterns"""
        self.log.info("Testing basic patterns")

        # Define test patterns based on level
        test_patterns = []
        
        # Always test these basic cases
        test_patterns.extend([0, self.MAX_DATA])
        
        # Single bit patterns
        if self.TEST_LEVEL == 'gate':
            # Test a few single bits
            bit_positions = [0, 1, self.WIDTH - 1] if self.WIDTH > 2 else [0, 1]
        elif self.TEST_LEVEL == 'func':
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
        if self.TEST_LEVEL != 'gate':
            # Add patterns with multiple bits set
            if self.WIDTH >= 8:
                test_patterns.extend([0x55555555 & self.MAX_DATA, 0xAAAAAAAA & self.MAX_DATA])
            test_patterns.extend([3, 7, 15])  # Small patterns
            
        if self.TEST_LEVEL == 'full':
            # Add more complex patterns
            test_patterns.extend([
                self.MAX_DATA >> 1,  # All bits except MSB
                self.MAX_DATA >> 2,  # All bits except 2 MSBs
                (self.MAX_DATA >> 4) if self.WIDTH > 4 else 1,
            ])

        # Remove duplicates and filter valid values
        test_patterns = sorted(list(set([v & self.MAX_DATA for v in test_patterns])))

        all_passed = True

        for data in test_patterns:
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"PASS: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b}) → clz={actual_clz}")
            else:
                self.log.error(f"FAIL: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'basic_patterns',
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_random_patterns(self):
        """Test random bit patterns"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping random pattern tests")
            return True

        self.log.info("Testing random patterns")

        # Determine number of random tests based on level
        if self.TEST_LEVEL == 'func':
            num_tests = min(100, 2 ** min(self.WIDTH, 10))
        else:  # full
            num_tests = min(500, 2 ** min(self.WIDTH, 12))

        all_passed = True

        for test_num in range(num_tests):
            data = random.randint(0, self.MAX_DATA)
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"Random {test_num}: PASS data=0x{data:0{(self.WIDTH+3)//4}x} → clz={actual_clz}")
            else:
                self.log.error(f"Random {test_num}: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    break

            # Store result
            result = {
                'test_type': 'random_patterns',
                'test_num': test_num,
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
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

        for data in range(2**self.WIDTH):
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if not success:
                self.log.error(f"Exhaustive: FAIL data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                break
            else:
                if data % (2**(self.WIDTH-4)) == 0:  # Log progress
                    self.log.debug(f"Exhaustive: {data}/{2**self.WIDTH} completed")

            # Store result (sample for large tests)
            if data % max(1, 2**(self.WIDTH-8)) == 0:
                result = {
                    'test_type': 'exhaustive',
                    'data': data,
                    'expected_clz': expected_clz,
                    'actual_clz': actual_clz,
                    'success': success
                }
                self.test_results.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping boundary condition tests")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test specific boundary cases
        boundary_cases = [
            (0, self.WIDTH),  # All zeros
            (1, self.WIDTH - 1),  # LSB only
            (self.MAX_DATA, 0),  # All ones
        ]

        # Add more boundary cases for larger widths
        if self.WIDTH > 8:
            boundary_cases.extend([
                (2, self.WIDTH - 2),  # Second bit only
                (self.MAX_DATA >> 1, 0),  # All except MSB
                (self.MAX_DATA >> 2, 0),  # All except 2 MSBs
            ])

        for data, expected_clz in boundary_cases:
            data = data & self.MAX_DATA
            expected_clz = self._calculate_expected_clz(data)  # Recalculate to be sure
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"Boundary: PASS data=0x{data:0{(self.WIDTH+3)//4}x} → clz={actual_clz}")
            else:
                self.log.error(f"Boundary: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def _dump_clz_debug_info(self, data, expected_clz, actual_clz):
        """Dump debug information for CLZ failures"""
        self.log.error("="*80)
        self.log.error("COUNT LEADING ZEROS FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input data: 0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
        self.log.error(f"Expected CLZ: {expected_clz}")
        self.log.error(f"Actual CLZ: {actual_clz}")

        # Show bit-by-bit analysis
        self.log.error("Bit analysis (LSB to MSB):")
        first_one_pos = None
        for i in range(self.WIDTH):
            bit_val = (data >> i) & 1
            marker = " <-- First 1" if bit_val == 1 and first_one_pos is None else ""
            if bit_val == 1 and first_one_pos is None:
                first_one_pos = i
            self.log.error(f"  Bit {i:2d}: {bit_val}{marker}")

        if first_one_pos is not None:
            self.log.error(f"First '1' found at position {first_one_pos} (CLZ should be {first_one_pos})")
        else:
            self.log.error(f"No '1' bits found (CLZ should be {self.WIDTH})")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running COUNT_LEADING_ZEROS tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_patterns, "Basic patterns"),
            (self.test_random_patterns, "Random patterns"),
            (self.test_exhaustive_small_widths, "Exhaustive small widths"),
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
        self.log.info(f"Overall COUNT_LEADING_ZEROS result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
