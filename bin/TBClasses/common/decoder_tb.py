# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: DecoderTB
# Purpose: Testbench for decoder
# Subsystem: framework
#
# Extracted from val/common/test_decoder.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from TBClasses.shared.tbbase import TBBase


class DecoderTB(TBBase):
    """Testbench for Generic Decoder module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.INPUT_WIDTH = self.convert_to_int(os.environ.get('TEST_INPUT_WIDTH', '4'))
        self.OUTPUT_WIDTH = 2 ** self.INPUT_WIDTH
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Maximum values
        self.MAX_INPUT = (1 << self.INPUT_WIDTH) - 1
        self.MAX_OUTPUT = (1 << self.OUTPUT_WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Decoder TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"INPUT_WIDTH={self.INPUT_WIDTH}, OUTPUT_WIDTH={self.OUTPUT_WIDTH}")

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
        self.encoded = self.dut.encoded
        self.data = self.dut.data

    def _calculate_expected_output(self, input_val):
        """Calculate expected decoder output (one-hot encoding)"""
        input_val &= self.MAX_INPUT
        expected = 1 << input_val
        return expected & self.MAX_OUTPUT

    async def test_basic_decoding(self):
        """Test basic decoder functionality"""
        self.log.info("Testing basic decoder functionality")

        # Define test data based on level
        if self.TEST_LEVEL == 'gate':
            # Test all possible inputs for gate level (should be fast for small widths)
            test_values = list(range(min(self.OUTPUT_WIDTH, 16)))
        elif self.TEST_LEVEL == 'func':
            # Test all inputs for func widths, sample for large widths
            if self.INPUT_WIDTH <= 4:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                # Test corners and some random values
                test_values = [0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT]
                test_values.extend([random.randint(0, self.MAX_INPUT) for _ in range(16)])
        else:  # full
            # Test all inputs for reasonable widths, comprehensive sampling for large widths
            if self.INPUT_WIDTH <= 5:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                # Test systematic patterns
                test_values = [0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT]
                # Test walking bit patterns
                for bit_pos in range(self.INPUT_WIDTH):
                    test_values.append(1 << bit_pos)
                    test_values.append(self.MAX_INPUT ^ (1 << bit_pos))
                # Add random values
                test_values.extend([random.randint(0, self.MAX_INPUT) for _ in range(32)])

        # Remove duplicates and sort
        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values])))

        all_passed = True

        for input_val in test_values:
            input_val &= self.MAX_INPUT
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: encoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} → " +
                             f"data=0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x}")
            else:
                self.log.error(f"FAIL: encoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"expected=0x{expected_output:0{(self.OUTPUT_WIDTH+3)//4}x}, " +
                             f"actual=0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'basic_decoding',
                'input': input_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_one_hot_property(self):
        """Test that output is always one-hot (exactly one bit set)"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping one-hot property test for gate level")
            return True

        self.log.info("Testing one-hot property")

        # Test data based on level
        if self.TEST_LEVEL == 'func':
            test_values = [random.randint(0, self.MAX_INPUT) for _ in range(16)]
            test_values.extend([0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT])
        else:  # full
            if self.INPUT_WIDTH <= 5:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                test_values = [random.randint(0, self.MAX_INPUT) for _ in range(64)]
                test_values.extend([0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT])

        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values])))

        all_passed = True

        for input_val in test_values:
            input_val &= self.MAX_INPUT

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            # Count number of bits set
            bits_set = bin(actual_output).count('1')
            is_one_hot = (bits_set == 1)

            success = is_one_hot

            if success:
                self.log.debug(f"PASS: encoded=0x{input_val:x} → one-hot output (bits_set={bits_set})")
            else:
                self.log.error(f"FAIL: encoded=0x{input_val:x}, output=0x{actual_output:x}, " +
                             f"bits_set={bits_set} (should be 1)")
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    break

            # Store result
            result = {
                'test_type': 'one_hot_property',
                'input': input_val,
                'output': actual_output,
                'bits_set': bits_set,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping boundary condition tests for gate level")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test minimum and maximum values
        boundary_values = [0, self.MAX_INPUT]

        # Test power-of-2 values
        for i in range(self.INPUT_WIDTH):
            boundary_values.append(1 << i)
            boundary_values.append(self.MAX_INPUT ^ (1 << i))  # All bits except one

        boundary_values = sorted(list(set([val & self.MAX_INPUT for val in boundary_values])))

        for input_val in boundary_values:
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Boundary test FAIL: encoded=0x{input_val:x}, " +
                             f"expected=0x{expected_output:x}, actual=0x{actual_output:x}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                break

            # Verify one-hot property
            bits_set = bin(actual_output).count('1')
            if bits_set != 1:
                self.log.error(f"Boundary one-hot FAIL: encoded=0x{input_val:x}, " +
                             f"output=0x{actual_output:x}, bits_set={bits_set}")
                all_passed = False
                break

        return all_passed

    async def _dump_debug_info(self, input_val, expected_output, actual_output):
        """Dump debug information for failures"""
        self.log.error("="*80)
        self.log.error("DECODER FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input (encoded): 0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                      f"({input_val:0{self.INPUT_WIDTH}b}) = {input_val}")
        self.log.error(f"Expected output: 0x{expected_output:0{(self.OUTPUT_WIDTH+3)//4}x} " +
                      f"({expected_output:0{self.OUTPUT_WIDTH}b})")
        self.log.error(f"Actual output:   0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x} " +
                      f"({actual_output:0{self.OUTPUT_WIDTH}b})")

        # Show which bit should be set
        expected_bit_pos = input_val
        actual_bit_positions = [i for i in range(self.OUTPUT_WIDTH) if (actual_output >> i) & 1]

        self.log.error(f"Expected bit position: {expected_bit_pos}")
        self.log.error(f"Actual bit positions: {actual_bit_positions}")

        # Check if it's a simple shift error
        if len(actual_bit_positions) == 1:
            actual_pos = actual_bit_positions[0]
            shift_error = actual_pos - expected_bit_pos
            self.log.error(f"Bit position error: {shift_error} (actual - expected)")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running DECODER tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_decoding, "Basic decoding"),
            (self.test_one_hot_property, "One-hot property"),
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
        self.log.info(f"Overall DECODER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
