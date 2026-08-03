# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: EncoderPriorityEnableTB
# Purpose: Testbench for encoder_priority_enable
# Subsystem: framework
#
# Extracted from val/common/test_encoder_priority_enable.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import math
import cocotb
from TBClasses.shared.tbbase import TBBase


class EncoderPriorityEnableTB(TBBase):
    """Testbench for Priority Encoder with Enable module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.INPUT_WIDTH = self.convert_to_int(os.environ.get('TEST_INPUT_WIDTH', '8'))
        self.OUTPUT_WIDTH = int(math.log2(self.INPUT_WIDTH))
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

        # Validate input width (must be power of 2)
        if not (self.INPUT_WIDTH & (self.INPUT_WIDTH - 1)) == 0:
            self.log.warning(f"Input width {self.INPUT_WIDTH} is not a power of 2")

        # Log configuration
        self.log.info(f"Priority Encoder with Enable TB initialized")
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
        self.priority = self.dut.priority_in
        self.enable = self.dut.enable
        self.encode = self.dut.encode

    def _calculate_expected_output(self, input_val, enable):
        """Calculate expected priority encoder output"""
        input_val &= self.MAX_INPUT
        
        if not enable:
            return 0  # Disabled - output should be 0
        
        if input_val == 0:
            return 0  # No bits set
        
        # Find highest priority bit (highest bit position set)
        for i in range(self.INPUT_WIDTH - 1, -1, -1):
            if (input_val >> i) & 1:
                return i
        
        return 0

    def _generate_one_hot_values(self):
        """Generate one-hot test values"""
        one_hot_values = []
        for i in range(self.INPUT_WIDTH):
            one_hot_values.append(1 << i)
        return one_hot_values

    def _generate_multi_bit_values(self):
        """Generate values with multiple bits set"""
        multi_bit_values = []
        
        # Two adjacent bits
        for i in range(self.INPUT_WIDTH - 1):
            multi_bit_values.append((1 << i) | (1 << (i + 1)))
        
        # Two non-adjacent bits
        for i in range(0, self.INPUT_WIDTH - 2, 2):
            multi_bit_values.append((1 << i) | (1 << (i + 2)))
        
        # All bits in lower half
        lower_half = (1 << (self.INPUT_WIDTH // 2)) - 1
        if lower_half > 0:
            multi_bit_values.append(lower_half)
        
        # All bits in upper half
        upper_half = ((1 << (self.INPUT_WIDTH // 2)) - 1) << (self.INPUT_WIDTH // 2)
        if upper_half > 0:
            multi_bit_values.append(upper_half)
        
        return multi_bit_values

    async def test_enable_functionality(self):
        """Test enable/disable functionality"""
        self.log.info("=== Scenario ENC-01: Zero input ===")
        self.log.info("Testing enable/disable functionality")

        # Test with enable = 0 (disabled)
        test_values = [0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT]
        
        all_passed = True

        for input_val in test_values:
            # Test with enable = 0
            expected_output = 0  # Should always be 0 when disabled

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = 0
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"enable=0 → encode={actual_output}")
            else:
                self.log.error(f"FAIL: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"enable=0, expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, 0, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'enable_disabled',
                'input': input_val,
                'enable': 0,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_one_hot_encoding(self):
        """Test encoder with one-hot inputs (enabled)"""
        self.log.info("=== Scenario ENC-02: One-hot encoding ===")
        self.log.info("Testing one-hot encoding (enabled)")

        one_hot_values = self._generate_one_hot_values()
        
        all_passed = True

        for input_val in one_hot_values:
            expected_output = self._calculate_expected_output(input_val, True)

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = 1
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"enable=1 → encode={actual_output} (bit {actual_output})")
            else:
                self.log.error(f"FAIL: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"enable=1, expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, 1, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'one_hot_encoding',
                'input': input_val,
                'enable': 1,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_priority_encoding(self):
        """Test encoder with multiple bits set (priority encoding)"""
        self.log.info("=== Scenario ENC-03: Priority encoding ===")
        self.log.info("Testing priority encoding")

        # Define test data based on level
        if self.TEST_LEVEL == 'gate':
            test_values = self._generate_multi_bit_values()[:8]  # Limited set
        elif self.TEST_LEVEL == 'func':
            test_values = self._generate_multi_bit_values()
            # Add some random multi-bit values
            for _ in range(16):
                val = random.randint(1, self.MAX_INPUT)
                # Ensure at least 2 bits are set
                if bin(val).count('1') >= 2:
                    test_values.append(val)
        else:  # full
            test_values = self._generate_multi_bit_values()
            # Add comprehensive random multi-bit values
            for _ in range(64):
                val = random.randint(1, self.MAX_INPUT)
                if bin(val).count('1') >= 2:
                    test_values.append(val)
            # Add systematic patterns
            test_values.append(self.MAX_INPUT)  # All bits set
            test_values.append(self.MAX_INPUT >> 1)  # All but MSB

        # Remove duplicates
        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values if val > 0])))

        all_passed = True

        for input_val in test_values:
            expected_output = self._calculate_expected_output(input_val, True)

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = 1
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                bit_count = bin(input_val).count('1')
                self.log.debug(f"PASS: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                             f"({bit_count} bits), enable=1 → encode={actual_output} (highest bit)")
            else:
                self.log.error(f"FAIL: priority=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"enable=1, expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, 1, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'priority_encoding',
                'input': input_val,
                'enable': 1,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_zero_input(self):
        """Test encoder with zero input"""
        self.log.info("Testing zero input")

        all_passed = True

        for enable_val in [0, 1]:
            input_val = 0
            expected_output = 0  # Should output 0 when no bits are set or disabled

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = enable_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: priority=0x{input_val:x}, enable={enable_val} → encode={actual_output}")
            else:
                self.log.error(f"FAIL: priority=0x{input_val:x}, enable={enable_val}, " +
                             f"expected={expected_output}, actual={actual_output}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'zero_input',
                'input': input_val,
                'enable': enable_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_enable_transitions(self):
        """Test enable signal transitions"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping enable transition tests for gate level")
            return True

        self.log.info("Testing enable signal transitions")

        all_passed = True

        # Test with a fixed input value
        test_input = (1 << (self.INPUT_WIDTH - 1)) | 1  # MSB and LSB set

        # Test enable 0 -> 1 transition
        self.priority.value = test_input
        self.enable.value = 0
        await cocotb.triggers.Timer(1, units='ns')
        
        disabled_output = int(self.encode.value) & self.MAX_OUTPUT
        if disabled_output != 0:
            self.log.error(f"Enable=0 failed: expected 0, got {disabled_output}")
            all_passed = False

        # Enable the encoder
        self.enable.value = 1
        await cocotb.triggers.Timer(1, units='ns')
        
        enabled_output = int(self.encode.value) & self.MAX_OUTPUT
        expected_enabled = self._calculate_expected_output(test_input, True)
        
        if enabled_output != expected_enabled:
            self.log.error(f"Enable=1 failed: expected {expected_enabled}, got {enabled_output}")
            all_passed = False

        # Test enable 1 -> 0 transition
        self.enable.value = 0
        await cocotb.triggers.Timer(1, units='ns')
        
        redisabled_output = int(self.encode.value) & self.MAX_OUTPUT
        if redisabled_output != 0:
            self.log.error(f"Re-disable failed: expected 0, got {redisabled_output}")
            all_passed = False

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping boundary condition tests for gate level")
            return True

        self.log.info("=== Scenario ENC-04: Boundary conditions ===")
        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test boundary values
        boundary_values = [
            1,  # Only LSB
            1 << (self.INPUT_WIDTH - 1),  # Only MSB
            self.MAX_INPUT,  # All bits set
            self.MAX_INPUT >> 1,  # All but MSB
            (1 << (self.INPUT_WIDTH - 1)) | 1,  # MSB and LSB
        ]

        for enable_val in [0, 1]:
            for input_val in boundary_values:
                if input_val == 0:
                    continue  # Already tested in zero_input
                    
                expected_output = self._calculate_expected_output(input_val, enable_val)

                # Drive inputs
                self.priority.value = input_val
                self.enable.value = enable_val
                await cocotb.triggers.Timer(1, units='ns')

                actual_output = int(self.encode.value) & self.MAX_OUTPUT

                success = (actual_output == expected_output)

                if not success:
                    self.log.error(f"Boundary test FAIL: priority=0x{input_val:x}, " +
                                 f"enable={enable_val}, expected={expected_output}, actual={actual_output}")
                    await self._dump_debug_info(input_val, enable_val, expected_output, actual_output)
                    all_passed = False
                    break
            
            if not all_passed:
                break

        return all_passed

    async def test_walking_patterns(self):
        """Test walking bit patterns"""
        if self.TEST_LEVEL != 'full':
            self.log.info("Skipping walking patterns test")
            return True

        self.log.info("=== Scenario ENC-05: Walking patterns ===")
        self.log.info("Testing walking bit patterns")

        all_passed = True

        # Walking ones pattern (enabled)
        for i in range(self.INPUT_WIDTH):
            input_val = 1 << i
            expected_output = i

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = 1
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Walking ones FAIL: bit {i}, priority=0x{input_val:x}, " +
                             f"expected={expected_output}, actual={actual_output}")
                all_passed = False
                break

        # Walking zeros pattern (all bits set except one) - enabled
        if all_passed:
            for i in range(self.INPUT_WIDTH):
                input_val = self.MAX_INPUT ^ (1 << i)  # All bits except bit i
                
                # Find the actual highest bit
                expected_output = self.INPUT_WIDTH - 1  # Start with highest possible
                for j in range(self.INPUT_WIDTH - 1, -1, -1):
                    if (input_val >> j) & 1:
                        expected_output = j
                        break

                # Drive inputs
                self.priority.value = input_val
                self.enable.value = 1
                await cocotb.triggers.Timer(1, units='ns')

                actual_output = int(self.encode.value) & self.MAX_OUTPUT

                success = (actual_output == expected_output)

                if not success:
                    self.log.error(f"Walking zeros FAIL: cleared bit {i}, priority=0x{input_val:x}, " +
                                 f"expected={expected_output}, actual={actual_output}")
                    all_passed = False
                    break

        return all_passed

    async def test_random_patterns(self):
        """Test random input patterns"""
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping random patterns test for gate level")
            return True

        self.log.info("Testing random patterns")

        all_passed = True

        # Number of random tests based on level
        num_tests = 32 if self.TEST_LEVEL == 'func' else 128

        for _ in range(num_tests):
            input_val = random.randint(0, self.MAX_INPUT)
            enable_val = random.choice([0, 1])
            
            expected_output = self._calculate_expected_output(input_val, enable_val)

            # Drive inputs
            self.priority.value = input_val
            self.enable.value = enable_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.encode.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Random test FAIL: priority=0x{input_val:x}, " +
                             f"enable={enable_val}, expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, enable_val, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    break

            # Store result
            result = {
                'test_type': 'random_patterns',
                'input': input_val,
                'enable': enable_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def _dump_debug_info(self, input_val, enable_val, expected_output, actual_output):
        """Dump debug information for failures"""
        self.log.error("="*80)
        self.log.error("PRIORITY ENCODER WITH ENABLE FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input (priority): 0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                      f"({input_val:0{self.INPUT_WIDTH}b})")
        self.log.error(f"Enable: {enable_val}")
        self.log.error(f"Expected output: {expected_output}")
        self.log.error(f"Actual output:   {actual_output}")

        if enable_val == 0:
            self.log.error("Enable is 0 - output should always be 0")
        else:
            # Show bit analysis
            bits_set = []
            for i in range(self.INPUT_WIDTH):
                if (input_val >> i) & 1:
                    bits_set.append(i)

            self.log.error(f"Input bits set: {bits_set}")
            self.log.error(f"Highest bit: {max(bits_set) if bits_set else 'none'}")
            self.log.error(f"Input bit count: {len(bits_set)}")

            if bits_set:
                expected_highest = max(bits_set)
                self.log.error(f"Expected highest bit position: {expected_highest}")
                if actual_output != expected_highest:
                    self.log.error(f"Priority error: got bit {actual_output}, should be bit {expected_highest}")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running PRIORITY ENCODER WITH ENABLE tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_zero_input, "Zero input"),
            (self.test_enable_functionality, "Enable functionality"),
            (self.test_one_hot_encoding, "One-hot encoding"),
            (self.test_priority_encoding, "Priority encoding"),
            (self.test_enable_transitions, "Enable transitions"),
            (self.test_boundary_conditions, "Boundary conditions"),
            (self.test_walking_patterns, "Walking patterns"),
            (self.test_random_patterns, "Random patterns")
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
        self.log.info(f"Overall PRIORITY ENCODER WITH ENABLE result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
