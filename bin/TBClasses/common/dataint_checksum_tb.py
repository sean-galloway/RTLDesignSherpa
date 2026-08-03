# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: ChecksumTB
# Purpose: Testbench for dataint_checksum
# Subsystem: framework
#
# Extracted from val/common/test_dataint_checksum.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.utils import get_sim_time
from TBClasses.shared.tbbase import TBBase


class ChecksumTB(TBBase):
    """
    Testbench for the Checksum module
    Features:
    - Verify checksum calculations with various data patterns
    - Test reset functionality
    - Test with different data widths
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))

        # Calculate maximum data value based on width
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.reset = self.dut.reset
        self.valid = self.dut.valid
        self.data = self.dut.data
        self.chksum = self.dut.chksum

        # Log configuration
        self.log.info("Checksum TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Test results storage
        self.test_results = []

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

    async def reset_dut(self, use_async_reset=True):
        """
        Reset the DUT

        Args:
            use_async_reset: Use asynchronous reset if True, synchronous if False
        """
        time_ns = get_sim_time('ns')
        self.log.debug(f'Starting reset_dut @ {time_ns}ns')

        # Initialize inputs
        self.valid.value = 0
        self.data.value = 0

        if use_async_reset:
            # Apply asynchronous reset
            self.rst_n.value = 0
            self.reset.value = 0
            await self.wait_clocks('clk', 5)
            self.rst_n.value = 1
        else:
            # Apply synchronous reset
            self.rst_n.value = 1
            self.reset.value = 1
            await self.wait_clocks('clk', 5)
            self.reset.value = 0

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        self.log.debug('Ending reset_dut')

    async def drive_data(self, data_values, expected_checksums=None):
        """
        Drive a series of data values and verify the checksum

        Args:
            data_values: List of data values to send
            expected_checksums: List of expected checksum values (optional)

        Returns:
            Dict with test results
        """
        # Calculate expected checksums if not provided
        if expected_checksums is None:
            expected_checksums = self._calculate_expected_checksums(data_values)

        test_result = {
            'data_values': data_values.copy(),
            'expected_checksums': expected_checksums.copy(),
            'actual_checksums': [],
            'all_match': True
        }

        # Reset for clean state
        await self.reset_dut()

        # Drive each data value
        for i, data in enumerate(data_values):
            # Mask data to the correct width
            masked_data = data & self.MAX_DATA

            # Drive the inputs
            self.valid.value = 1
            self.data.value = masked_data
            await self.wait_clocks('clk', 1)

            self.valid.value = 0
            self.data.value = 0
            await self.wait_clocks('clk', 1)

            # Check output on the next cycle
            actual_checksum = int(self.chksum.value)
            expected_checksum = expected_checksums[i]

            # Store results
            test_result['actual_checksums'].append(actual_checksum)

            # Check if checksum matches expected
            match = (actual_checksum == expected_checksum)
            if not match:
                test_result['all_match'] = False
                time_ns = get_sim_time('ns')
                self.log.error(f"Checksum mismatch at step {i+1}: " +
                                f"expected=0x{expected_checksum:x}, actual=0x{actual_checksum:x}"
                                f"@ {time_ns}ns")
            else:
                self.log.info(f"Checksum match at step {i+1}: 0x{actual_checksum:x}")

        # Deassert valid
        self.valid.value = 0

        # Wait a few cycles
        await self.wait_clocks('clk', 5)

        # Store test result
        self.test_results.append(test_result)

        return test_result

    def _calculate_expected_checksums(self, data_values):
        """
        Calculate expected checksums for a series of data values

        Args:
            data_values: List of data values

        Returns:
            List of expected checksum values
        """
        checksum = 0
        checksums = []

        for data in data_values:
            # Mask data to the correct width
            masked_data = data & self.MAX_DATA

            # Calculate new checksum
            checksum = (checksum + masked_data) & self.MAX_DATA

            # Store checksum
            checksums.append(checksum)

        return checksums

    async def test_basic_operation(self):
        """
        Test basic checksum operation with simple patterns

        Returns:
            True if all tests passed
        """
        self.log.info("Testing basic checksum operation")

        # Define test vectors
        test_vectors = [
            [0x01, 0x02, 0x03, 0x04],                      # Simple incrementing
            [0xFF, 0xFF, 0xFF, 0xFF],                      # All ones
            [0x00, 0x00, 0x00, 0x00],                      # All zeros
            [0xAA, 0x55, 0xAA, 0x55],                      # Alternating pattern
            [0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10]     # Longer sequence
        ]

        all_passed = True

        # Drive each test vector
        for i, vector in enumerate(test_vectors):
            time_ns = get_sim_time('ns')
            self.log.info(f"Testing vector {i+1}: {[hex(x) for x in vector]} @ {time_ns}ns")

            # Drive the vector
            result = await self.drive_data(vector)

            # Check if all checksums matched
            if not result['all_match']:
                self.log.error(f"Test vector {i+1} failed")
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

        return all_passed

    async def test_reset_functionality(self):
        """
        Test reset functionality

        Returns:
            True if all tests passed
        """
        self.log.info("Testing reset functionality")

        # First, drive some data to build up a checksum
        initial_data = [0x12, 0x34, 0x56, 0x78]

        result1 = await self.drive_data(initial_data)
        if not result1['all_match']:
            self.log.error("Initial data sequence failed")
            return False

        # Get the final checksum
        final_checksum = result1['actual_checksums'][-1]
        self.log.info(f"Final checksum before reset: 0x{final_checksum:x}")

        # Test asynchronous reset
        self.log.info("Testing asynchronous reset")
        self.rst_n.value = 0
        await self.wait_clocks('clk', 2)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 2)

        # Check if checksum was reset
        reset_checksum = int(self.chksum.value)
        if reset_checksum != 0:
            self.log.error(f"Asynchronous reset failed: checksum=0x{reset_checksum:x}, expected=0x0")
            return False

        self.log.info("Asynchronous reset successful")

        # Drive more data
        more_data = [0x9A, 0xBC, 0xDE, 0xF0]

        result2 = await self.drive_data(more_data)
        if not result2['all_match']:
            self.log.error("Second data sequence failed")
            return False

        # Test synchronous reset
        self.log.info("Testing synchronous reset")
        self.reset.value = 1
        await self.wait_clocks('clk', 1)
        self.reset.value = 0
        await self.wait_clocks('clk', 1)

        # Check if checksum was reset
        reset_checksum = int(self.chksum.value)
        if reset_checksum != 0:
            self.log.error(f"Synchronous reset failed: checksum=0x{reset_checksum:x}, expected=0x0")
            return False

        self.log.info("Synchronous reset successful")

        return True

    async def test_overflow_behavior(self):
        """
        Test checksum overflow behavior

        Returns:
            True if all tests passed
        """

        self.log.info("Testing overflow behavior")

        # Create a test vector that will cause overflow
        max_value = self.MAX_DATA
        half_max = max_value // 2

        test_vector = [max_value, 1]
        expected_checksums = [max_value, 0]  # Expect overflow back to 0

        result = await self.drive_data(test_vector, expected_checksums)
        time_ns = get_sim_time('ns')
        if not result['all_match']:
            self.log.error("Overflow test failed @ {time_ns}ns")
            return False

        self.log.info("Overflow test passed")

        # Test multiple overflows if not in gate mode
        if self.TEST_LEVEL != 'gate':
            self.log.info("Testing multiple overflows")

            # Create a test vector with multiple overflows
            test_vector = [max_value] * 5

            # Calculate expected checksums with overflow consideration
            expected = 0
            expected_checksums = []
            for _ in range(5):
                expected = (expected + max_value) & self.MAX_DATA
                expected_checksums.append(expected)

            result = await self.drive_data(test_vector, expected_checksums)

            if not result['all_match']:
                time_ns = get_sim_time('ns')
                self.log.error("Multiple overflow test failed @ {time_ns}ns")
                return False

            self.log.info("Multiple overflow test passed")

        return True

    async def test_random_data(self):
        """
        Test checksum calculation with random data

        Returns:
            True if all tests passed
        """
        self.log.info("Testing with random data")

        # Determine number of tests based on test level
        if self.TEST_LEVEL == 'gate':
            num_tests = 2
            max_length = 10
        elif self.TEST_LEVEL == 'func':
            num_tests = 5
            max_length = 20
        else:  # full
            num_tests = 10
            max_length = 50

        all_passed = True

        for test_num in range(num_tests):
            # Generate random data vector
            length = random.randint(5, max_length)
            data_vector = [random.randint(0, self.MAX_DATA) for _ in range(length)]

            self.log.info(f"Random test {test_num+1}: length={length}")

            # Drive the vector
            result = await self.drive_data(data_vector)

            # Check if all checksums matched
            if not result['all_match']:
                self.log.error(f"Random test {test_num+1} failed")
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}")

        all_passed = True

        # 1. Basic operation test
        self.log.info("1. Testing basic operation")
        basic_passed = await self.test_basic_operation()
        if not basic_passed:
            self.log.error("Basic operation test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 2. Reset functionality test
        self.log.info("2. Testing reset functionality")
        reset_passed = await self.test_reset_functionality()
        if not reset_passed:
            self.log.error("Reset functionality test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 3. Overflow behavior test
        self.log.info("3. Testing overflow behavior")
        overflow_passed = await self.test_overflow_behavior()
        if not overflow_passed:
            self.log.error("Overflow behavior test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # Skip random data test in gate mode
        if self.TEST_LEVEL != 'gate':
            # 4. Random data test
            self.log.info("4. Testing with random data")
            random_passed = await self.test_random_data()
            if not random_passed:
                self.log.error("Random data test failed")
                all_passed = False

        # Print summary
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(bool(r['all_match'])
                        for r in self.test_results)

        self.log.info("="*50)
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed")
        self.log.info("="*50)

        # Print detailed results based on test level
        if self.TEST_LEVEL != 'gate' and passed_tests < total_tests:
            self.log.info("Failed tests:")
            for i, result in enumerate(self.test_results):
                if not result['all_match']:
                    self.log.info(f"Test {i+1}:")
                    for j, (data, expected, actual) in enumerate(zip(
                            result['data_values'],
                            result['expected_checksums'],
                            result['actual_checksums'])):
                        if expected != actual:
                            self.log.info(f"  Step {j+1}: data=0x{data:x}, expected=0x{expected:x}, actual=0x{actual:x}")
