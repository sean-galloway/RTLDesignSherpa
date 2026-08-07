# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: BinToBcdTB
# Purpose: Testbench for bin_to_bcd
# Subsystem: framework
#
# Extracted from val/common/test_bin_to_bcd.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from TBClasses.shared.tbbase import TBBase


class BinToBcdTB(TBBase):
    """Testbench for Binary to BCD Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.DIGITS = self.convert_to_int(os.environ.get('TEST_DIGITS', '3'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"BinToBcd TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, DIGITS={self.DIGITS}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_binary = (1 << self.WIDTH) - 1
        self.max_bcd_value = int('9' * self.DIGITS)

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

        self.log.info(f"Binary range: 0 to {self.max_binary}")
        self.log.info(f"BCD range: 0 to {self.max_bcd_value}")

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
        # Mark it, so a later setup_clock() from a sub-test does not stack a
        # second driver on top of the one TBBase just started.
        self._clock_started = True
        await self.reset_dut()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.start = self.dut.start
        self.binary = self.dut.binary
        self.bcd = self.dut.bcd
        self.done = self.dut.done

    async def setup_clock(self):
        """Start the clock once, however many sub-tests ask for it.

        This used to start a new Clock coroutine on every call, and four
        sub-tests call it -- so dut.clk had two independent drivers at GATE and
        up to four at FULL, each scheduling its own edges on the same signal.
        The contract path (setup_clocks_and_reset -> TBBase.start_clock) is
        guarded, but bin_to_bcd_test calls run_all_tests() directly, so the
        guarded path never ran and this was the only clock source.
        """
        if not getattr(self, '_clock_started', False):
            cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
            self._clock_started = True
        # The settle always happens, started here or not: callers use this as
        # "clock running, one delta done". Returning early instead skipped it
        # and failed every bin_to_bcd config.
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.start.value = 0
        self.binary.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def binary_to_bcd_reference(self, binary_val):
        """Reference implementation: convert binary to BCD"""
        # All values within the binary range that fit in BCD digits are valid
        if binary_val > self.max_bcd_value:
            return None  # Invalid conversion
        
        # Convert to decimal string, then to BCD
        decimal_str = str(binary_val).zfill(self.DIGITS)
        bcd_val = 0
        
        for i, digit_char in enumerate(reversed(decimal_str)):
            digit = int(digit_char)
            bcd_val |= (digit << (i * 4))
        
        return bcd_val

    def bcd_to_decimal(self, bcd_val):
        """Convert BCD value back to decimal for verification"""
        decimal_val = 0
        for i in range(self.DIGITS):
            digit = (bcd_val >> (i * 4)) & 0xF
            if digit > 9:
                return None  # Invalid BCD
            decimal_val += digit * (10 ** i)
        return decimal_val

    def format_bcd(self, bcd_val):
        """Format BCD value for display"""
        digits = []
        for i in range(self.DIGITS):
            digit = (bcd_val >> (i * 4)) & 0xF
            digits.append(str(digit))
        return ''.join(reversed(digits))

    async def convert_binary_to_bcd(self, binary_val, timeout_cycles=None):
        """Perform a single binary to BCD conversion"""
        # Calculate expected cycles for double-dabble algorithm:
        # - WIDTH iterations (shift operations)
        # - Each iteration: 1 shift + DIGITS add operations + state overhead
        # - Conservative estimate with margin
        expected_cycles = self.WIDTH * (1 + self.DIGITS + 2) + 10  # ~60 for WIDTH=8, DIGITS=3
        
        if timeout_cycles is None:
            timeout_cycles = expected_cycles * 2  # 2x margin for safety
            
        self.log.debug(f"Converting binary {binary_val}, expected ~{expected_cycles} cycles, timeout={timeout_cycles}")

        # Set inputs
        self.binary.value = binary_val
        self.start.value = 1
        
        await RisingEdge(self.clk)
        self.start.value = 0

        # Wait for conversion to complete
        cycle_count = 0
        while self.done.value == 0:
            await RisingEdge(self.clk)
            cycle_count += 1

            if cycle_count >= timeout_cycles:
                break

        if cycle_count >= timeout_cycles:
            return False, None, None, cycle_count  # Timeout

        # Read result
        actual_bcd = int(self.bcd.value)
        expected_bcd = self.binary_to_bcd_reference(binary_val)

        # Verify conversion
        success = (expected_bcd is not None) and (actual_bcd == expected_bcd)

        return success, actual_bcd, expected_bcd, cycle_count

    async def check_conversion(self, binary_val):
        """Check a single conversion with detailed logging"""
        success, actual_bcd, expected_bcd, cycles = await self.convert_binary_to_bcd(binary_val)

        if not success or self.DEBUG:
            expected_str = self.format_bcd(expected_bcd) if expected_bcd is not None else "INVALID"
            actual_str = self.format_bcd(actual_bcd) if actual_bcd is not None else "TIMEOUT"

            self.log.info(f"Binary: {binary_val:>5d} (0x{binary_val:0{(self.WIDTH+3)//4}X}) "
                            f"-> BCD: {actual_str} "
                            f"(Expected: {expected_str}) "
                            f"Cycles: {cycles} "
                            f"{'✓' if success else '✗'}")

        return success, actual_bcd, expected_bcd, cycles

    async def test_corner_cases(self):
        """Test corner cases"""
        self.log.info(f"Testing corner cases")

        await self.setup_clock()
        await self.reset_dut()

        corner_cases = [0, 1, self.max_binary]

        # Add some powers of 10 if they fit
        power_of_10 = 1
        while power_of_10 <= self.max_binary and power_of_10 <= self.max_bcd_value:
            corner_cases.append(power_of_10)
            power_of_10 *= 10

        # Add some specific values
        if self.WIDTH >= 8:
            corner_cases.extend([99, 100, 255])
        if self.WIDTH >= 12:
            corner_cases.extend([999, 1000, 4095])
        if self.WIDTH >= 16:
            corner_cases.extend([9999, 10000, 65535])

        # Remove duplicates and values out of range
        corner_cases = list(set([val for val in corner_cases if val <= self.max_binary]))

        all_passed = True
        failed_count = 0

        for binary_val in corner_cases:
            success, actual, expected, cycles = await self.check_conversion(binary_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'corner_cases',
                    'binary_input': binary_val,
                    'expected_bcd': expected,
                    'actual_bcd': actual,
                    'cycles_taken': cycles,
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
        """Test random values"""
        self.log.info(f"Testing random values")

        await self.setup_clock()
        await self.reset_dut()

        # Determine number of tests based on level and range
        if self.TEST_LEVEL == 'gate':
            num_tests = min(20, self.max_binary + 1)
        elif self.TEST_LEVEL == 'func':
            num_tests = min(100, self.max_binary + 1)
        else:  # full
            num_tests = min(500, self.max_binary + 1)

        all_passed = True
        failed_count = 0
        total_cycles = 0

        # Generate random test values within BCD range
        test_values = []
        max_test_val = min(self.max_binary, self.max_bcd_value)

        for _ in range(num_tests):
            val = random.randint(0, max_test_val)
            test_values.append(val)

        for i, binary_val in enumerate(test_values):
            success, actual, expected, cycles = await self.check_conversion(binary_val)
            total_cycles += cycles

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random_values',
                    'test_index': i,
                    'binary_input': binary_val,
                    'expected_bcd': expected,
                    'actual_bcd': actual,
                    'cycles_taken': cycles,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'gate' and failed_count >= 5:
                    break

        # Store summary result
        avg_cycles = total_cycles / len(test_values) if test_values else 0
        result = {
            'test_type': 'random_values',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'average_cycles': avg_cycles,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Random values test: {result['total_tests']} tests, "
                        f"{failed_count} failures, avg cycles: {avg_cycles:.1f}")

        return all_passed

    async def test_sequential_values(self):
        """Test sequential values (useful for small ranges)"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping sequential values test")
            return True

        # Only test sequential for small ranges
        max_test_val = min(self.max_binary, self.max_bcd_value)
        if max_test_val > 1000:
            self.log.info(f"Skipping sequential test for large range ({max_test_val})")
            return True

        self.log.info(f"Testing sequential values 0 to {max_test_val}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        failed_count = 0
        total_cycles = 0

        # Test every value in range (for small ranges only)
        test_limit = min(max_test_val + 1, 200 if self.TEST_LEVEL == 'func' else 500)

        for binary_val in range(test_limit):
            success, actual, expected, cycles = await self.check_conversion(binary_val)
            total_cycles += cycles

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'sequential_values',
                    'binary_input': binary_val,
                    'expected_bcd': expected,
                    'actual_bcd': actual,
                    'cycles_taken': cycles,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early if too many failures
                if failed_count >= 10:
                    break

        # Store summary result
        avg_cycles = total_cycles / test_limit if test_limit > 0 else 0
        result = {
            'test_type': 'sequential_values',
            'total_tests': min(test_limit, binary_val + 1),
            'failures': failed_count,
            'average_cycles': avg_cycles,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Sequential values test: {result['total_tests']} tests, "
                        f"{failed_count} failures, avg cycles: {avg_cycles:.1f}")

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior during conversion"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping reset behavior test")
            return True

        self.log.info(f"Testing reset behavior")
        
        await self.setup_clock()
        await self.reset_dut()
        
        all_passed = True
        failed_count = 0
        
        # Test reset during conversion - use values within range
        max_test_val = min(self.max_binary, self.max_bcd_value)
        test_values = [
            min(123, max_test_val), 
            min(200, max_test_val), 
            min(50, max_test_val)
        ]
        
        for binary_val in test_values:
            # Start conversion
            self.binary.value = binary_val
            self.start.value = 1
            await RisingEdge(self.clk)
            self.start.value = 0
            
            # Wait a few cycles, then reset
            for _ in range(3):
                await RisingEdge(self.clk)
            
            # Apply reset
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            self.rst_n.value = 1
            await RisingEdge(self.clk)
            
            # Check that done is not asserted after reset
            if self.done.value == 1:
                failed_count += 1
                all_passed = False
                self.log.error(f"Done signal asserted after reset for binary={binary_val}")
            
            # Now do a proper conversion
            success, actual, expected, cycles = await self.check_conversion(binary_val)
            
            if not success:
                failed_count += 1
                all_passed = False

        # Store summary result
        result = {
            'test_type': 'reset_behavior',
            'total_tests': len(test_values) * 2,  # Reset test + conversion test
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Reset behavior test: {result['total_tests']} tests, {failed_count} failures")
        
        return all_passed

    async def test_invalid_bcd_range(self):
        """Test values that exceed BCD range"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping invalid BCD range test")
            return True

        # Only test if binary range exceeds BCD range
        if self.max_binary <= self.max_bcd_value:
            self.log.info(f"Skipping invalid BCD range test (all values valid)")
            return True

        self.log.info(f"Testing values that exceed BCD range")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        failed_count = 0

        # Test values beyond BCD range
        invalid_values = []

        # Start just above max BCD value
        start_val = self.max_bcd_value + 1
        end_val = min(self.max_binary, start_val + 50)  # Test up to 50 invalid values

        for val in range(start_val, end_val + 1):
            invalid_values.append(val)

        for binary_val in invalid_values:
            # For values beyond BCD range, behavior depends on implementation
            # We mainly check that the module doesn't hang or crash
            success, actual_bcd, expected_bcd, cycles = await self.convert_binary_to_bcd(binary_val)

            # For invalid range, we mainly care that it doesn't timeout
            if cycles >= 100:  # Timeout occurred
                failed_count += 1
                all_passed = False

                self.log.error(f"Timeout for invalid binary value: {binary_val}")

                # Store failure
                result = {
                    'test_type': 'invalid_bcd_range',
                    'binary_input': binary_val,
                    'timeout': True,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'invalid_bcd_range',
            'total_tests': len(invalid_values),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Invalid BCD range test: {len(invalid_values)} tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running BIN_TO_BCD tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_sequential_values, "Sequential values"),
            (self.test_random_values, "Random values"),
            (self.test_corner_cases, "Corner cases"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_invalid_bcd_range, "Invalid BCD range")
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
        self.log.info(f"Overall BIN_TO_BCD result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
