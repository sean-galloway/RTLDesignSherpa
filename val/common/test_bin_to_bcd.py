# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BinToBcdTB
# Purpose: Binary to BCD Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary to BCD Converter Test

This test verifies the binary to BCD (Binary Coded Decimal) conversion functionality:

CONFIGURATION:
    WIDTH: Bit width of binary input (8, 12, 16)
    DIGITS: Number of BCD digits output (3, 4, 5)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (5-10 min): Integration testing for CI/branches
    full (15-30 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - (WIDTH=8, DIGITS=3): 0-255 -> 000-255
    - (WIDTH=12, DIGITS=4): 0-4095 -> 0000-4095
    - (WIDTH=16, DIGITS=5): 0-65535 -> 00000-65535

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Binary input width
    TEST_DIGITS: BCD output digits

BCD CONVERSION BEHAVIOR:
    Uses double dabble algorithm with FSM
    Each BCD digit is 4 bits (0-9)
    Sequential operation: start -> shifting -> adding -> done
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
from conftest import get_coverage_compile_args

class BinToBcdTB(TBBase):
    """Testbench for Binary to BCD Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.DIGITS = self.convert_to_int(os.environ.get('TEST_DIGITS', '3'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

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

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.start = self.dut.start
        self.binary = self.dut.binary
        self.bcd = self.dut.bcd
        self.done = self.dut.done

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
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
        if self.TEST_LEVEL == 'basic':
            num_tests = min(20, self.max_binary + 1)
        elif self.TEST_LEVEL == 'medium':
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
                if self.TEST_LEVEL == 'basic' and failed_count >= 5:
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
        if self.TEST_LEVEL == 'basic':
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
        test_limit = min(max_test_val + 1, 200 if self.TEST_LEVEL == 'medium' else 500)

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

@cocotb.test(timeout_time=120000, timeout_unit="us")
async def bin_to_bcd_test(dut):
    """Test for Binary to BCD Converter module"""
    tb = BinToBcdTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"BIN_TO_BCD test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"BinToBcd test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Valid parameter combinations based on typical usage
    param_combinations = [
        (8, 3),   # 8-bit binary (0-255) -> 3 BCD digits (000-255)
        (12, 4),  # 12-bit binary (0-4095) -> 4 BCD digits (0000-4095)
        (16, 5),  # 16-bit binary (0-65535) -> 5 BCD digits (00000-65535)
    ]

    if reg_level == 'GATE':
        # GATE: Minimal - just 8-bit
        param_combinations = [(8, 3)]
        test_levels = ['full']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        param_combinations = [(8, 3), (12, 4)]
        test_levels = ['full']
    else:  # FULL
        # FULL: All widths
        test_levels = ['full']

    valid_params = []
    for (width, digits), test_level in product(param_combinations, test_levels):
        valid_params.append((width, digits, test_level))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, digits, test_level", params)
def test_bin_to_bcd(request, width, digits, test_level):
    """
    Parameterized Binary to BCD Converter test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "bin_to_bcd"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/bin_to_bcd.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)
    digits_str = TBBase.format_dec(digits, 1)
    test_name_plus_params = f"test_bin_to_bcd_w{width_str}_d{digits_str}_{test_level}_{reg_level}"

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
        'DIGITS': str(digits)
    }

    # Adjust timeout based on test level and complexity
    timeout_multipliers = {'basic': 1, 'medium': 5, 'full': 10}
    # BCD conversion is sequential and can take many cycles
    complexity_factor = (2 ** width) / 1000.0 if width <= 12 else width / 2.0
    base_timeout = 10000  # 10 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

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
        'TEST_DIGITS': str(digits),
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

    max_binary = (1 << width) - 1
    max_bcd = int('9' * digits)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}, digits={digits}")
    print(f"Binary range: 0 to {max_binary}")
    print(f"BCD range: 0 to {max_bcd}")
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
            includes=includes,  # From filelist via get_sources_from_filelist()
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}, digits={digits}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise