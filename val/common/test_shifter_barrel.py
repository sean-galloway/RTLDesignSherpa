# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ShifterBarrelConfig
# Purpose: Configuration class for Barrel Shifter tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run


# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class ShifterBarrelConfig:
    """Configuration class for Barrel Shifter tests"""
    def __init__(self, name, test_vectors, width=8):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            test_vectors: List of test vectors (dict with data, ctrl, shift, expected)
            width: Data width
        """
        self.name = name
        self.test_vectors = test_vectors
        self.width = width


class ShifterBarrelTB(TBBase):
    """
    Testbench for the Barrel Shifter module
    Features:
    - Verify all shift modes (no shift, logical right, arithmetic right, wrap right, logical left, wrap left)
    - Test various shift amounts
    - Test with different data widths
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))

        # Calculate maximum data value based on width
        self.MAX_DATA = (1 << self.WIDTH) - 1
        self.SHIFT_BITS = (self.WIDTH).bit_length()  # Number of bits needed to represent shift amount

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.data = self.dut.data
        self.ctrl = self.dut.ctrl
        self.shift_amount = self.dut.shift_amount
        self.data_out = self.dut.data_out

        # Control signal definitions for clarity
        self.CTRL_NO_SHIFT = 0
        self.CTRL_RIGHT_SHIFT = 1
        self.CTRL_ARITH_RIGHT_SHIFT = 2
        self.CTRL_RIGHT_SHIFT_WRAP = 3
        self.CTRL_LEFT_SHIFT = 4
        self.CTRL_LEFT_SHIFT_WRAP = 6

        # Log configuration
        self.log.info("Barrel Shifter TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Test results storage
        self.test_results = []

    async def drive_and_check(self, data, ctrl, shift_amount, expected=None):
        """
        Drive the inputs and check the outputs

        Args:
            data: Input data
            ctrl: Control signal
            shift_amount: Shift amount
            expected: Expected output (None for auto calculation)

        Returns:
            True if output matched expected value
        """
        # Mask to correct bit widths
        data &= self.MAX_DATA
        ctrl &= 0x7
        shift_amount &= ((1 << self.SHIFT_BITS) - 1)

        time_ns = get_sim_time('ns')
        self.log.info(f"Testing @ {time_ns}ns: data=0x{data:x}, ctrl={ctrl}, shift_amount={shift_amount}")

        # Drive the inputs
        self.data.value = data
        self.ctrl.value = ctrl
        self.shift_amount.value = shift_amount

        # Wait a small time for combinational logic to settle
        await Timer(1, units='ns')

        # Read output
        actual_output = int(self.data_out.value)

        # Calculate expected output if not provided
        if expected is None:
            expected = self._calculate_expected_output(data, ctrl, shift_amount)

        # Check result
        match = (actual_output == expected)

        # Log result
        if match:
            self.log.info(f"PASS: output=0x{actual_output:x}")
        else:
            self.log.error(f"FAIL: data=0x{data:x}, ctrl={ctrl}, shift_amount={shift_amount}")
            self.log.error(f"  Expected=0x{expected:x}, Actual=0x{actual_output:x}")

        # Store result for reporting
        self.test_results.append({
            'data': data,
            'ctrl': ctrl,
            'shift_amount': shift_amount,
            'expected': expected,
            'actual': actual_output,
            'match': match
        })

        return match

    def _calculate_expected_output(self, data, ctrl, shift_amount):
        """
        Calculate the expected output based on the inputs

        Args:
            data: Input data
            ctrl: Control signal
            shift_amount: Shift amount

        Returns:
            Expected output
        """
        # Ensure inputs are masked to appropriate width
        data &= self.MAX_DATA
        shift_amount_mod = shift_amount % self.WIDTH

        # Calculate expected output based on control signal
        if ctrl == self.CTRL_NO_SHIFT:
            # No shift
            return data
        elif ctrl == self.CTRL_RIGHT_SHIFT:
            # Logical right shift (no wrap)
            return data if shift_amount_mod == 0 else data >> shift_amount
        elif ctrl == self.CTRL_ARITH_RIGHT_SHIFT:
            # Arithmetic right shift
            # Check if MSB is set (negative number)
            msb_set = (data >> (self.WIDTH - 1)) & 1
            if not msb_set:
                # For positive numbers, same as logical shift
                return (data >> shift_amount_mod) & self.MAX_DATA
            # Arithmetic shift for negative number
            mask = ((1 << shift_amount_mod) - 1) << (self.WIDTH - shift_amount_mod)
            return ((data >> shift_amount_mod) | mask) & self.MAX_DATA
        elif ctrl == self.CTRL_RIGHT_SHIFT_WRAP:
            # Logical right shift with wrap
            if shift_amount_mod == 0:
                return data
            # Calculate wrapped bits
            wrapped = (data & ((1 << shift_amount_mod) - 1)) << (self.WIDTH - shift_amount_mod)
            # Calculate shifted bits
            shifted = data >> shift_amount_mod
            # Combine
            return (wrapped | shifted) & self.MAX_DATA
        elif ctrl == self.CTRL_LEFT_SHIFT:
            # Logical left shift (no wrap)
            return (
                data
                if shift_amount_mod == 0
                else (data << shift_amount) & self.MAX_DATA
            )
        elif ctrl == self.CTRL_LEFT_SHIFT_WRAP:
            # Logical left shift with wrap
            if shift_amount_mod == 0:
                return data
            # Calculate wrapped bits
            wrapped = (data >> (self.WIDTH - shift_amount_mod))
            # Calculate shifted bits
            shifted = (data << shift_amount_mod) & self.MAX_DATA
            # Combine
            return (wrapped | shifted) & self.MAX_DATA
        else:
            # Default is no shift
            return data

    async def test_no_shift(self):
        """
        Test no shift operation (ctrl=0)

        Returns:
            True if all tests passed
        """
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing no shift operation (ctrl=0) @ {time_ns}ns")

        # Test cases for no shift
        test_cases = [
            0x00,
            0x01,
            0xFF & self.MAX_DATA,
            0xA5 & self.MAX_DATA,
            0x5A & self.MAX_DATA
        ]

        all_passed = True

        for data in test_cases:
            # Test with different shift amounts, but they should be ignored
            for shift in [0, 1, self.WIDTH // 2, self.WIDTH - 1]:
                test_passed = await self.drive_and_check(data, self.CTRL_NO_SHIFT, shift, data)

                if not test_passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        return False

        return all_passed

    async def test_logical_right_shift(self):
        """
        Test logical right shift (ctrl=1)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing logical right shift (ctrl=1)")

        # Test cases for logical right shift
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 2),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_RIGHT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    return False

        return all_passed

    async def test_arithmetic_right_shift(self):
        """
        Test arithmetic right shift (ctrl=2)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing arithmetic right shift (ctrl=2)")

        # Test cases for arithmetic right shift
        test_cases = [
            # (data, shift_amount)
            (0x7F & self.MAX_DATA, 1),    # Positive number (MSB=0)
            ((0x80 | 0x3F) & self.MAX_DATA, 1),    # Negative number (MSB=1)
            (0x7F & self.MAX_DATA, 4),    # Larger shift for positive
            ((0x80 | 0x3F) & self.MAX_DATA, 4)     # Larger shift for negative
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_ARITH_RIGHT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    return False

        return all_passed

    async def test_right_shift_wrap(self):
        """
        Test right shift with wrap (ctrl=3)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing right shift with wrap (ctrl=3)")

        # Test cases for right shift with wrap
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 4),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_RIGHT_SHIFT_WRAP, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    return False

        return all_passed

    async def test_left_shift(self):
        """
        Test left shift (ctrl=4)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing left shift (ctrl=4)")

        # Test cases for left shift
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 2),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_LEFT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    return False

        return all_passed

    async def test_left_shift_wrap(self):
        """
        Test left shift with wrap (ctrl=6)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing left shift with wrap (ctrl=6)")

        # Test cases for left shift with wrap
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 4),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_LEFT_SHIFT_WRAP, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    return False

        return all_passed

    async def test_shift_amounts(self):
        """
        Test various shift amounts including 0, width, and full range

        Returns:
            True if all tests passed
        """
        self.log.info("Testing various shift amounts")

        # Test single data pattern with different shift amounts
        data = 0xA5 & self.MAX_DATA

        # Test shift amounts
        shift_amounts = [0]  # No shift

        # Include more shift amounts based on test level
        if self.TEST_LEVEL == 'basic':
            shift_amounts.extend([1, self.WIDTH // 2, self.WIDTH - 1])
        elif self.TEST_LEVEL == 'medium':
            shift_amounts.extend(list(range(1, min(self.WIDTH, 16))))
        else:  # full
            shift_amounts.extend(list(range(1, self.WIDTH + 8)))  # Include beyond width

        all_passed = True

        for ctrl in [self.CTRL_RIGHT_SHIFT, self.CTRL_ARITH_RIGHT_SHIFT,
                        self.CTRL_RIGHT_SHIFT_WRAP, self.CTRL_LEFT_SHIFT,
                        self.CTRL_LEFT_SHIFT_WRAP]:
            for shift in shift_amounts:
                test_passed = await self.drive_and_check(data, ctrl, shift)

                if not test_passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        return False

        return all_passed

    async def test_random_patterns(self):
        """
        Test random data patterns

        Returns:
            True if all tests passed
        """
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping random pattern tests in basic mode")
            return True

        self.log.info("Testing random data patterns")

        # Determine number of tests based on test level
        num_tests = 10 if self.TEST_LEVEL == 'medium' else 50

        all_passed = True

        for _ in range(num_tests):
            data = random.randint(0, self.MAX_DATA)
            ctrl = random.choice([self.CTRL_NO_SHIFT, self.CTRL_RIGHT_SHIFT,
                                    self.CTRL_ARITH_RIGHT_SHIFT, self.CTRL_RIGHT_SHIFT_WRAP,
                                    self.CTRL_LEFT_SHIFT, self.CTRL_LEFT_SHIFT_WRAP])
            shift = random.randint(0, self.WIDTH + 4)  # Include beyond width

            test_passed = await self.drive_and_check(data, ctrl, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    return False

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        time_ns = get_sim_time('ns')
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL} @ {time_ns}ns")

        all_passed = True

        # 1. No shift test
        self.log.info("1. Testing no shift operation")
        no_shift_passed = await self.test_no_shift()
        if not no_shift_passed:
            self.log.error("No shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 2. Logical right shift test
        self.log.info("2. Testing logical right shift")
        right_shift_passed = await self.test_logical_right_shift()
        if not right_shift_passed:
            self.log.error("Logical right shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 3. Arithmetic right shift test
        self.log.info("3. Testing arithmetic right shift")
        arith_shift_passed = await self.test_arithmetic_right_shift()
        if not arith_shift_passed:
            self.log.error("Arithmetic right shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 4. Right shift with wrap test
        self.log.info("4. Testing right shift with wrap")
        right_wrap_passed = await self.test_right_shift_wrap()
        if not right_wrap_passed:
            self.log.error("Right shift wrap test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 5. Left shift test
        self.log.info("5. Testing left shift")
        left_shift_passed = await self.test_left_shift()
        if not left_shift_passed:
            self.log.error("Left shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 6. Left shift with wrap test
        self.log.info("6. Testing left shift with wrap")
        left_wrap_passed = await self.test_left_shift_wrap()
        if not left_wrap_passed:
            self.log.error("Left shift wrap test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 7. Shift amount test
        self.log.info("7. Testing various shift amounts")
        shift_amount_passed = await self.test_shift_amounts()
        if not shift_amount_passed:
            self.log.error("Shift amount test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 8. Random pattern test (medium and full only)
        if self.TEST_LEVEL != 'basic':
            self.log.info("8. Testing random patterns")
            random_passed = await self.test_random_patterns()
            if not random_passed:
                self.log.error("Random pattern test failed")
                all_passed = False

        # Print summary
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(bool(r['match'])
                        for r in self.test_results)

        self.log.info("="*50)
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed")
        self.log.info("="*50)

        # Print detailed results based on test level
        if self.TEST_LEVEL != 'basic' and passed_tests < total_tests:
            self.log.info("Failed tests:")
            for i, result in enumerate(self.test_results):
                if not result['match']:
                    self.log.info(f"Test {i+1}:")
                    self.log.info(f"  Inputs: data=0x{result['data']:x}, ctrl={result['ctrl']}, shift={result['shift_amount']}")
                    self.log.info(f"  Expected=0x{result['expected']:x}, Actual=0x{result['actual']:x}")


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = ShifterBarrelTB(dut)

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8-bit, basic+medium)
    REG_LEVEL=FUNC: 3 tests (8-bit all levels) - default
    REG_LEVEL=FULL: 6 tests (8-bit all levels + 4, 16, 32-bit)

    Returns:
        List of dicts with WIDTH, test_level
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},
            {'WIDTH': 8, 'test_level': 'medium'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},
            {'WIDTH': 8, 'test_level': 'medium'},
            {'WIDTH': 8, 'test_level': 'full'},
        ]
    else:  # FULL
        return [
            {'WIDTH': 8, 'test_level': 'basic'},
            {'WIDTH': 8, 'test_level': 'medium'},
            {'WIDTH': 8, 'test_level': 'full'},
            {'WIDTH':  4, 'test_level': 'medium'},
            {'WIDTH': 16, 'test_level': 'medium'},
            {'WIDTH': 32, 'test_level': 'medium'},
        ]


@pytest.mark.parametrize("params", generate_test_params())
def test_shifter_barrel(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "shifter_barrel"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_barrel.f'
    )

    # Create a human-readable test identifier
    t_width = params['WIDTH']
    t_name = params['test_level']
    test_name_plus_params = f"test_{dut_name}_W{t_width}_{t_name}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    parameters = {
        'WIDTH': params['WIDTH']
    }

    # Prepare environment variables
    seed = random.randint(0, 100000)
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),  # str(seed),
        'TEST_LEVEL': params['test_level'],
        'TEST_WIDTH': str(params['WIDTH'])
    }

    # Calculate timeout based on test complexity
    complexity_factor = 1.0
    # sourcery skip: no-conditionals-in-tests
    if params['test_level'] == 'medium':
        complexity_factor = 2.0
    elif params['test_level'] == 'full':
        complexity_factor = 5.0
    timeout_factor = complexity_factor * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


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

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
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
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure