# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ShifterUniversalConfig
# Purpose: Configuration class for Universal Shifter tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random

import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from conftest import get_coverage_compile_args

class ShifterUniversalConfig:
    """Configuration class for Universal Shifter tests"""
    def __init__(self, name, test_vectors, width=4):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            test_vectors: List of test vectors
            width: Data width
        """
        self.name = name
        self.test_vectors = test_vectors
        self.width = width

class ShifterUniversalTB(TBBase):
    """
    Testbench for the Universal Shifter module
    Features:
    - Verify all shift operations (hold, right shift, left shift, load)
    - Test serial input/output functionality with proper timing
    - Test with different data widths
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))

        # Calculate maximum data value based on width
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.select = self.dut.select
        self.i_pdata = self.dut.i_pdata
        self.i_sdata_lt = self.dut.i_sdata_lt
        self.i_sdata_rt = self.dut.i_sdata_rt
        self.o_pdata = self.dut.o_pdata
        self.o_sdata_lt = self.dut.o_sdata_lt
        self.o_sdata_rt = self.dut.o_sdata_rt

        # Operation select values for clarity
        self.SEL_HOLD = 0
        self.SEL_RIGHT_SHIFT = 1
        self.SEL_LEFT_SHIFT = 2
        self.SEL_LOAD = 3

        # Log configuration
        self.log.info("Universal Shifter TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Test results storage
        self.test_results = []
        self.test_failures = []

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f'Starting reset_dut{self.get_time_ns_str()}')

        # Initialize inputs
        self.select.value = 0
        self.i_pdata.value = 0
        self.i_sdata_lt.value = 0
        self.i_sdata_rt.value = 0

        # Apply reset
        self.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 5)

        self.log.debug('Ending reset_dut')

    async def drive_and_check(self, pdata, select, sdata_lt=0, sdata_rt=0, 
                            expected_pdata=None, expected_sdata_lt=None, expected_sdata_rt=None):
        """
        Drive the inputs and check the outputs

        Args:
            pdata: Parallel data input
            select: Operation select
            sdata_lt: Serial data input for left shifting
            sdata_rt: Serial data input for right shifting
            expected_pdata: Expected parallel data output
            expected_sdata_lt: Expected serial data output for left shifting
            expected_sdata_rt: Expected serial data output for right shifting

        Returns:
            True if outputs match expected values
        """
        # Ensure values are masked to appropriate width
        pdata &= self.MAX_DATA
        select &= 0x3
        sdata_lt &= 0x1
        sdata_rt &= 0x1

        # Get current state before driving inputs
        prev_pdata = int(self.o_pdata.value) & self.MAX_DATA

        self.log.info(f"Testing{self.get_time_ns_str()}: pdata=0x{pdata:x}, select={select}, " +
                    f"sdata_lt={sdata_lt}, sdata_rt={sdata_rt}, prev_pdata=0x{prev_pdata:x}")

        # Calculate expected outputs if not provided
        if expected_pdata is None or expected_sdata_lt is None or expected_sdata_rt is None:
            calc_pdata, calc_sdata_lt, calc_sdata_rt = self._calculate_expected_outputs(
                pdata, select, sdata_lt, sdata_rt, prev_pdata)
            
            if expected_pdata is None:
                expected_pdata = calc_pdata
            if expected_sdata_lt is None:
                expected_sdata_lt = calc_sdata_lt
            if expected_sdata_rt is None:
                expected_sdata_rt = calc_sdata_rt

        # Drive the inputs
        self.i_pdata.value = pdata
        self.select.value = select
        self.i_sdata_lt.value = sdata_lt
        self.i_sdata_rt.value = sdata_rt

        # Wait for the clock edge
        await self.wait_clocks('clk', 1)

        # Read the outputs
        actual_pdata = int(self.o_pdata.value) & self.MAX_DATA
        actual_sdata_lt = int(self.o_sdata_lt.value) & 0x1
        actual_sdata_rt = int(self.o_sdata_rt.value) & 0x1

        # Check the outputs
        pdata_match = (actual_pdata == expected_pdata)
        sdata_lt_match = (actual_sdata_lt == expected_sdata_lt)
        sdata_rt_match = (actual_sdata_rt == expected_sdata_rt)
        all_match = pdata_match and sdata_lt_match and sdata_rt_match

        # Log the results
        if all_match:
            self.log.info(f"PASS: pdata=0x{actual_pdata:x}, " +
                        f"sdata_lt={actual_sdata_lt}, sdata_rt={actual_sdata_rt}")
        else:
            self.log.error(f"FAIL: inputs(pdata=0x{pdata:x}, select={select}, " +
                            f"sdata_lt={sdata_lt}, sdata_rt={sdata_rt})")
            if not pdata_match:
                self.log.error(f"  pdata: expected=0x{expected_pdata:x}, actual=0x{actual_pdata:x}")
            if not sdata_lt_match:
                self.log.error(f"  sdata_lt: expected={expected_sdata_lt}, actual={actual_sdata_lt}")
            if not sdata_rt_match:
                self.log.error(f"  sdata_rt: expected={expected_sdata_rt}, actual={actual_sdata_rt}")

        # Store the results
        result = {
            'prev_pdata': prev_pdata,
            'pdata': pdata,
            'select': select,
            'sdata_lt': sdata_lt,
            'sdata_rt': sdata_rt,
            'expected_pdata': expected_pdata,
            'actual_pdata': actual_pdata,
            'expected_sdata_lt': expected_sdata_lt,
            'actual_sdata_lt': actual_sdata_lt,
            'expected_sdata_rt': expected_sdata_rt,
            'actual_sdata_rt': actual_sdata_rt,
            'pdata_match': pdata_match,
            'sdata_lt_match': sdata_lt_match,
            'sdata_rt_match': sdata_rt_match,
            'all_match': all_match
        }
        self.test_results.append(result)
        
        if not all_match:
            self.test_failures.append(result)

        return all_match

    def _calculate_expected_outputs(self, pdata, select, sdata_lt, sdata_rt, prev_pdata):
        """
        Calculate expected outputs for the given inputs based on the updated RTL timing

        Args:
            pdata: Parallel data input
            select: Operation select
            sdata_lt: Serial data input for left shifting
            sdata_rt: Serial data input for right shifting
            prev_pdata: Previous parallel data output (current state)

        Returns:
            Tuple of (expected_pdata, expected_sdata_lt, expected_sdata_rt)
        """
        # Ensure values are masked to appropriate width
        pdata &= self.MAX_DATA
        select &= 0x3
        sdata_lt &= 0x1
        sdata_rt &= 0x1
        prev_pdata &= self.MAX_DATA

        # Calculate expected outputs based on the fixed RTL
        if select == self.SEL_HOLD:
            # Hold operation - keep previous value, no serial outputs
            expected_pdata = prev_pdata
            expected_sdata_lt = 0
            expected_sdata_rt = 0
            
        elif select == self.SEL_RIGHT_SHIFT:
            # Right shift operation
            expected_pdata = ((prev_pdata >> 1) | (sdata_rt << (self.WIDTH - 1))) & self.MAX_DATA
            expected_sdata_lt = 0  # Not used in right shift
            expected_sdata_rt = prev_pdata & 0x1  # Bit being shifted out (LSB)
            
        elif select == self.SEL_LEFT_SHIFT:
            # Left shift operation
            expected_pdata = ((prev_pdata << 1) | sdata_lt) & self.MAX_DATA
            expected_sdata_lt = (prev_pdata >> (self.WIDTH - 1)) & 0x1  # Bit being shifted out (MSB)
            expected_sdata_rt = 0  # Not used in left shift
            
        else:  # select == self.SEL_LOAD
            # Load operation - parallel in, no serial outputs
            expected_pdata = pdata
            expected_sdata_lt = 0
            expected_sdata_rt = 0

        return (expected_pdata, expected_sdata_lt, expected_sdata_rt)

    async def test_hold_operation(self):
        """
        Test hold operation (select=0)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing hold operation (select=0)")

        # Reset DUT
        await self.reset_dut()

        # First, load a known value
        test_data = 0xA & self.MAX_DATA
        await self.drive_and_check(test_data, self.SEL_LOAD)

        # Now test hold operation for multiple cycles
        all_passed = True
        for i in range(5):
            # Change parallel input but keep select=0 (hold)
            new_data = random.randint(0, self.MAX_DATA)
            test_passed = await self.drive_and_check(new_data, self.SEL_HOLD)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

        return all_passed

    async def test_right_shift_operation(self):
        """
        Test right shift operation (select=1)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing right shift operation (select=1)")

        # Reset DUT
        await self.reset_dut()

        # First, load a known value
        test_data = 0xA & self.MAX_DATA  # Binary: 1010 for 4-bit
        await self.drive_and_check(test_data, self.SEL_LOAD)

        all_passed = True

        # Test right shift with 0 serial input
        test_passed = await self.drive_and_check(0, self.SEL_RIGHT_SHIFT, 0, 0)
        if not test_passed:
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return False

        # Test right shift with 1 serial input
        test_passed = await self.drive_and_check(0, self.SEL_RIGHT_SHIFT, 0, 1)
        if not test_passed:
            all_passed = False

        return all_passed

    async def test_left_shift_operation(self):
        """
        Test left shift operation (select=2)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing left shift operation (select=2)")

        # Reset DUT
        await self.reset_dut()

        # First, load a known value
        test_data = 0x5 & self.MAX_DATA  # Binary: 0101 for 4-bit
        await self.drive_and_check(test_data, self.SEL_LOAD)

        all_passed = True

        # Test left shift with 0 serial input
        test_passed = await self.drive_and_check(0, self.SEL_LEFT_SHIFT, 0, 0)
        if not test_passed:
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return False

        # Test left shift with 1 serial input
        test_passed = await self.drive_and_check(0, self.SEL_LEFT_SHIFT, 1, 0)
        if not test_passed:
            all_passed = False

        return all_passed

    async def test_load_operation(self):
        """
        Test load operation (select=3)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing load operation (select=3)")

        # Reset DUT
        await self.reset_dut()

        # Test loading different values
        test_values = [
            0,
            1,
            0xA & self.MAX_DATA,
            0x5 & self.MAX_DATA,
            self.MAX_DATA
        ]

        all_passed = True

        for test_data in test_values:
            test_passed = await self.drive_and_check(test_data, self.SEL_LOAD)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

        return all_passed

    async def test_serial_io(self):
        """
        Test serial input/output functionality with proper timing

        Returns:
            True if all tests passed
        """
        self.log.info("Testing serial I/O functionality")

        # Skip in basic mode
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping detailed serial I/O tests in basic mode")
            return True

        # Reset DUT
        await self.reset_dut()

        # Load initial value
        test_data = 0xA & self.MAX_DATA  # Binary: 1010 for 4-bit
        await self.drive_and_check(test_data, self.SEL_LOAD)

        all_passed = True

        # Test shifting data out to the right
        self.log.info("Testing right shift serial output")
        curr_data = test_data

        for i in range(self.WIDTH):
            expected_bit_out = curr_data & 0x1  # LSB should come out on o_sdata_rt
            
            # Perform right shift with 0 input
            test_passed = await self.drive_and_check(0, self.SEL_RIGHT_SHIFT, 0, 0)
            
            # Check if the correct bit was shifted out
            actual_bit_out = self.test_results[-1]['actual_sdata_rt']
            
            if actual_bit_out != expected_bit_out:
                self.log.error(f"Right shift bit {i}: expected bit out={expected_bit_out}, " +
                              f"actual bit out={actual_bit_out}")
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            curr_data = curr_data >> 1  # Update for next iteration

        if not all_passed and self.TEST_LEVEL == 'medium':
            return False

        # Reset and test shifting data out to the left
        await self.reset_dut()
        test_data = 0x5 & self.MAX_DATA  # Binary: 0101 for 4-bit
        await self.drive_and_check(test_data, self.SEL_LOAD)

        self.log.info("Testing left shift serial output")
        curr_data = test_data

        for i in range(self.WIDTH):
            expected_bit_out = (curr_data >> (self.WIDTH - 1)) & 0x1  # MSB should come out on o_sdata_lt
            
            # Perform left shift with 0 input
            test_passed = await self.drive_and_check(0, self.SEL_LEFT_SHIFT, 0, 0)
            
            # Check if the correct bit was shifted out
            actual_bit_out = self.test_results[-1]['actual_sdata_lt']
            
            if actual_bit_out != expected_bit_out:
                self.log.error(f"Left shift bit {i}: expected bit out={expected_bit_out}, " +
                              f"actual bit out={actual_bit_out}")
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            curr_data = (curr_data << 1) & self.MAX_DATA  # Update for next iteration

        return all_passed

    async def test_shift_pattern(self):
        """
        Test shifting specific patterns through the register

        Returns:
            True if all tests passed
        """
        self.log.info("Testing shift patterns")

        # Reset DUT
        await self.reset_dut()

        # Define patterns to shift in
        if self.TEST_LEVEL == 'basic':
            pattern = [1, 0, 1, 0][:self.WIDTH]
        elif self.TEST_LEVEL == 'medium':
            pattern = [1, 1, 0, 1, 0, 1, 0, 0][:self.WIDTH]
        else:  # full
            pattern = [random.randint(0, 1) for _ in range(self.WIDTH)]

        # Ensure pattern is exactly WIDTH bits
        while len(pattern) < self.WIDTH:
            pattern.extend(pattern)
        pattern = pattern[:self.WIDTH]

        self.log.info(f"Testing with pattern: {pattern}")

        # First, clear the register
        await self.drive_and_check(0, self.SEL_LOAD)

        all_passed = True

        # Shift in the pattern from the right
        self.log.info("Shifting pattern in from right")
        for i, bit in enumerate(pattern):
            test_passed = await self.drive_and_check(0, self.SEL_RIGHT_SHIFT, 0, bit)
            
            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break
                    
            # Log current state for debugging
            current_data = self.test_results[-1]['actual_pdata']
            self.log.debug(f"After shift {i+1}: data=0x{current_data:x}")

        if not all_passed and self.TEST_LEVEL == 'basic':
            return False

        # Clear and shift in from the left
        await self.drive_and_check(0, self.SEL_LOAD)
        
        self.log.info("Shifting pattern in from left")
        for i, bit in enumerate(pattern):
            test_passed = await self.drive_and_check(0, self.SEL_LEFT_SHIFT, bit, 0)
            
            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break
                    
            # Log current state for debugging
            current_data = self.test_results[-1]['actual_pdata']
            self.log.debug(f"After shift {i+1}: data=0x{current_data:x}")

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}{self.get_time_ns_str()}")

        # Define test functions and their conditions based on test level
        test_functions = [
            # (function, name, run_in_basic, run_in_medium, run_in_full)
            (self.test_hold_operation, "Hold operation", True, True, True),
            (self.test_right_shift_operation, "Right shift operation", True, True, True),
            (self.test_left_shift_operation, "Left shift operation", True, True, True),
            (self.test_load_operation, "Load operation", True, True, True),
            (self.test_serial_io, "Serial I/O functionality", False, True, True),
            (self.test_shift_pattern, "Shift patterns", True, True, True),
        ]

        all_passed = True
        test_results = {}
        test_number = 1

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests based on the test level
        for test_func, test_name, run_in_basic, run_in_medium, run_in_full in test_functions:
            should_run = (
                (self.TEST_LEVEL == 'basic' and run_in_basic)
                or (self.TEST_LEVEL == 'medium' and run_in_medium)
                or (self.TEST_LEVEL == 'full' and run_in_full)
            )
            
            if should_run:
                self.log.info(f"{test_number}. Testing {test_name}")
                try:
                    test_passed = await test_func()
                    test_results[test_name] = test_passed

                    if not test_passed:
                        self.log.error(f"{test_name} test FAILED")
                        all_passed = False
                    else:
                        self.log.info(f"{test_name} test PASSED")

                except Exception as e:
                    self.log.error(f"{test_name} test raised exception: {str(e)}")
                    test_results[test_name] = False
                    all_passed = False

                test_number += 1
            else:
                self.log.info(f"Skipping {test_name} test at {self.TEST_LEVEL} level")
                test_results[test_name] = "Skipped"

        # Print summary of test results
        self.log.info("="*50)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*50)
        for test_name, result in test_results.items():
            if result == "Skipped":
                status = "SKIPPED"
            else:
                status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*50)
        
        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall result: {overall_status}")
        self.log.info("="*50)

        # Print detailed summary of individual operations
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(1 for r in self.test_results if r['all_match'])
        failed_tests = len(self.test_failures)

        self.log.info("="*50)
        self.log.info(f"DETAILED TEST SUMMARY")
        self.log.info(f"Total operations tested: {total_tests}")
        self.log.info(f"Passed: {passed_tests}")
        self.log.info(f"Failed: {failed_tests}")
        self.log.info("="*50)

        # Print detailed results for failures
        if failed_tests > 0:
            self.log.error(f"FAILED TEST DETAILS ({failed_tests} failures):")
            for i, failure in enumerate(self.test_failures):
                self.log.error(f"Failure {i+1}:")
                self.log.error(f"  Inputs: prev_pdata=0x{failure['prev_pdata']:x}, " +
                              f"pdata=0x{failure['pdata']:x}, select={failure['select']}, " +
                              f"sdata_lt={failure['sdata_lt']}, sdata_rt={failure['sdata_rt']}")

                if not failure['pdata_match']:
                    self.log.error(f"  pdata mismatch: " +
                                  f"expected=0x{failure['expected_pdata']:x}, " +
                                  f"actual=0x{failure['actual_pdata']:x}")

                if not failure['sdata_lt_match']:
                    self.log.error(f"  sdata_lt mismatch: " +
                                  f"expected={failure['expected_sdata_lt']}, " +
                                  f"actual={failure['actual_sdata_lt']}")

                if not failure['sdata_rt_match']:
                    self.log.error(f"  sdata_rt mismatch: " +
                                  f"expected={failure['expected_sdata_rt']}, " +
                                  f"actual={failure['actual_sdata_rt']}")
                self.log.error("")

# Single comprehensive test function that handles all test levels
@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = ShifterUniversalTB(dut)

    # Start clock with configured period
    await tb.start_clock('clk', 10, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Report final result and PROPERLY FAIL if tests failed
    tb.log.info(f"Comprehensive test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL}")

    # CRITICAL FIX: Actually assert on the result so test fails when it should
    assert passed, f"Universal Shifter test FAILED - {len(tb.test_failures)} individual test failures detected"

    return passed

def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (8-bit, basic)
    REG_LEVEL=FUNC: 1 test (8-bit, full) - default
    REG_LEVEL=FULL: 3 tests (8, 16, 32-bit, full)

    Returns:
        List of dicts with WIDTH, test_level
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH': 8, 'test_level': 'full'},
        ]
    else:  # FULL
        return [
            {'WIDTH': 8, 'test_level': 'full'},
            {'WIDTH': 16, 'test_level': 'full'},
            {'WIDTH': 32, 'test_level': 'full'},
        ]

@pytest.mark.parametrize("params", generate_test_params())
def test_shifter_universal(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "shifter_universal"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_universal.f'
    )

    # Create a human-readable test identifier
    t_width = params['WIDTH']
    t_name = params['test_level']
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_W{t_width}_{t_name}_{reg_level}"

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
    # RTL parameters
    parameters = {
        'WIDTH': params['WIDTH']
    }

    # Prepare environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),
        'TEST_LEVEL': params['test_level'],
        'TEST_WIDTH': str(params['WIDTH'])
    }

    # Calculate timeout based on test complexity
    complexity_factor = 1.0
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

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
            python_search=[tests_dir],
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
