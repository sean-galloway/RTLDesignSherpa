# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ChecksumConfig
# Purpose: Configuration class for Checksum tests
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
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run


# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class ChecksumConfig:
    """Configuration class for Checksum tests"""
    def __init__(self, name, test_vectors, width=8):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            test_vectors: List of test vectors (list of data values)
            width: Data width
        """
        self.name = name
        self.test_vectors = test_vectors
        self.width = width


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
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
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
                if self.TEST_LEVEL == 'basic':
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

        # Test multiple overflows if not in basic mode
        if self.TEST_LEVEL != 'basic':
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
        if self.TEST_LEVEL == 'basic':
            num_tests = 2
            max_length = 10
        elif self.TEST_LEVEL == 'medium':
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
                if self.TEST_LEVEL == 'basic':
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
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 2. Reset functionality test
        self.log.info("2. Testing reset functionality")
        reset_passed = await self.test_reset_functionality()
        if not reset_passed:
            self.log.error("Reset functionality test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 3. Overflow behavior test
        self.log.info("3. Testing overflow behavior")
        overflow_passed = await self.test_overflow_behavior()
        if not overflow_passed:
            self.log.error("Overflow behavior test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # Skip random data test in basic mode
        if self.TEST_LEVEL != 'basic':
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
        if self.TEST_LEVEL != 'basic' and passed_tests < total_tests:
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


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = ChecksumTB(dut)

    # Start clock with configured period
    await tb.start_clock('clk', 10, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8-bit, basic+medium)
    REG_LEVEL=FUNC: 4 tests (varied widths, medium) - default
    REG_LEVEL=FULL: 6 tests (all combinations)

    Returns:
        List of dicts with WIDTH and test_level
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'test_level': 'basic'},
            {'WIDTH': 8, 'test_level': 'medium'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH':  4, 'test_level': 'medium'},
            {'WIDTH':  8, 'test_level': 'medium'},
            {'WIDTH': 16, 'test_level': 'medium'},
            {'WIDTH': 32, 'test_level': 'medium'},
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
def test_dataint_checksum(request, params): # sourcery skip: no-conditionals-in-tests
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "dataint_checksum"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/dataint_checksum.f'
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