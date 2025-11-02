# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiGenAddrConfig
# Purpose: Configuration class for AXI Address Generator tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import contextlib
import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class AxiGenAddrConfig:
    """Configuration class for AXI Address Generator tests"""
    def __init__(self, name, test_vectors, aw=32, dw=32, odw=32, len_width=8):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            test_vectors: List of test vectors (dict with addr, size, burst, len, expected_next, expected_align)
            aw: Address width
            dw: Data width
            odw: Output data width
            len_width: Length parameter width
        """
        self.name = name
        self.test_vectors = test_vectors
        self.aw = aw
        self.dw = dw
        self.odw = odw
        self.len_width = len_width


class AxiGenAddrTB(TBBase):
    """
    Testbench for the AXI Address Generator module
    Features:
    - Verify address generation for all burst types (FIXED, INCR, WRAP)
    - Test various data sizes and address alignments
    - Test with different data widths
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.ODW = self.convert_to_int(os.environ.get('TEST_ODW', '32'))
        self.LEN = self.convert_to_int(os.environ.get('TEST_LEN', '8'))

        # Calculate bytes per transfer based on data width
        self.DW_BYTES = self.DW // 8
        self.ODW_BYTES = self.ODW // 8

        # Maximum values based on parameters
        self.MAX_ADDR = (1 << self.AW) - 1
        self.MAX_LEN = (1 << self.LEN) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.curr_addr = self.dut.curr_addr
        self.size = self.dut.size
        self.burst = self.dut.burst
        self.len = self.dut.len
        self.next_addr = self.dut.next_addr
        self.next_addr_align = self.dut.next_addr_align

        # Log configuration
        self.log.info("AXI Address Generator TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"AW={self.AW}, DW={self.DW}, ODW={self.ODW}, LEN={self.LEN}")
        self.log.info(f"DW_BYTES={self.DW_BYTES}, ODW_BYTES={self.ODW_BYTES}")

        # Test results storage
        self.test_results = []

    async def drive_and_check(self, curr_addr, size, burst, length, expected_next=None, expected_align=None):
        """
        Drive the inputs and check the outputs

        Args:
            curr_addr: Current address
            size: Size parameter (0=byte, 1=halfword, 2=word, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            length: Burst length
            expected_next: Expected next address (None for auto calculation)
            expected_align: Expected aligned address (None for auto calculation)

        Returns:
            True if outputs match expected values
        """
        # Ensure values are within parameter limits
        curr_addr &= self.MAX_ADDR
        size &= 0x7  # 3 bits
        burst &= 0x3  # 2 bits
        length &= self.MAX_LEN

        self.log.info(f"Testing: addr=0x{curr_addr:08x}, size={size}, burst={burst}, len={length}")

        # Drive inputs
        self.curr_addr.value = curr_addr
        self.size.value = size
        self.burst.value = burst
        self.len.value = length

        # Wait a small time for combinational logic to settle
        await Timer(1, units='ns')

        # Read outputs
        actual_next = int(self.next_addr.value)
        actual_align = int(self.next_addr_align.value)

        # Calculate expected outputs if not provided
        if expected_next is None:
            expected_next = self._calculate_expected_next_addr(curr_addr, size, burst, length)

        if expected_align is None:
            expected_align = actual_next & ~(self.ODW_BYTES - 1)

        # Check results
        next_match = (actual_next == expected_next)
        align_match = (actual_align == expected_align)

        # Log results
        if next_match and align_match:
            self.log.info(f"PASS: next=0x{actual_next:08x}, align=0x{actual_align:08x}")
        else:
            self.log.error(f"FAIL: addr=0x{curr_addr:08x}, size={size}, burst={burst}, len={length}")
        if not next_match:
            self.log.error(f"  Next address: expected=0x{expected_next:08x}, actual=0x{actual_next:08x}")
        if not align_match:
            self.log.error(f"  Aligned address: expected=0x{expected_align:08x}, actual=0x{actual_align:08x}")

        # Store result for reporting
        self.test_results.append({
            'curr_addr': curr_addr,
            'size': size,
            'burst': burst,
            'length': length,
            'expected_next': expected_next,
            'actual_next': actual_next,
            'expected_align': expected_align,
            'actual_align': actual_align,
            'next_match': next_match,
            'align_match': align_match
        })

        return next_match and align_match

    def _calculate_expected_next_addr(self, curr_addr, size, burst, length):
        """
        Calculate the expected next address

        Args:
            curr_addr: Current address
            size: Size parameter (0=byte, 1=halfword, 2=word, etc.)
            burst: Burst type (0=FIXED, 1=INCR, 2=WRAP)
            length: Burst length

        Returns:
            Expected next address
        """
        # Apply address mask based on AW
        curr_addr &= self.MAX_ADDR

        # Calculate increment based on size
        increment_pre = 1 << size
        increment = increment_pre

        # Adjust increment if there's a data width difference
        if self.DW != self.ODW:
            increment = min(increment, self.ODW_BYTES)
        # Calculate next address based on burst type
        if burst == 0:  # FIXED
            return curr_addr
        elif burst == 1 or burst != 2:  # INCR
            return (curr_addr + increment) & self.MAX_ADDR
        else:  # WRAP
            # Calculate wrap mask based on size and length
            wrap_mask = (1 << (size + self._clog2(length + 1))) - 1

            # Calculate aligned address
            aligned_addr = (curr_addr + increment) & ~(increment - 1)

            # Calculate wrap address
            wrap_addr = (curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask)

            return wrap_addr & self.MAX_ADDR

    def _clog2(self, value):
        """
        Calculate ceil(log2(value))

        Args:
            value: Input value

        Returns:
            ceil(log2(value))
        """
        return 0 if value <= 0 else (value - 1).bit_length()

    async def test_fixed_burst(self):
        """
        Test fixed burst addressing

        Returns:
            True if all tests passed
        """
        self.log.info("Running fixed burst tests")

        # Fixed burst should always return the same address
        sizes = [0, 1, 2, 3]  # byte, halfword, word, doubleword
        addrs = [addr & self.MAX_ADDR for addr in [0x00000000, 0x12345678, 0xFFFFFFFC]]
        lengths = [0, 1, 15]

        if self.TEST_LEVEL != 'basic':
            # Add more test cases for higher test levels
            sizes.extend([4, 5, 6, 7])
            addrs.extend([0x55555555, 0xAAAAAAAA])
            lengths.extend([7, 255])

        all_passed = True

        for addr in addrs:
            for size in sizes:
                for length in lengths:
                    # For fixed burst, expected_next should be the same as curr_addr
                    test_passed = await self.drive_and_check(addr, size, 0, length, addr)

                    if not test_passed:
                        all_passed = False
                        if self.TEST_LEVEL == 'basic':
                            # Stop on first failure in basic mode
                            return False

        return all_passed

    async def test_incr_burst(self):
        """
        Test incremental burst addressing

        Returns:
            True if all tests passed
        """
        self.log.info("Running incremental burst tests")

        # Define test cases with different sizes and alignments
        test_cases = [
            # addr, size, length
            (0x00000000, 0, 0),   # byte transfers, aligned, 1 transfer
            (0x00000001, 0, 1),   # byte transfers, unaligned, 2 transfers
            (0x00000000, 2, 3),   # word transfers, aligned, 4 transfers
            (0x00000002, 2, 7),   # word transfers, unaligned, 8 transfers
            (0x12345678, 3, 15),  # doubleword transfers, complex address, 16 transfers
        ]

        if self.TEST_LEVEL != 'basic':
            # Add more test cases for higher test levels
            test_cases.extend([
                (0xFFFFFFFC, 2, 1),      # word transfers near address wrap, 2 transfers
                (0x55555555, 1, 0),      # halfword transfers, odd pattern, 1 transfer
                (0xAAAAAAAA, 4, 7),      # 16-byte transfers, odd pattern, 8 transfers
                (0x00FFFF00, 5, 3),      # 32-byte transfers, complex address, 4 transfers
                (0x12345678, 6, 255),    # 64-byte transfers, complex address, 256 transfers
            ])

        all_passed = True

        for addr, size, length in test_cases:
            # For incr burst, expected_next should be curr_addr + increment
            test_passed = await self.drive_and_check(addr, size, 1, length)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    # Stop on first failure in basic mode
                    return False

        # Also test random cases for incr burst if not in basic mode
        if self.TEST_LEVEL != 'basic':
            num_random_tests = 10 if self.TEST_LEVEL == 'medium' else 50

            for _ in range(num_random_tests):
                addr = random.randint(0, self.MAX_ADDR)
                size = random.randint(0, 7)
                length = random.randint(0, self.MAX_LEN)

                test_passed = await self.drive_and_check(addr, size, 1, length)

                if not test_passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'medium':
                        # Stop on first failure in medium mode
                        return False

        return all_passed

    async def test_wrap_burst(self):
        """
        Test wrap burst addressing

        Returns:
            True if all tests passed
        """
        self.log.info("Running wrap burst tests")

        # Define test cases with different wrap boundaries
        test_cases = [
            # addr, size, length - These values create different wrap boundaries
            (0x00000000, 0, 1),   # 2-byte wrap at byte granularity
            (0x00000001, 0, 3),   # 4-byte wrap at byte granularity
            (0x00000002, 0, 7),   # 8-byte wrap at byte granularity
            (0x00000000, 2, 1),   # 8-byte wrap at word granularity
            (0x00000004, 2, 3),   # 16-byte wrap at word granularity
            (0x00000008, 2, 7),   # 32-byte wrap at word granularity
            (0x12345678, 2, 3),   # 16-byte wrap with complex address
        ]

        if self.TEST_LEVEL != 'basic':
            # Add more test cases for higher test levels
            test_cases.extend([
                (0xFFFFFFFC, 2, 1),      # word transfers near address space limit
                (0x55555550, 3, 3),      # doubleword transfers with complex pattern
                (0xAAAAAAA0, 4, 7),      # 16-byte transfers with complex pattern
                (0x00FFFF00, 5, 3),      # 32-byte transfers with complex address
                (0x12345600, 6, 7),      # 64-byte transfers with complex address
            ])

        all_passed = True

        for addr, size, length in test_cases:
            # For wrap burst, expected_next is calculated in the driver function
            test_passed = await self.drive_and_check(addr, size, 2, length)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    # Stop on first failure in basic mode
                    return False

        # Also test random cases for wrap burst if not in basic mode
        if self.TEST_LEVEL != 'basic':
            num_random_tests = 10 if self.TEST_LEVEL == 'medium' else 50

            for _ in range(num_random_tests):
                addr = random.randint(0, self.MAX_ADDR)
                size = random.randint(0, 7)
                # Length for wrap burst must be 1, 3, 7, 15, etc. (2^n - 1)
                length_exp = random.randint(0, min(7, self.LEN - 1))  # Max 256 transfers
                length = (1 << length_exp) - 1

                test_passed = await self.drive_and_check(addr, size, 2, length)

                if not test_passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'medium':
                        # Stop on first failure in medium mode
                        return False

        return all_passed

    async def test_different_data_widths(self):
        """
        Test address generation with different data widths (DW != ODW)

        Returns:
            True if all tests passed
        """
        # Skip this test if DW and ODW are the same - nothing special to test
        if self.DW == self.ODW:
            self.log.info("Skipping different data widths test - DW and ODW are the same")
            return True

        self.log.info(f"Running different data widths test (DW={self.DW}, ODW={self.ODW})")

        # Define test cases that test the data width difference handling
        test_cases = []

        # Add test cases to test data width handling
        if self.ODW > self.DW:
            # When ODW > DW, increment is still based on size
            test_cases.extend([
                (0x00000000, 0, 1, 0),  # byte transfers, INCR burst
                (0x00000000, 2, 1, 0),  # word transfers, INCR burst
                (0x00000000, 4, 1, 0),  # 16-byte transfers, INCR burst
            ])
        else:  # self.ODW < self.DW
            # When ODW < DW, large increments should be capped at ODW_BYTES
            test_cases.extend([
                (0x00000000, 0, 1, 0),   # byte transfers (no capping)
                (0x00000000, 1, 1, 0),   # halfword transfers (no capping if ODW_BYTES >= 2)
                (0x00000000, self._clog2(self.ODW_BYTES) + 1, 1, 0),  # Just over ODW_BYTES
                (0x00000000, 6, 1, 0),   # 64-byte transfers (capping at ODW_BYTES)
            ])

        all_passed = True

        for addr, size, burst, length in test_cases:
            test_passed = await self.drive_and_check(addr, size, burst, length)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    # Stop on first failure in basic mode
                    return False

        return all_passed

    async def test_alignment(self):
        """
        Test address alignment for different sizes and output data widths

        Returns:
            True if all tests passed
        """
        self.log.info("Running alignment tests")

        # Test cases for alignment testing
        test_cases = [
            # addr, size, burst, length
            (0x00000000, 0, 1, 0),  # Aligned byte
            (0x00000001, 0, 1, 0),  # Unaligned byte
            (0x00000002, 1, 1, 0),  # Aligned halfword
            (0x00000003, 1, 1, 0),  # Unaligned halfword
            (0x00000004, 2, 1, 0),  # Aligned word
            (0x00000005, 2, 1, 0),  # Unaligned word
            (0x00000008, 3, 1, 0),  # Aligned doubleword
            (0x0000000C, 3, 1, 0),  # Aligned doubleword at different address
            (0x0000000D, 3, 1, 0),  # Unaligned doubleword
        ]

        if self.TEST_LEVEL != 'basic':
            # Add more test cases for higher test levels
            test_cases.extend([
                (0xFFFFFFFC, 2, 1, 0),  # Word near address space limit
                (0xFFFFFFFD, 2, 1, 0),  # Unaligned word near address space limit
                (0x12345678, 4, 1, 0),  # 16-byte transfer with complex address
                (0x87654321, 5, 1, 0),  # 32-byte transfer with complex address
            ])

        all_passed = True

        for addr, size, burst, length in test_cases:
            # Calculate expected_align manually - it should be aligned to ODW_BYTES
            expected_next = self._calculate_expected_next_addr(addr, size, burst, length)
            expected_align = expected_next & ~(self.ODW_BYTES - 1)

            test_passed = await self.drive_and_check(addr, size, burst, length, expected_next, expected_align)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    # Stop on first failure in basic mode
                    return False

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}")

        all_passed = True

        # Test all burst types
        self.log.info("1. Testing fixed burst")
        fixed_burst_passed = await self.test_fixed_burst()
        if not fixed_burst_passed:
            self.log.error("Fixed burst tests failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        self.log.info("2. Testing incremental burst")
        incr_burst_passed = await self.test_incr_burst()
        if not incr_burst_passed:
            self.log.error("Incremental burst tests failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        self.log.info("3. Testing wrap burst")
        wrap_burst_passed = await self.test_wrap_burst()
        if not wrap_burst_passed:
            self.log.error("Wrap burst tests failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # Test alignment functionality
        self.log.info("4. Testing address alignment")
        alignment_passed = await self.test_alignment()
        if not alignment_passed:
            self.log.error("Alignment tests failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # Test data width difference handling
        self.log.info("5. Testing different data widths")
        diff_width_passed = await self.test_different_data_widths()
        if not diff_width_passed:
            self.log.error("Different data widths tests failed")
            all_passed = False

        # Print summary
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(bool(r['next_match'] and r['align_match'])
                                for r in self.test_results)

        self.log.info("="*50)
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed")
        self.log.info("="*50)

        # Print detailed results based on test level
        if self.TEST_LEVEL != 'basic' and passed_tests < total_tests:
            self.log.info("Failed tests:")
            for i, result in enumerate(self.test_results):
                if not (result['next_match'] and result['align_match']):
                    self.log.info(f"Test {i+1}:")
                    self.log.info(f"  Inputs: addr=0x{result['curr_addr']:08x}, " +
                                    f"size={result['size']}, burst={result['burst']}, len={result['length']}")

                if not result['next_match']:
                    self.log.info(f"  Next address mismatch: expected=0x{result['expected_next']:08x}, " +
                                    f"actual=0x{result['actual_next']:08x}")

                if not result['align_match']:
                    self.log.info(f"  Aligned address mismatch: expected=0x{result['expected_align']:08x}, " +
                                    f"actual=0x{result['actual_align']:08x}")


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = AxiGenAddrTB(dut)

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


@pytest.mark.parametrize("params", [
    # Test with standard configurations
    # {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'basic'},
    # {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'medium'},
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'full'},

    # Test with different data widths
    {'AW': 32, 'DW': 64, 'ODW': 32, 'LEN': 8, 'test_level': 'full'},  # DW > ODW
    {'AW': 32, 'DW': 32, 'ODW': 64, 'LEN': 8, 'test_level': 'full'},  # DW < ODW

    # Test with different address widths
    {'AW': 24, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'basic'},
    {'AW': 64, 'DW': 32, 'ODW': 32, 'LEN': 8, 'test_level': 'basic'},

    # Test with different length parameter
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 4, 'test_level': 'basic'},
    {'AW': 32, 'DW': 32, 'ODW': 32, 'LEN': 16, 'test_level': 'basic'},
])
def test_axi_gen_addr(request, params):
    """Run the test with pytest and configurable parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common',
            'rtl_amba_shared':'rtl/amba/shared',
        })

    dut_name = "axi_gen_addr"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # Create a human-readable test identifier
    t_aw = params['AW']
    t_dw = params['DW']
    t_odw = params['ODW']
    t_len = params['LEN']
    t_name = params['test_level']
    # Format parameters with lowercase and zero-padding for consistent sorting
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{t_aw:03d}_dw{t_dw:03d}_odw{t_odw:03d}_len{t_len:02d}_{t_name}"
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
    parameters = {}
    # sourcery skip: no-conditionals-in-tests
    if 'AW' in params:
        parameters['AW'] = params['AW']
    if 'DW' in params:
        parameters['DW'] = params['DW']
    if 'ODW' in params:
        parameters['ODW'] = params['ODW']
    if 'LEN' in params:
        parameters['LEN'] = params['LEN']

    # Convert parameters to format expected by simulator
    rtl_parameters = {k.upper(): str(v) for k, v in parameters.items()}

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
        'TEST_AW': str(params['AW']),
        'TEST_DW': str(params['DW']),
        'TEST_ODW': str(params['ODW']),
        'TEST_LEN': str(params['LEN'])
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
            
            "--trace-depth", "99",
    ]

    sim_args = [
            "--trace",  # Tell Verilator to use VCD
            
            "--trace-depth", "99",
    ]

    plusargs = [
            "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
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
