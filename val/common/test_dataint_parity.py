# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ParityTB
# Purpose: Generic Parity Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Parity Test with Parameterized Test Levels and Configuration

This test uses chunks, width, parity_type and test_level as parameters for maximum flexibility:

CONFIGURATION:
    chunks:      Number of parity chunks (1, 2, 4, 8)
    width:       Total data width (8, 16, 32, 64)
    parity_type: Even (1) or Odd (0) parity

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - chunks: [1, 2, 4, 8]
    - width: [8, 16, 32, 64]
    - parity_type: [0, 1] (odd, even)
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Data width for parity calculation
    TEST_CHUNKS: Number of parity chunks
    TEST_PARITY_TYPE: Parity type (0=odd, 1=even)
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class ParityTB(TBBase):
    """Testbench for Generic Parity module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '32'))
        self.CHUNKS = self.convert_to_int(os.environ.get('TEST_CHUNKS', '4'))
        self.PARITY_TYPE = self.convert_to_int(os.environ.get('TEST_PARITY_TYPE', '1'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate chunk parameters
        self.CHUNK_SIZE = self.WIDTH // self.CHUNKS
        self.EXTRA_BITS = self.WIDTH % self.CHUNKS
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Validate configuration
        if self.WIDTH % self.CHUNKS != 0 and self.CHUNKS > 1:
            self.log.warning(f"WIDTH {self.WIDTH} not evenly divisible by CHUNKS {self.CHUNKS}")

        # Log configuration
        self.log.info(f"Parity TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, CHUNKS={self.CHUNKS}, PARITY_TYPE={'EVEN' if self.PARITY_TYPE else 'ODD'}")
        self.log.info(f"CHUNK_SIZE={self.CHUNK_SIZE}, EXTRA_BITS={self.EXTRA_BITS}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.data_in = self.dut.data_in
        self.parity_in = self.dut.parity_in
        self.parity_type = self.dut.parity_type
        self.parity_out = self.dut.parity
        self.parity_err = self.dut.parity_err

    def _get_chunk_bounds(self, chunk_idx):
        """Get the bit bounds for a specific chunk"""
        lower_bound = chunk_idx * self.CHUNK_SIZE
        if chunk_idx < self.CHUNKS - 1:
            upper_bound = ((chunk_idx + 1) * self.CHUNK_SIZE) - 1
        else:
            upper_bound = self.WIDTH - 1
        return lower_bound, upper_bound

    def _calculate_expected_parity(self, data, chunk_idx):
        """Calculate expected parity for a specific chunk"""
        lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
        
        # Extract chunk data
        chunk_data = (data >> lower_bound) & ((1 << (upper_bound - lower_bound + 1)) - 1)
        
        # Calculate XOR parity
        xor_parity = 0
        while chunk_data:
            xor_parity ^= chunk_data & 1
            chunk_data >>= 1
        
        # Apply parity type (1=even, 0=odd)
        if self.PARITY_TYPE:  # Even parity
            return xor_parity
        else:  # Odd parity
            return xor_parity ^ 1

    def _calculate_all_expected_parities(self, data):
        """Calculate expected parity for all chunks"""
        expected_parities = 0
        for chunk_idx in range(self.CHUNKS):
            parity_bit = self._calculate_expected_parity(data, chunk_idx)
            expected_parities |= (parity_bit << chunk_idx)
        return expected_parities

    def _calculate_expected_errors(self, data, input_parities):
        """Calculate expected error flags for all chunks"""
        expected_errors = 0
        for chunk_idx in range(self.CHUNKS):
            expected_parity = self._calculate_expected_parity(data, chunk_idx)
            input_parity = (input_parities >> chunk_idx) & 1
            error_bit = 1 if (expected_parity != input_parity) else 0
            expected_errors |= (error_bit << chunk_idx)
        return expected_errors

    async def test_parity_generation(self):
        """Test parity generation functionality"""
        self.log.info("Testing parity generation")

        # Define test data based on level
        if self.TEST_LEVEL == 'basic':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
            # Add some chunk-specific patterns
            for chunk_idx in range(self.CHUNKS):
                lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
                chunk_mask = ((1 << (upper_bound - lower_bound + 1)) - 1) << lower_bound
                test_values.extend([chunk_mask, chunk_mask >> 1])
        elif self.TEST_LEVEL == 'medium':
            test_values = []
            # Add systematic patterns
            test_values.extend([0, 1, self.MAX_DATA >> 1, self.MAX_DATA])
            # Add chunk-specific patterns
            for chunk_idx in range(self.CHUNKS):
                lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
                chunk_size = upper_bound - lower_bound + 1
                chunk_mask = ((1 << chunk_size) - 1) << lower_bound
                test_values.extend([chunk_mask, chunk_mask >> 1, chunk_mask >> 2])
            # Add random values
            test_values.extend([random.randint(0, self.MAX_DATA) for _ in range(32)])
        else:  # full
            test_values = []
            # Add systematic patterns
            test_values.extend([0, 1, self.MAX_DATA >> 1, self.MAX_DATA])
            # Add walking bit patterns
            for bit_pos in range(min(self.WIDTH, 32)):
                test_values.append(1 << bit_pos)
            # Add chunk-specific patterns
            for chunk_idx in range(self.CHUNKS):
                lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
                chunk_size = upper_bound - lower_bound + 1
                # All combinations for small chunks, subset for large chunks
                if chunk_size <= 4:
                    for val in range(1 << chunk_size):
                        test_values.append(val << lower_bound)
                else:
                    for val in [0, 1, (1 << chunk_size) - 1, (1 << chunk_size) >> 1]:
                        test_values.append(val << lower_bound)
            # Add random values
            test_values.extend([random.randint(0, self.MAX_DATA) for _ in range(128)])

        # Remove duplicates and sort
        test_values = sorted(list(set(test_values)))
        test_values = [val for val in test_values if val <= self.MAX_DATA]

        all_passed = True

        for data in test_values:
            data &= self.MAX_DATA
            expected_parity = self._calculate_all_expected_parities(data)

            # Drive inputs
            self.data_in.value = data
            self.parity_type.value = self.PARITY_TYPE
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_parity = int(self.parity_out.value) & ((1 << self.CHUNKS) - 1)

            success = (actual_parity == expected_parity)

            if success:
                self.log.debug(f"PASS: data=0x{data:0{(self.WIDTH+3)//4}x} → parity=0x{actual_parity:x}")
            else:
                self.log.error(f"FAIL: data=0x{data:0{(self.WIDTH+3)//4}x}, " +
                             f"expected_parity=0x{expected_parity:x}, actual_parity=0x{actual_parity:x}")
                await self._dump_parity_debug_info(data, expected_parity, actual_parity)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'generation',
                'data': data,
                'expected_parity': expected_parity,
                'actual_parity': actual_parity,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_parity_checking(self):
        """Test parity checking (error detection) functionality"""
        self.log.info("Testing parity checking")

        # Define test data based on level
        if self.TEST_LEVEL == 'basic':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
        elif self.TEST_LEVEL == 'medium':
            test_values = [random.randint(0, self.MAX_DATA) for _ in range(16)]
            test_values.extend([0, 1, self.MAX_DATA >> 1, self.MAX_DATA])
        else:  # full
            test_values = [random.randint(0, self.MAX_DATA) for _ in range(64)]
            test_values.extend([0, 1, self.MAX_DATA >> 1, self.MAX_DATA])
            # Add chunk-specific patterns
            for chunk_idx in range(self.CHUNKS):
                lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
                chunk_mask = ((1 << (upper_bound - lower_bound + 1)) - 1) << lower_bound
                test_values.extend([chunk_mask, chunk_mask >> 1])

        # Remove duplicates
        test_values = sorted(list(set([val & self.MAX_DATA for val in test_values])))

        all_passed = True

        for data in test_values:
            # Test with correct parity (should show no errors)
            correct_parity = self._calculate_all_expected_parities(data)
            success1 = await self._test_parity_check(data, correct_parity, 0)
            if not success1:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Test with incorrect parity (should show errors)
            if self.TEST_LEVEL != 'basic':
                # Test each chunk with wrong parity
                for chunk_idx in range(min(self.CHUNKS, 4 if self.TEST_LEVEL == 'medium' else self.CHUNKS)):
                    wrong_parity = correct_parity ^ (1 << chunk_idx)
                    expected_error = 1 << chunk_idx
                    success2 = await self._test_parity_check(data, wrong_parity, expected_error)
                    if not success2:
                        all_passed = False
                        if self.TEST_LEVEL == 'medium':
                            break

                if not all_passed and self.TEST_LEVEL == 'medium':
                    break

        return all_passed

    async def _test_parity_check(self, data, input_parity, expected_error):
        """Test parity checking for specific inputs"""
        data &= self.MAX_DATA
        input_parity &= ((1 << self.CHUNKS) - 1)
        expected_error &= ((1 << self.CHUNKS) - 1)

        # Drive inputs
        self.data_in.value = data
        self.parity_in.value = input_parity
        self.parity_type.value = self.PARITY_TYPE
        await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

        actual_error = int(self.parity_err.value) & ((1 << self.CHUNKS) - 1)
        actual_parity = int(self.parity_out.value) & ((1 << self.CHUNKS) - 1)

        success = (actual_error == expected_error)

        if success:
            self.log.debug(f"PASS: data=0x{data:0{(self.WIDTH+3)//4}x}, " +
                         f"parity_in=0x{input_parity:x} → error=0x{actual_error:x}")
        else:
            self.log.error(f"FAIL: data=0x{data:0{(self.WIDTH+3)//4}x}, " +
                         f"parity_in=0x{input_parity:x}, expected_error=0x{expected_error:x}, " +
                         f"actual_error=0x{actual_error:x}")
            await self._dump_check_debug_info(data, input_parity, expected_error, actual_error, actual_parity)

        # Store result
        result = {
            'test_type': 'checking',
            'data': data,
            'input_parity': input_parity,
            'expected_error': expected_error,
            'actual_error': actual_error,
            'actual_parity': actual_parity,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return success

    async def _dump_parity_debug_info(self, data, expected_parity, actual_parity):
        """Dump debug information for parity generation failures"""
        self.log.error("="*80)
        self.log.error("PARITY GENERATION FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input data: 0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
        self.log.error(f"Parity type: {'EVEN' if self.PARITY_TYPE else 'ODD'}")
        self.log.error(f"Expected parity: 0x{expected_parity:x} ({expected_parity:0{self.CHUNKS}b})")
        self.log.error(f"Actual parity:   0x{actual_parity:x} ({actual_parity:0{self.CHUNKS}b})")

        # Analyze each chunk
        self.log.error("Chunk-by-chunk analysis:")
        for chunk_idx in range(self.CHUNKS):
            lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
            chunk_data = (data >> lower_bound) & ((1 << (upper_bound - lower_bound + 1)) - 1)
            expected_bit = (expected_parity >> chunk_idx) & 1
            actual_bit = (actual_parity >> chunk_idx) & 1
            
            # Count 1s in chunk
            ones_count = bin(chunk_data).count('1')
            
            self.log.error(f"  Chunk {chunk_idx} [bits {upper_bound}:{lower_bound}]:")
            self.log.error(f"    Data: 0x{chunk_data:x} ({chunk_data:0{upper_bound-lower_bound+1}b})")
            self.log.error(f"    Ones count: {ones_count}")
            self.log.error(f"    Expected parity: {expected_bit}")
            self.log.error(f"    Actual parity: {actual_bit}")
            self.log.error(f"    Match: {expected_bit == actual_bit}")

        self.log.error("="*80)

    async def _dump_check_debug_info(self, data, input_parity, expected_error, actual_error, actual_parity):
        """Dump debug information for parity checking failures"""
        self.log.error("="*80)
        self.log.error("PARITY CHECKING FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input data: 0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
        self.log.error(f"Input parity: 0x{input_parity:x} ({input_parity:0{self.CHUNKS}b})")
        self.log.error(f"Parity type: {'EVEN' if self.PARITY_TYPE else 'ODD'}")
        self.log.error(f"Expected error: 0x{expected_error:x} ({expected_error:0{self.CHUNKS}b})")
        self.log.error(f"Actual error:   0x{actual_error:x} ({actual_error:0{self.CHUNKS}b})")
        self.log.error(f"Actual parity:  0x{actual_parity:x} ({actual_parity:0{self.CHUNKS}b})")

        # Analyze each chunk
        self.log.error("Chunk-by-chunk analysis:")
        for chunk_idx in range(self.CHUNKS):
            lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
            chunk_data = (data >> lower_bound) & ((1 << (upper_bound - lower_bound + 1)) - 1)
            calculated_parity = self._calculate_expected_parity(data, chunk_idx)
            input_parity_bit = (input_parity >> chunk_idx) & 1
            expected_error_bit = (expected_error >> chunk_idx) & 1
            actual_error_bit = (actual_error >> chunk_idx) & 1
            
            ones_count = bin(chunk_data).count('1')
            
            self.log.error(f"  Chunk {chunk_idx} [bits {upper_bound}:{lower_bound}]:")
            self.log.error(f"    Data: 0x{chunk_data:x} ({chunk_data:0{upper_bound-lower_bound+1}b})")
            self.log.error(f"    Ones count: {ones_count}")
            self.log.error(f"    Calculated parity: {calculated_parity}")
            self.log.error(f"    Input parity: {input_parity_bit}")
            self.log.error(f"    Expected error: {expected_error_bit}")
            self.log.error(f"    Actual error: {actual_error_bit}")
            self.log.error(f"    Error match: {expected_error_bit == actual_error_bit}")

        self.log.error("="*80)

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test all zeros and all ones
        boundary_values = [0, self.MAX_DATA]
        
        # Test chunk boundaries
        for chunk_idx in range(self.CHUNKS):
            lower_bound, upper_bound = self._get_chunk_bounds(chunk_idx)
            # Single bit in chunk
            boundary_values.append(1 << lower_bound)
            boundary_values.append(1 << upper_bound)
            # All bits in chunk
            chunk_size = upper_bound - lower_bound + 1
            chunk_mask = ((1 << chunk_size) - 1) << lower_bound
            boundary_values.append(chunk_mask)

        # Test alternating patterns
        if self.WIDTH >= 8:
            boundary_values.extend([0x55555555 & self.MAX_DATA, 0xAAAAAAAA & self.MAX_DATA])

        boundary_values = sorted(list(set([val & self.MAX_DATA for val in boundary_values])))

        for data in boundary_values:
            # Test generation
            expected_parity = self._calculate_all_expected_parities(data)
            self.data_in.value = data
            self.parity_type.value = self.PARITY_TYPE
            await cocotb.triggers.Timer(1, units='ns')
            actual_parity = int(self.parity_out.value) & ((1 << self.CHUNKS) - 1)

            if actual_parity != expected_parity:
                self.log.error(f"Boundary test FAIL: data=0x{data:0{(self.WIDTH+3)//4}x}")
                all_passed = False
                break

            # Test checking with correct parity
            success = await self._test_parity_check(data, expected_parity, 0)
            if not success:
                all_passed = False
                break

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running PARITY tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_parity_generation, "Parity generation"),
            (self.test_parity_checking, "Parity checking"),
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
        self.log.info(f"Overall PARITY result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def parity_test(dut):
    """Test for Generic Parity module"""
    tb = ParityTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"PARITY test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Parity test FAILED - {len(tb.test_failures)} failures detected"

    return passed


def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 4 tests (16/32-bit, 1/2 chunks, even parity, basic)
    REG_LEVEL=FUNC: ~20 tests (varied configs, basic) - default
    REG_LEVEL=FULL: ~60 tests (all valid combinations, all levels)

    Returns:
        List of tuples: (data_width, chunks, parity_type, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [8, 16, 32, 64]      # Different data widths
    chunks_list = [1, 2, 4, 8]    # Different chunk counts
    parity_types = [0, 1]         # Odd and Even parity
    test_levels = ['basic', 'medium', 'full']

    if reg_level == 'GATE':
        # Quick smoke test: 16/32-bit, simple chunks, even parity, basic
        return [
            (16, 1, 1, 'basic'),
            (16, 2, 1, 'basic'),
            (32, 1, 1, 'basic'),
            (32, 2, 1, 'basic'),
        ]

    elif reg_level == 'FUNC':
        # Functional coverage: varied configs, basic level, even parity only
        valid_params = []
        for width, chunks in product(widths, chunks_list):
            if chunks <= width:
                valid_params.append((width, chunks, 1, 'basic'))  # even parity only
        return valid_params

    else:  # FULL
        # Comprehensive: all valid combinations
        valid_params = []
        for width, chunks, parity_type, test_level in product(widths, chunks_list, parity_types, test_levels):
            if chunks <= width:
                valid_params.append((width, chunks, parity_type, test_level))
        return valid_params


params = generate_params()


@pytest.mark.parametrize("data_width, chunks, parity_type, test_level", params)
def test_dataint_parity(request, data_width, chunks, parity_type, test_level):
    """
    Parameterized Generic Parity test with configurable chunks, width, parity type and test level.

    Chunks controls how many parity bits are calculated in parallel:
    - 1: Single parity bit for entire data width
    - 2, 4, 8: Multiple parity bits for data chunks

    Parity type controls even vs odd parity:
    - 0: Odd parity (XOR + 1)
    - 1: Even parity (XOR)

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "dataint_parity"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/dataint_parity.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 2)
    c_str = TBBase.format_dec(chunks, 1)
    p_str = "even" if parity_type else "odd"
    test_name_plus_params = f"test_parity_w{w_str}_c{c_str}_{p_str}_{test_level}"

    # Handle pytest-xdist parallel execution
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
        'WIDTH': str(data_width),
        'CHUNKS': str(chunks)
    }

    # Adjust timeout based on test level and data width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, data_width / 32.0)  # Larger widths take more time
    chunks_factor = max(1.0, chunks / 4.0)      # More chunks take more time
    base_timeout = 1500  # 1.5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor * chunks_factor)

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
        'TEST_WIDTH': str(data_width),
        'TEST_CHUNKS': str(chunks),
        'TEST_PARITY_TYPE': str(parity_type),
        'TEST_DEBUG': '1',
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
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: {chunks} chunks, width={data_width}, {p_str} parity")
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
            includes=[],
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
        print(f"✓ {test_level.upper()} test PASSED: {chunks} chunks, {p_str} parity")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
