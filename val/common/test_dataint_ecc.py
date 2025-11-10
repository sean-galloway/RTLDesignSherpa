# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HammingECCTB
# Purpose: Hamming ECC Test with Parameterized Test Levels and Module Selection
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Hamming ECC Test with Parameterized Test Levels and Module Selection

This test uses module_type and test_level as parameters for maximum flexibility:

MODULE TYPES:
    encoder:  Test only the encoder module (combinational)
    decoder:  Test only the decoder module (sequential)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - data_width: [4, 8, 16, 32]
    - module_type: [encoder, decoder]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Data width for ECC calculation
    TEST_MODULE: Module type (encoder/decoder/both)
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
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class HammingECCTB(TBBase):
    """Unified testbench for Hamming ECC modules"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.MODULE_TYPE = os.environ.get('TEST_MODULE', 'encoder').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate ECC parameters
        self.PARITY_BITS = math.ceil(math.log2(self.WIDTH + math.ceil(math.log2(self.WIDTH)) + 1))
        self.TOTAL_WIDTH = self.WIDTH + self.PARITY_BITS + 1
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Hamming ECC TB initialized - Module: {self.MODULE_TYPE.upper()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}, WIDTH={self.WIDTH}")
        self.log.info(f"PARITY_BITS={self.PARITY_BITS}, TOTAL_WIDTH={self.TOTAL_WIDTH}")

        # Initialize signal mappings based on module type
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings based on module type"""
        if self.MODULE_TYPE == 'encoder':
            self.data = self.dut.data
            self.encoded_data = self.dut.encoded_data

        elif self.MODULE_TYPE == 'decoder':
            self.clk = self.dut.clk
            self.rst_n = self.dut.rst_n
            self.enable = self.dut.enable
            self.hamming_data = self.dut.hamming_data
            self.data = self.dut.data
            self.error_detected = self.dut.error_detected
            self.double_error_detected = self.dut.double_error_detected

    def _calculate_bit_position(self, k):
        """Calculate bit position for data bit k in encoded data"""
        pos = k + 1
        for j in range(self.PARITY_BITS):
            if pos >= (2 ** j):
                pos += 1
        return pos - 1

    def _get_covered_bits(self, parity_bit):
        """Get bit mask for bits covered by parity bit"""
        covered_bits = 0
        for j in range(self.TOTAL_WIDTH):
            if ((j + 1) >> parity_bit) & 1:
                covered_bits |= (1 << j)
        return covered_bits

    def _calculate_expected_encoding(self, data):
        """Calculate expected encoded data for verification"""
        data &= self.MAX_DATA
        encoded = 0

        # Insert data bits into correct positions
        for i in range(self.WIDTH):
            bit_pos = self._calculate_bit_position(i)
            if (data >> i) & 1:
                encoded |= (1 << bit_pos)

        # Calculate parity bits
        for i in range(self.PARITY_BITS):
            parity_pos = (2 ** i) - 1
            covered_bits = self._get_covered_bits(i)
            parity = 0

            for bit_index in range(self.TOTAL_WIDTH):
                if (covered_bits >> bit_index) & 1:
                    if (encoded >> bit_index) & 1:
                        parity ^= 1

            if parity:
                encoded |= (1 << parity_pos)

        # Calculate SECDED bit (overall parity)
        overall_parity = 0
        for i in range(self.TOTAL_WIDTH - 1):
            if (encoded >> i) & 1:
                overall_parity ^= 1

        if overall_parity:
            encoded |= (1 << (self.TOTAL_WIDTH - 1))

        return encoded & ((1 << self.TOTAL_WIDTH) - 1)

    async def reset_decoder(self):
        """Reset decoder (only for decoder module)"""
        if self.MODULE_TYPE == 'encoder':
            return

        self.log.debug(f'Starting reset_decoder{self.get_time_ns_str()}')

        self.enable.value = 0
        self.hamming_data.value = 0
        self.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 5)

        self.log.debug('Ending reset_decoder')

    async def test_encoder_basic(self):
        """Test basic encoder functionality"""
        if self.MODULE_TYPE == 'decoder':
            return True

        self.log.info("Testing encoder basic functionality")

        # Define test data based on level
        if self.TEST_LEVEL == 'basic':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
        elif self.TEST_LEVEL == 'medium':
            test_values = list(range(min(16, self.MAX_DATA + 1)))
            if self.MAX_DATA >= 16:
                test_values.extend([random.randint(0, self.MAX_DATA) for _ in range(16)])
        else:  # full
            if self.WIDTH <= 8:
                test_values = list(range(self.MAX_DATA + 1))  # All values
            else:
                test_values = list(range(256))  # First 256
                test_values.extend([random.randint(0, self.MAX_DATA) for _ in range(256)])

        all_passed = True

        for data in test_values:
            data &= self.MAX_DATA
            expected = self._calculate_expected_encoding(data)

            # Drive encoder input
            self.data.value = data
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay
            actual = int(self.encoded_data.value) & ((1 << self.TOTAL_WIDTH) - 1)

            success = (actual == expected)

            if success:
                self.log.debug(f"PASS: data=0x{data:x} → encoded=0x{actual:x}")
            else:
                self.log.error(f"FAIL: data=0x{data:x}, expected=0x{expected:x}, actual=0x{actual:x}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'encoder',
                'data': data,
                'expected': expected,
                'actual': actual,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_decoder_basic(self):
        """Test basic decoder functionality with no errors"""
        if self.MODULE_TYPE == 'encoder':
            return True

        self.log.info("Testing decoder basic functionality")
        await self.reset_decoder()

        # Define test data
        if self.TEST_LEVEL == 'basic':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
        elif self.TEST_LEVEL == 'medium':
            test_values = list(range(min(32, self.MAX_DATA + 1)))
        else:  # full
            if self.WIDTH <= 6:
                test_values = list(range(self.MAX_DATA + 1))
            else:
                test_values = list(range(min(128, self.MAX_DATA + 1)))
                test_values.extend([random.randint(0, self.MAX_DATA) for _ in range(128)])

        all_passed = True

        for data in test_values:
            data &= self.MAX_DATA
            # Encode the data first to get valid hamming code
            encoded = self._calculate_expected_encoding(data)

            # Test decoding
            success = await self._test_decode(encoded, data, False, False)
            if not success:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

        return all_passed

    async def test_single_bit_errors(self):
        """Test single-bit error detection and correction"""
        if self.MODULE_TYPE == 'encoder' or self.TEST_LEVEL == 'basic':
            self.log.info("Skipping single-bit error tests")
            return True

        self.log.info("Testing single-bit error detection and correction")
        await self.reset_decoder()

        # Test with known data patterns
        test_data_values = [0x5 & self.MAX_DATA, 0xA & self.MAX_DATA, self.MAX_DATA]

        all_passed = True

        for test_data in test_data_values:
            # Get clean encoded data
            clean_encoded = self._calculate_expected_encoding(test_data)

            # Test errors in different bit positions
            positions_to_test = range(self.TOTAL_WIDTH) if self.TEST_LEVEL == 'full' else range(min(8, self.TOTAL_WIDTH))

            for bit_pos in positions_to_test:
                # Introduce single-bit error
                corrupted_data = clean_encoded ^ (1 << bit_pos)

                self.log.debug(f"Testing single-bit error at position {bit_pos}")

                # Should detect error and correct to original data
                success = await self._test_decode(corrupted_data, test_data, True, False)
                if not success:
                    all_passed = False
                    if self.TEST_LEVEL == 'medium':
                        break

            if not all_passed and self.TEST_LEVEL == 'medium':
                break

        return all_passed

    async def test_double_bit_errors(self):
        """Test double-bit error detection"""
        if self.MODULE_TYPE == 'encoder' or self.TEST_LEVEL != 'full':
            self.log.info("Skipping double-bit error tests")
            return True

        self.log.info("Testing double-bit error detection")
        await self.reset_decoder()

        test_data = 0xA & self.MAX_DATA
        clean_encoded = self._calculate_expected_encoding(test_data)

        # Test a few double-bit error combinations
        test_combinations = [
            (0, 1), (0, 2), (1, 2), (0, self.TOTAL_WIDTH - 1),
            (self.TOTAL_WIDTH - 2, self.TOTAL_WIDTH - 1)
        ]

        valid_combinations = [(p1, p2) for p1, p2 in test_combinations
                            if p1 < self.TOTAL_WIDTH and p2 < self.TOTAL_WIDTH and p1 != p2]

        all_passed = True

        for pos1, pos2 in valid_combinations[:min(5, len(valid_combinations))]:
            # Introduce double-bit error
            corrupted_data = clean_encoded ^ (1 << pos1) ^ (1 << pos2)

            self.log.debug(f"Testing double-bit error at positions {pos1}, {pos2}")

            # Should detect double error (data may be wrong, but double_error should be set)
            success = await self._test_decode(corrupted_data, None, True, True)
            if not success:
                all_passed = False
                break

        return all_passed

    async def _test_decode(self, hamming_data, expected_data=None,
                            expected_error=False, expected_double_error=False):
        """Test decoding for decoder module"""
        hamming_data &= ((1 << self.TOTAL_WIDTH) - 1)

        self.hamming_data.value = hamming_data
        self.enable.value = 1
        await self.wait_clocks('clk', 1)

        actual_data = int(self.data.value) & self.MAX_DATA
        actual_error = bool(int(self.error_detected.value))
        actual_double_error = bool(int(self.double_error_detected.value))

        # Enhanced debugging for failures
        success = self._check_decode_results(hamming_data, expected_data, expected_error, expected_double_error,
                                            actual_data, actual_error, actual_double_error)

        # If this is a failure, dump detailed debug information
        if not success:
            await self._dump_debug_info(hamming_data, expected_data, expected_error, expected_double_error,
                                        actual_data, actual_error, actual_double_error)

        return success

    async def _dump_debug_info(self, hamming_data, expected_data, expected_error, expected_double_error,
                                actual_data, actual_error, actual_double_error):
        """Dump comprehensive debug information for failed test cases"""

        self.log.error("="*80)
        self.log.error("DETAILED FAILURE ANALYSIS")
        self.log.error("="*80)

        # Input information
        self.log.error(f"Input hamming_data: 0x{hamming_data:0{(self.TOTAL_WIDTH+3)//4}x} ({hamming_data:0{self.TOTAL_WIDTH}b})")

        # Expected vs Actual
        self.log.error(f"Expected: data=0x{expected_data:x}, error={expected_error}, double_error={expected_double_error}")
        self.log.error(f"Actual:   data=0x{actual_data:x}, error={actual_error}, double_error={actual_double_error}")

        # Calculate what we expect the RTL to compute
        expected_syndrome = self._calculate_expected_syndrome(hamming_data)
        expected_overall_parity = self._calculate_expected_overall_parity(hamming_data)
        expected_overall_parity_in = (hamming_data >> (self.TOTAL_WIDTH - 1)) & 1

        self.log.error(f"Expected syndrome calculation: 0x{expected_syndrome:x} ({expected_syndrome:0{self.PARITY_BITS}b})")
        self.log.error(f"Expected overall_parity: {expected_overall_parity}")
        self.log.error(f"Expected overall_parity_in: {expected_overall_parity_in}")

        # Try to read RTL internal signals if possible (this may not work in all simulators)
        try:
            # These might be accessible depending on the simulator
            if hasattr(self.dut, 'w_syndrome'):
                rtl_syndrome = int(self.dut.w_syndrome.value)
                self.log.error(f"RTL syndrome: 0x{rtl_syndrome:x} ({rtl_syndrome:0{self.PARITY_BITS}b})")

            if hasattr(self.dut, 'w_overall_parity'):
                rtl_overall_parity = int(self.dut.w_overall_parity.value)
                self.log.error(f"RTL overall_parity: {rtl_overall_parity}")

            if hasattr(self.dut, 'w_overall_parity_in'):
                rtl_overall_parity_in = int(self.dut.w_overall_parity_in.value)
                self.log.error(f"RTL overall_parity_in: {rtl_overall_parity_in}")

            if hasattr(self.dut, 'w_syndrome_0_based'):
                rtl_syndrome_0_based = int(self.dut.w_syndrome_0_based.value)
                self.log.error(f"RTL syndrome_0_based: {rtl_syndrome_0_based}")

        except Exception as e:
            self.log.error(f"Could not read RTL internal signals: {e}")

        # Bit-by-bit analysis
        self.log.error("Bit-by-bit breakdown:")
        for bit_pos in range(self.TOTAL_WIDTH):
            bit_val = (hamming_data >> bit_pos) & 1
            bit_type = self._get_bit_type(bit_pos)
            self.log.error(f"  Position {bit_pos:2d}: {bit_val} ({bit_type})")

        # Parity bit analysis
        self.log.error("Parity bit analysis:")
        for parity_bit in range(self.PARITY_BITS):
            parity_pos = (2 ** parity_bit) - 1
            covered_bits = self._get_covered_bits(parity_bit)
            calculated_parity = self._calculate_parity_for_bit(hamming_data, parity_bit)
            actual_parity = (hamming_data >> parity_pos) & 1

            self.log.error(f"  Parity bit {parity_bit} (pos {parity_pos}):")
            self.log.error(f"    Covers positions: {self._format_covered_positions(covered_bits)}")
            self.log.error(f"    Calculated parity: {calculated_parity}")
            self.log.error(f"    Actual parity: {actual_parity}")
            self.log.error(f"    Match: {calculated_parity == actual_parity}")

        # Data extraction analysis
        self.log.error("Data bit extraction:")
        for data_bit in range(self.WIDTH):
            bit_pos = self._calculate_bit_position(data_bit)
            expected_bit = (expected_data >> data_bit) & 1 if expected_data is not None else '?'
            actual_bit = (actual_data >> data_bit) & 1
            hamming_bit = (hamming_data >> bit_pos) & 1

            self.log.error(f"  Data bit {data_bit}: pos={bit_pos}, hamming_bit={hamming_bit}, " +
                            f"expected={expected_bit}, actual={actual_bit}")

        self.log.error("="*80)

    def _calculate_expected_syndrome(self, hamming_data):
        """Calculate what the syndrome should be"""
        syndrome = 0
        for parity_bit in range(self.PARITY_BITS):
            parity_pos = (2 ** parity_bit) - 1
            stored_parity = (hamming_data >> parity_pos) & 1
            calculated_parity = self._calculate_parity_for_bit(hamming_data, parity_bit)
            syndrome |= ((stored_parity ^ calculated_parity) << parity_bit)
        return syndrome

    def _calculate_expected_overall_parity(self, hamming_data):
        """Calculate expected overall parity (XOR of all bits except SECDED)"""
        parity = 0
        for i in range(self.TOTAL_WIDTH - 1):
            parity ^= (hamming_data >> i) & 1
        return parity

    def _calculate_parity_for_bit(self, hamming_data, parity_bit):
        """Calculate parity for a specific parity bit"""
        covered_bits = self._get_covered_bits(parity_bit)
        parity_pos = (2 ** parity_bit) - 1  # Position of this parity bit
        parity = 0
        for bit_pos in range(self.TOTAL_WIDTH):
            # FIXED: Exclude the parity bit itself from the calculation (match RTL behavior)
            if (covered_bits >> bit_pos) & 1 and bit_pos != parity_pos:
                parity ^= (hamming_data >> bit_pos) & 1
        return parity

    def _get_bit_type(self, position):
        """Get the type of bit at a given position"""
        if position == self.TOTAL_WIDTH - 1:
            return "SECDED"
        elif position == 0:
            return "P0"
        elif (position & (position - 1)) == 0:  # Power of 2
            return f"P{position.bit_length()-1}"
        else:
            return "DATA"

    def _format_covered_positions(self, covered_bits):
        """Format covered bit positions for display"""
        positions = []
        for bit_pos in range(self.TOTAL_WIDTH):
            if (covered_bits >> bit_pos) & 1:
                positions.append(str(bit_pos))
        return "[" + ",".join(positions) + "]"

    def _check_decode_results(self, hamming_data, expected_data, expected_error, expected_double_error,
                            actual_data, actual_error, actual_double_error):
        """Check decode results and log appropriately"""
        data_match = (expected_data is None) or (actual_data == expected_data)
        error_match = (actual_error == expected_error)
        double_error_match = (actual_double_error == expected_double_error)
        success = data_match and error_match and double_error_match

        if success:
            self.log.debug(f"PASS: hamming=0x{hamming_data:x} → data=0x{actual_data:x}, " +
                            f"err={actual_error}, derr={actual_double_error}")
        else:
            self.log.error(f"FAIL: hamming=0x{hamming_data:x}")
            if not data_match and expected_data is not None:
                self.log.error(f"  data: expected=0x{expected_data:x}, actual=0x{actual_data:x}")
            if not error_match:
                self.log.error(f"  error: expected={expected_error}, actual={actual_error}")
            if not double_error_match:
                self.log.error(f"  double_error: expected={expected_double_error}, actual={actual_double_error}")

        # Store result
        result = {
            'test_type': 'decoder',
            'hamming_data': hamming_data,
            'expected_data': expected_data,
            'actual_data': actual_data,
            'expected_error': expected_error,
            'actual_error': actual_error,
            'expected_double_error': expected_double_error,
            'actual_double_error': actual_double_error,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return success

    async def run_all_tests(self):
        """Run all appropriate tests based on module type and test level"""
        self.log.info(f"Running {self.MODULE_TYPE.upper()} tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions based on module type
        test_functions = []

        if self.MODULE_TYPE == 'encoder':
            test_functions.append((self.test_encoder_basic, "Encoder basic functionality"))

        elif self.MODULE_TYPE == 'decoder':
            test_functions.append((self.test_decoder_basic, "Decoder basic functionality"))
            test_functions.append((self.test_single_bit_errors, "Single-bit error correction"))
            test_functions.append((self.test_double_bit_errors, "Double-bit error detection"))

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
        self.log.info(f"Overall {self.MODULE_TYPE.upper()} result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def dataint_ecc_test(dut):
    """Unified test for Hamming ECC modules"""
    tb = HammingECCTB(dut)

    # Start clock if needed (for decoder module)
    if tb.MODULE_TYPE == 'decoder':
        await tb.start_clock('clk', 10, 'ns')

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"{tb.MODULE_TYPE.upper()} test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Hamming ECC {tb.MODULE_TYPE} test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4-bit, both modules, basic)
    REG_LEVEL=FUNC: 6 tests (all widths, both modules, basic) - default
    REG_LEVEL=FULL: 18 tests (all combinations)

    Returns:
        List of tuples: (data_width, module_type, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [4, 8, 16]  # Different data widths
    modules = ['encoder', 'decoder']  # Module types
    test_levels = ['basic', 'medium', 'full']

    if reg_level == 'GATE':
        # Quick smoke test: 4-bit, both modules, basic level
        return [(4, 'encoder', 'basic'), (4, 'decoder', 'basic')]

    elif reg_level == 'FUNC':
        # Functional coverage: all widths, both modules, basic level only
        return list(product(widths, modules, ['basic']))

    else:  # FULL
        # Comprehensive: all combinations
        return list(product(widths, modules, test_levels))

params = generate_params()

@pytest.mark.parametrize("data_width, module_type, test_level", params)
def test_dataint_ecc(request, data_width, module_type, test_level):
    """
    Parameterized Hamming ECC test with configurable module type and test level.

    Module type controls which DUT is compiled and tested:
    - encoder: Test only the encoder module (combinational)
    - decoder: Test only the decoder module (sequential)

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # Select DUT and sources based on module_type
    if module_type == 'encoder':
        dut_name = "dataint_ecc_hamming_encode_secded"
        # Get verilog sources and includes from filelist
        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='rtl/common/filelists/dataint_ecc_hamming_encode_secded.f'
        )
    else:  # decoder
        dut_name = "dataint_ecc_hamming_decode_secded"
        # Get verilog sources and includes from filelist
        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='rtl/common/filelists/dataint_ecc_hamming_decode_secded.f'
        )

    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_hamming_{module_type}_w{w_str}_{test_level}_{reg_level}"

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
        'DEBUG': '1'  # Always enable debug for better failure analysis
    }

    # Adjust timeout based on test level and data width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, data_width / 8.0)  # Larger widths take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

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
        'TEST_MODULE': module_type,
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
    print(f"Running {test_level.upper()} test: {module_type} module, width={data_width}")
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
        print(f"✓ {test_level.upper()} test PASSED: {module_type} module")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
