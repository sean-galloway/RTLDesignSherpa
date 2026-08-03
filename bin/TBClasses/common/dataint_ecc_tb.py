# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: HammingECCTB
# Purpose: Testbench for dataint_ecc
# Subsystem: framework
#
# Extracted from val/common/test_dataint_ecc.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import math
import cocotb
from TBClasses.shared.tbbase import TBBase


class HammingECCTB(TBBase):
    """Unified testbench for Hamming ECC modules"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
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
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Hamming ECC TB initialized - Module: {self.MODULE_TYPE.upper()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}, WIDTH={self.WIDTH}")
        self.log.info(f"PARITY_BITS={self.PARITY_BITS}, TOTAL_WIDTH={self.TOTAL_WIDTH}")

        # Initialize signal mappings based on module type
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
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

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
        if self.TEST_LEVEL == 'gate':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
            test_values = [0, 1, self.MAX_DATA >> 1, self.MAX_DATA]
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
                    break

        return all_passed

    async def test_single_bit_errors(self):
        """Test single-bit error detection and correction"""
        if self.MODULE_TYPE == 'encoder' or self.TEST_LEVEL == 'gate':
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
                    if self.TEST_LEVEL == 'func':
                        break

            if not all_passed and self.TEST_LEVEL == 'func':
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
