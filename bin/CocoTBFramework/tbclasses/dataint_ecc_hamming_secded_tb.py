# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DataintEccHammingSecDedTB
# Purpose: Testbench for dataint_ecc_hamming_encode_secded and dataint_ecc_hamming_decode_s
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Testbench for dataint_ecc_hamming_encode_secded and dataint_ecc_hamming_decode_secded modules

The Hamming SECDED (Single Error Correction, Double Error Detection) implementation
provides data integrity for memory and communication systems. It combines:
- Hamming code for single-bit error correction
- Extra parity bit for double-bit error detection

Key Features Tested:
- Encode/decode round-trip with no errors
- Single-bit error correction
- Double-bit error detection
- All bit positions (data, parity, SECDED)
- Multiple data widths (4, 8, 16, 32, 64 bits)

Author: RTL Design Sherpa Project
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
import os
import random


class DataintEccHammingSecDedTB(TBBase):
    """Testbench for dataint_ecc_hamming SECDED encoder/decoder pair"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get parameters from environment
        self.WIDTH = self.convert_to_int(os.environ.get('PARAM_WIDTH', '8'))

        # Calculate ECC parameters (must match RTL)
        import math
        self.PARITY_BITS = math.ceil(math.log2(self.WIDTH + math.ceil(math.log2(self.WIDTH + math.ceil(math.log2(self.WIDTH + 1)))) + 1))
        self.TOTAL_WIDTH = self.WIDTH + self.PARITY_BITS + 1  # +1 for SECDED bit

        self.log.info(f"ECC SECDED TB initialized: WIDTH={self.WIDTH}, PARITY_BITS={self.PARITY_BITS}, TOTAL_WIDTH={self.TOTAL_WIDTH}")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset"""
        # Decoder is sequential, encoder is combinational
        await self.start_clock('clk', freq=10, units='ns')

        # Initialize decoder inputs
        self.dut.enable.value = 0
        self.dut.hamming_data.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 3)

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.rst_n.value = 1

    def inject_single_bit_error(self, encoded_data, bit_pos):
        """Inject a single-bit error at the specified position"""
        return encoded_data ^ (1 << bit_pos)

    def inject_double_bit_error(self, encoded_data, bit_pos1, bit_pos2):
        """Inject double-bit errors at two positions"""
        return encoded_data ^ (1 << bit_pos1) ^ (1 << bit_pos2)

    async def encode_decode_test(self, data_value):
        """Encode data, decode it, and verify correctness"""
        # Drive encoder input (combinational)
        self.dut.data.value = data_value

        # Wait for combinational propagation
        await Timer(1, units='ns')

        # Read encoded data
        encoded_value = int(self.dut.encoded_data.value)

        # Drive decoder input
        self.dut.hamming_data.value = encoded_value
        self.dut.enable.value = 1

        # Wait for decoder to process (sequential)
        await RisingEdge(self.dut.clk)
        await RisingEdge(self.dut.clk)  # Extra cycle for output

        # Read decoded data
        decoded_value = int(self.dut.decoded_data.value)
        error_detected = int(self.dut.error_detected.value)
        double_error = int(self.dut.double_error_detected.value)

        return encoded_value, decoded_value, error_detected, double_error

    async def test_no_errors(self):
        """Test encode/decode round-trip with no errors"""
        self.log.info("=== Test: No Errors (Round-Trip) ===")

        all_passed = True
        test_patterns = [
            0x00,  # All zeros
            (1 << self.WIDTH) - 1,  # All ones
            0xAA & ((1 << self.WIDTH) - 1),  # Alternating 10101010
            0x55 & ((1 << self.WIDTH) - 1),  # Alternating 01010101
        ]

        # Add random patterns
        for _ in range(5):
            test_patterns.append(random.randint(0, (1 << self.WIDTH) - 1))

        for data in test_patterns:
            encoded, decoded, error_det, double_err = await self.encode_decode_test(data)

            if decoded != data:
                self.log.error(f"  FAIL: data=0x{data:X} → encoded=0x{encoded:X} → decoded=0x{decoded:X} (mismatch!)")
                all_passed = False
            elif error_det != 0:
                self.log.error(f"  FAIL: data=0x{data:X} → error_detected={error_det} (should be 0)")
                all_passed = False
            elif double_err != 0:
                self.log.error(f"  FAIL: data=0x{data:X} → double_error={double_err} (should be 0)")
                all_passed = False
            else:
                self.log.debug(f"  PASS: 0x{data:X} → 0x{encoded:X} → 0x{decoded:X}")

        if all_passed:
            self.log.info("✓ No errors test passed")

        return all_passed

    async def test_single_bit_correction(self):
        """Test single-bit error detection and correction"""
        self.log.info("=== Test: Single-Bit Error Correction ===")

        all_passed = True
        test_data = random.randint(0, (1 << self.WIDTH) - 1)

        # Encode clean data
        self.dut.data.value = test_data
        await Timer(1, units='ns')
        clean_encoded = int(self.dut.encoded_data.value)

        # Test error injection at each bit position
        error_count = 0
        for bit_pos in range(self.TOTAL_WIDTH):
            corrupted = self.inject_single_bit_error(clean_encoded, bit_pos)

            # Decode corrupted data
            self.dut.hamming_data.value = corrupted
            self.dut.enable.value = 1
            await RisingEdge(self.dut.clk)
            await RisingEdge(self.dut.clk)

            decoded = int(self.dut.decoded_data.value)
            error_det = int(self.dut.error_detected.value)
            double_err = int(self.dut.double_error_detected.value)

            if decoded != test_data:
                self.log.error(f"  FAIL: Bit {bit_pos} error - decoded=0x{decoded:X}, expected=0x{test_data:X}")
                all_passed = False
                error_count += 1
            elif error_det != 1:
                self.log.error(f"  FAIL: Bit {bit_pos} error - error_detected={error_det} (should be 1)")
                all_passed = False
                error_count += 1
            elif double_err != 0:
                self.log.error(f"  FAIL: Bit {bit_pos} error - double_error={double_err} (should be 0)")
                all_passed = False
                error_count += 1
            else:
                self.log.debug(f"  PASS: Bit {bit_pos} error corrected (0x{test_data:X})")

        if all_passed:
            self.log.info(f"✓ Single-bit correction test passed ({self.TOTAL_WIDTH} bit positions)")
        else:
            self.log.error(f"✗ Single-bit correction failed ({error_count} errors)")

        return all_passed

    async def test_double_bit_detection(self):
        """Test double-bit error detection (no correction)"""
        self.log.info("=== Test: Double-Bit Error Detection ===")

        all_passed = True
        test_data = random.randint(0, (1 << self.WIDTH) - 1)

        # Encode clean data
        self.dut.data.value = test_data
        await Timer(1, units='ns')
        clean_encoded = int(self.dut.encoded_data.value)

        # Test a few double-bit error combinations
        test_pairs = [
            (0, 1), (0, self.TOTAL_WIDTH-1),
            (1, 2), (self.TOTAL_WIDTH//2, self.TOTAL_WIDTH//2 + 1)
        ]

        for bit_pos1, bit_pos2 in test_pairs:
            if bit_pos2 >= self.TOTAL_WIDTH:
                continue

            corrupted = self.inject_double_bit_error(clean_encoded, bit_pos1, bit_pos2)

            # Decode corrupted data
            self.dut.hamming_data.value = corrupted
            self.dut.enable.value = 1
            await RisingEdge(self.dut.clk)
            await RisingEdge(self.dut.clk)

            error_det = int(self.dut.error_detected.value)
            double_err = int(self.dut.double_error_detected.value)

            if error_det != 1:
                self.log.error(f"  FAIL: Bits {bit_pos1},{bit_pos2} - error_detected={error_det} (should be 1)")
                all_passed = False
            elif double_err != 1:
                self.log.error(f"  FAIL: Bits {bit_pos1},{bit_pos2} - double_error={double_err} (should be 1)")
                all_passed = False
            else:
                self.log.debug(f"  PASS: Bits {bit_pos1},{bit_pos2} double error detected")

        if all_passed:
            self.log.info(f"✓ Double-bit detection test passed ({len(test_pairs)} combinations)")

        return all_passed

    async def test_all_data_patterns(self):
        """Test with exhaustive data patterns (small widths only)"""
        if self.WIDTH > 8:
            self.log.info("=== Test: All Data Patterns (skipped for WIDTH > 8) ===")
            return True

        self.log.info(f"=== Test: All {2**self.WIDTH} Data Patterns ===")

        all_passed = True
        for data in range(2**self.WIDTH):
            encoded, decoded, error_det, double_err = await self.encode_decode_test(data)

            if decoded != data or error_det != 0 or double_err != 0:
                self.log.error(f"  FAIL: Pattern 0x{data:X} failed")
                all_passed = False

        if all_passed:
            self.log.info(f"✓ All {2**self.WIDTH} patterns passed")

        return all_passed

    async def run_all_tests(self):
        """Run all test scenarios"""
        results = []

        # Test 1: No errors (round-trip)
        passed = await self.test_no_errors()
        results.append(("No Errors (Round-Trip)", passed))

        # Test 2: Single-bit error correction
        passed = await self.test_single_bit_correction()
        results.append(("Single-Bit Error Correction", passed))

        # Test 3: Double-bit error detection
        passed = await self.test_double_bit_detection()
        results.append(("Double-Bit Error Detection", passed))

        # Test 4: All data patterns (small widths)
        passed = await self.test_all_data_patterns()
        results.append(("All Data Patterns", passed))

        # Summary
        self.log.info("=" * 60)
        self.log.info("Test Summary:")
        for name, passed in results:
            status = "✓ PASSED" if passed else "✗ FAILED"
            self.log.info(f"  {name}: {status}")
        self.log.info("=" * 60)

        return all(result[1] for result in results)
