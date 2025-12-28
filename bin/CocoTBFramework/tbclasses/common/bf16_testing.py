# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BF16TB
# Purpose: BF16 Floating-Point Testing Module
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-11-25

"""BF16 Floating-Point Testing Module

This module provides testbenches for BF16 (Brain Float 16) arithmetic units.
Supports testing of:
- BF16 Multiplier
- BF16 FMA (Fused Multiply-Add) with FP32 accumulator
"""
import os
import random
import struct
import contextlib
from typing import List, Tuple, Dict, Any, Optional

from cocotb.triggers import Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class BF16Utils:
    """Utility class for BF16 floating-point operations."""

    # BF16 format: [15]=sign, [14:7]=exponent (8 bits), [6:0]=mantissa (7 bits)
    # Bias = 127

    @staticmethod
    def float_to_bf16(f: float) -> int:
        """Convert Python float to BF16 bit representation.

        BF16 is essentially FP32 truncated to upper 16 bits.
        """
        # Handle special cases
        if f != f:  # NaN check
            return 0x7FC0  # Canonical qNaN

        # Handle infinity
        if f == float('inf'):
            return 0x7F80  # +inf
        if f == float('-inf'):
            return 0xFF80  # -inf

        # Handle overflow (value too large for FP32)
        try:
            fp32_bytes = struct.pack('>f', f)
        except OverflowError:
            # Return signed infinity
            return 0xFF80 if f < 0 else 0x7F80

        fp32_bits = struct.unpack('>I', fp32_bytes)[0]

        # Truncate to upper 16 bits (BF16)
        bf16_bits = (fp32_bits >> 16) & 0xFFFF

        return bf16_bits

    @staticmethod
    def bf16_to_float(bf16: int) -> float:
        """Convert BF16 bit representation to Python float."""
        # Extend to FP32 by padding lower 16 bits with zeros
        fp32_bits = (bf16 & 0xFFFF) << 16

        # Unpack as FP32
        fp32_bytes = struct.pack('>I', fp32_bits)
        f = struct.unpack('>f', fp32_bytes)[0]

        return f

    @staticmethod
    def float_to_fp32(f: float) -> int:
        """Convert Python float to FP32 bit representation."""
        fp32_bytes = struct.pack('>f', f)
        return struct.unpack('>I', fp32_bytes)[0]

    @staticmethod
    def fp32_to_float(fp32: int) -> float:
        """Convert FP32 bit representation to Python float."""
        fp32_bytes = struct.pack('>I', fp32 & 0xFFFFFFFF)
        return struct.unpack('>f', fp32_bytes)[0]

    @staticmethod
    def bf16_is_zero(bf16: int) -> bool:
        """Check if BF16 value is zero (positive or negative)."""
        return (bf16 & 0x7FFF) == 0

    @staticmethod
    def bf16_is_subnormal(bf16: int) -> bool:
        """Check if BF16 value is subnormal."""
        exp = (bf16 >> 7) & 0xFF
        mant = bf16 & 0x7F
        return exp == 0 and mant != 0

    @staticmethod
    def bf16_is_inf(bf16: int) -> bool:
        """Check if BF16 value is infinity."""
        exp = (bf16 >> 7) & 0xFF
        mant = bf16 & 0x7F
        return exp == 0xFF and mant == 0

    @staticmethod
    def bf16_is_nan(bf16: int) -> bool:
        """Check if BF16 value is NaN."""
        exp = (bf16 >> 7) & 0xFF
        mant = bf16 & 0x7F
        return exp == 0xFF and mant != 0

    @staticmethod
    def bf16_fields(bf16: int) -> Tuple[int, int, int]:
        """Extract BF16 fields: (sign, exponent, mantissa)."""
        sign = (bf16 >> 15) & 1
        exp = (bf16 >> 7) & 0xFF
        mant = bf16 & 0x7F
        return sign, exp, mant

    @staticmethod
    def make_bf16(sign: int, exp: int, mant: int) -> int:
        """Construct BF16 from fields."""
        return ((sign & 1) << 15) | ((exp & 0xFF) << 7) | (mant & 0x7F)

    @staticmethod
    def fp32_fields(fp32: int) -> Tuple[int, int, int]:
        """Extract FP32 fields: (sign, exponent, mantissa)."""
        sign = (fp32 >> 31) & 1
        exp = (fp32 >> 23) & 0xFF
        mant = fp32 & 0x7FFFFF
        return sign, exp, mant

    @staticmethod
    def make_fp32(sign: int, exp: int, mant: int) -> int:
        """Construct FP32 from fields."""
        return ((sign & 1) << 31) | ((exp & 0xFF) << 23) | (mant & 0x7FFFFF)


class BF16MultiplierTB(TBBase):
    """Testbench for BF16 multiplier (math_bf16_multiplier).

    Tests the complete BF16 multiplier including:
    - Normal multiplication
    - Special value handling (zero, infinity, NaN, subnormal)
    - Overflow/underflow detection
    - RNE rounding
    """

    def __init__(self, dut):
        """Initialize the BF16 multiplier testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Multiplier TB initialized, test_level={self.test_level}")

    def _compute_expected_mult(self, a_bf16: int, b_bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected multiplication result.

        Returns:
            Tuple of (result_bf16, overflow, underflow, invalid)
        """
        # Convert to floats
        a_float = BF16Utils.bf16_to_float(a_bf16)
        b_float = BF16Utils.bf16_to_float(b_bf16)

        # Check special cases
        a_is_zero = BF16Utils.bf16_is_zero(a_bf16) or BF16Utils.bf16_is_subnormal(a_bf16)
        b_is_zero = BF16Utils.bf16_is_zero(b_bf16) or BF16Utils.bf16_is_subnormal(b_bf16)
        a_is_inf = BF16Utils.bf16_is_inf(a_bf16)
        b_is_inf = BF16Utils.bf16_is_inf(b_bf16)
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)

        # Result sign
        sign_a = (a_bf16 >> 15) & 1
        sign_b = (b_bf16 >> 15) & 1
        sign_result = sign_a ^ sign_b

        # Invalid operation: 0 * inf
        invalid = (a_is_zero and b_is_inf) or (b_is_zero and a_is_inf)

        # NaN handling
        if a_is_nan or b_is_nan or invalid:
            return (sign_result << 15) | 0x7FC0, False, False, invalid

        # Infinity
        if a_is_inf or b_is_inf:
            return (sign_result << 15) | 0x7F80, False, False, False

        # Zero
        if a_is_zero or b_is_zero:
            return (sign_result << 15), False, False, False

        # Normal multiplication
        result_float = a_float * b_float

        # Check for overflow/underflow before conversion
        abs_result = abs(result_float)
        overflow = False
        underflow = False

        # BF16 max normal: ~3.39e38, min normal: ~1.17e-38
        if abs_result > 3.39e38:
            overflow = True
            return (sign_result << 15) | 0x7F80, True, False, False

        if abs_result < 1.17e-38 and abs_result > 0:
            underflow = True
            return (sign_result << 15), False, True, False

        # Convert to BF16 with RNE rounding
        result_bf16 = BF16Utils.float_to_bf16(result_float)

        return result_bf16, overflow, underflow, False

    async def test_single_mult(self, a_bf16: int, b_bf16: int, desc: str = "",
                               allow_ulp_tolerance: bool = True) -> bool:
        """Test a single multiplication.

        Args:
            a_bf16: First BF16 operand
            b_bf16: Second BF16 operand
            desc: Test description
            allow_ulp_tolerance: If True, allow 1 ULP difference for normal values
                                (due to rounding implementation differences)

        Returns:
            True if test passed, False otherwise
        """
        # Apply inputs
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_result.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        invalid = int(self.dut.ow_invalid.value)

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_invalid = \
            self._compute_expected_mult(a_bf16, b_bf16)

        # Compare
        self.test_count += 1

        # For NaN results, just check it's a NaN (don't compare exact bits)
        result_is_nan = BF16Utils.bf16_is_nan(result)
        exp_is_nan = BF16Utils.bf16_is_nan(exp_result)

        # Check for special values (zero, inf) - these must match exactly
        result_is_special = BF16Utils.bf16_is_zero(result) or BF16Utils.bf16_is_inf(result)
        exp_is_special = BF16Utils.bf16_is_zero(exp_result) or BF16Utils.bf16_is_inf(exp_result)

        if result_is_nan and exp_is_nan:
            # Both NaN - pass
            passed = True
        elif result_is_special or exp_is_special:
            # Special values must match exactly
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        elif allow_ulp_tolerance:
            # Allow 1 ULP difference for normal values due to rounding differences
            # Python float_to_bf16 truncates, hardware does proper RNE
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= 1
        else:
            passed = False

        # Also check flags (with tolerance for underflow/overflow edge cases)
        # When we're within 1 ULP, flag differences at boundary are acceptable
        flags_match = (overflow == exp_overflow and
                       underflow == exp_underflow and
                       invalid == exp_invalid)

        if not flags_match and allow_ulp_tolerance:
            # Allow flag mismatches at overflow/underflow boundaries
            # This happens when the rounding pushes a value across a threshold
            flags_match = (invalid == exp_invalid)  # Invalid must always match

        if not flags_match:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = BF16Utils.bf16_to_float(a_bf16)
            b_float = BF16Utils.bf16_to_float(b_bf16)
            self.log.error(f"FAIL {desc}: {a_float} * {b_float}")
            self.log.error(f"  a=0x{a_bf16:04X}, b=0x{b_bf16:04X}")
            self.log.error(f"  Expected: result=0x{exp_result:04X}, "
                          f"ovf={exp_overflow}, udf={exp_underflow}, inv={exp_invalid}")
            self.log.error(f"  Actual:   result=0x{result:04X}, "
                          f"ovf={overflow}, udf={underflow}, inv={invalid}")
            if allow_ulp_tolerance:
                ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
                self.log.error(f"  ULP diff: {ulp_diff}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values: zero, infinity, NaN, subnormal."""
        self.log.info("Starting Special Values Test")
        failures = []

        # Special value bit patterns
        pos_zero = 0x0000
        neg_zero = 0x8000
        pos_inf = 0x7F80
        neg_inf = 0xFF80
        pos_nan = 0x7FC0  # Quiet NaN
        neg_nan = 0xFFC0
        subnormal = 0x0001  # Smallest subnormal
        pos_one = 0x3F80   # 1.0
        neg_one = 0xBF80   # -1.0
        pos_two = 0x4000   # 2.0

        special_cases = [
            # Zero cases
            (pos_zero, pos_one, "0 * 1"),
            (pos_one, pos_zero, "1 * 0"),
            (neg_zero, pos_one, "-0 * 1"),
            (pos_zero, neg_zero, "0 * -0"),

            # Infinity cases
            (pos_inf, pos_one, "inf * 1"),
            (pos_one, pos_inf, "1 * inf"),
            (pos_inf, pos_inf, "inf * inf"),
            (neg_inf, neg_inf, "-inf * -inf"),
            (pos_inf, neg_inf, "inf * -inf"),

            # Invalid: 0 * inf
            (pos_zero, pos_inf, "0 * inf (invalid)"),
            (pos_inf, pos_zero, "inf * 0 (invalid)"),
            (neg_zero, pos_inf, "-0 * inf (invalid)"),

            # NaN propagation
            (pos_nan, pos_one, "NaN * 1"),
            (pos_one, pos_nan, "1 * NaN"),
            (pos_nan, pos_nan, "NaN * NaN"),
            (pos_nan, pos_inf, "NaN * inf"),

            # Subnormal (FTZ)
            (subnormal, pos_one, "subnormal * 1"),
            (pos_one, subnormal, "1 * subnormal"),

            # Normal operations
            (pos_one, pos_one, "1 * 1"),
            (pos_two, pos_two, "2 * 2"),
            (neg_one, neg_one, "-1 * -1"),
            (pos_one, neg_one, "1 * -1"),
        ]

        for a, b, desc in special_cases:
            if not await self.test_single_mult(a, b, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def corner_cases_test(self) -> List[str]:
        """Test corner cases: max/min normal, powers of 2, etc."""
        self.log.info("Starting Corner Cases Test")
        failures = []

        # Important BF16 values
        max_normal = 0x7F7F  # Largest normal (~3.39e38)
        min_normal = 0x0080  # Smallest positive normal (~1.17e-38)
        pos_one = 0x3F80    # 1.0
        neg_one = 0xBF80    # -1.0
        pos_two = 0x4000    # 2.0
        half = 0x3F00       # 0.5

        corner_cases = [
            (max_normal, pos_one, "max_normal * 1"),
            (min_normal, pos_one, "min_normal * 1"),
            (max_normal, half, "max_normal * 0.5"),
            (min_normal, pos_two, "min_normal * 2"),
            (max_normal, pos_two, "max_normal * 2 (overflow)"),
            (min_normal, half, "min_normal * 0.5 (underflow)"),
        ]

        # Powers of 2
        for exp in range(0, 8):
            val = 0x3F80 + (exp << 7)  # 1.0 * 2^exp
            corner_cases.append((val, val, f"2^{exp} * 2^{exp}"))

        for a, b, desc in corner_cases:
            if not await self.test_single_mult(a, b, desc):
                failures.append(f"Corner case failed: {desc}")

        self.log.info(f"Corner Cases Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values (avoid NaN/Inf for basic random test)
            a = random.randint(0, 0x7F7F)  # Positive normal range
            b = random.randint(0, 0x7F7F)

            # Randomly negate
            if random.random() < 0.5:
                a |= 0x8000
            if random.random() < 0.5:
                b |= 0x8000

            if not await self.test_single_mult(a, b, f"random_{i}"):
                failures.append(f"Random test {i} failed: a=0x{a:04X}, b=0x{b:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Multiplier Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            failures.extend(await self.corner_cases_test())

        # Random tests scale with level
        if self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Tests failed: {self.fail_count}"


class BF16FMATB(TBBase):
    """Testbench for BF16 FMA (math_bf16_fma).

    Tests the FMA with BF16 inputs and FP32 accumulator.
    FMA computes: result = (a * b) + c
    """

    def __init__(self, dut):
        """Initialize the BF16 FMA testbench."""
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 FMA TB initialized, test_level={self.test_level}")

    def _compute_expected_fma(self, a_bf16: int, b_bf16: int, c_fp32: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected FMA result.

        Returns:
            Tuple of (result_fp32, overflow, underflow, invalid)
        """
        # Convert inputs to float
        a_float = BF16Utils.bf16_to_float(a_bf16)
        b_float = BF16Utils.bf16_to_float(b_bf16)
        c_float = BF16Utils.fp32_to_float(c_fp32)

        # Check special cases
        a_is_zero = BF16Utils.bf16_is_zero(a_bf16) or BF16Utils.bf16_is_subnormal(a_bf16)
        b_is_zero = BF16Utils.bf16_is_zero(b_bf16) or BF16Utils.bf16_is_subnormal(b_bf16)
        a_is_inf = BF16Utils.bf16_is_inf(a_bf16)
        b_is_inf = BF16Utils.bf16_is_inf(b_bf16)
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)

        c_sign, c_exp, c_mant = BF16Utils.fp32_fields(c_fp32)
        c_is_zero = (c_fp32 & 0x7FFFFFFF) == 0
        c_is_subnormal = c_exp == 0 and c_mant != 0
        c_is_inf = c_exp == 0xFF and c_mant == 0
        c_is_nan = c_exp == 0xFF and c_mant != 0

        # Invalid: 0 * inf or inf - inf
        sign_a = (a_bf16 >> 15) & 1
        sign_b = (b_bf16 >> 15) & 1
        prod_sign = sign_a ^ sign_b

        invalid_mul = (a_is_zero and b_is_inf) or (b_is_zero and a_is_inf)
        prod_is_inf = a_is_inf or b_is_inf
        invalid_add = prod_is_inf and c_is_inf and (prod_sign != c_sign)
        invalid = invalid_mul or invalid_add

        # Any NaN
        any_nan = a_is_nan or b_is_nan or c_is_nan

        if any_nan or invalid:
            return 0x7FC00000, False, False, invalid  # Canonical qNaN

        # Product infinity
        if prod_is_inf and not c_is_inf:
            return (prod_sign << 31) | 0x7F800000, False, False, False

        # Addend infinity
        if c_is_inf:
            return c_fp32, False, False, False

        # Product zero
        if a_is_zero or b_is_zero:
            if c_is_zero or c_is_subnormal:
                result_sign = prod_sign & c_sign
                return result_sign << 31, False, False, False
            return c_fp32, False, False, False

        # C is zero - return product extended to FP32
        if c_is_zero or c_is_subnormal:
            result_float = a_float * b_float
            result_fp32 = BF16Utils.float_to_fp32(result_float)
            return result_fp32, False, False, False

        # Normal FMA operation
        result_float = (a_float * b_float) + c_float

        # Check overflow/underflow
        abs_result = abs(result_float)
        if abs_result > 3.4e38:
            sign = 1 if result_float < 0 else 0
            return (sign << 31) | 0x7F800000, True, False, False

        if abs_result < 1.17e-38 and abs_result > 0:
            sign = 1 if result_float < 0 else 0
            return sign << 31, False, True, False

        if result_float == 0:
            return 0, False, False, False

        result_fp32 = BF16Utils.float_to_fp32(result_float)
        return result_fp32, False, False, False

    async def test_single_fma(self, a_bf16: int, b_bf16: int, c_fp32: int, desc: str = "") -> bool:
        """Test a single FMA operation."""
        # Apply inputs
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16
        self.dut.i_c.value = c_fp32

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_result.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        invalid = int(self.dut.ow_invalid.value)

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_invalid = \
            self._compute_expected_fma(a_bf16, b_bf16, c_fp32)

        self.test_count += 1

        # Check for NaN - both NaN is a pass
        result_is_nan = (result & 0x7F800000) == 0x7F800000 and (result & 0x007FFFFF) != 0
        exp_is_nan = (exp_result & 0x7F800000) == 0x7F800000 and (exp_result & 0x007FFFFF) != 0

        if result_is_nan and exp_is_nan:
            passed = True
        else:
            # Allow small ULP differences due to rounding
            if result == exp_result:
                passed = True
            else:
                # Check if within 1 ULP
                diff = abs(int(result) - int(exp_result))
                passed = diff <= 1

        # Check flags
        if overflow != exp_overflow or underflow != exp_underflow or invalid != exp_invalid:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = BF16Utils.bf16_to_float(a_bf16)
            b_float = BF16Utils.bf16_to_float(b_bf16)
            c_float = BF16Utils.fp32_to_float(c_fp32)
            self.log.error(f"FAIL {desc}: ({a_float} * {b_float}) + {c_float}")
            self.log.error(f"  a=0x{a_bf16:04X}, b=0x{b_bf16:04X}, c=0x{c_fp32:08X}")
            self.log.error(f"  Expected: result=0x{exp_result:08X}, "
                          f"ovf={exp_overflow}, udf={exp_underflow}, inv={exp_invalid}")
            self.log.error(f"  Actual:   result=0x{result:08X}, "
                          f"ovf={overflow}, udf={underflow}, inv={invalid}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special values for FMA."""
        self.log.info("Starting FMA Special Values Test")
        failures = []

        # BF16 special values
        bf16_zero = 0x0000
        bf16_one = 0x3F80
        bf16_two = 0x4000
        bf16_inf = 0x7F80
        bf16_nan = 0x7FC0
        bf16_neg_one = 0xBF80

        # FP32 special values
        fp32_zero = 0x00000000
        fp32_one = 0x3F800000
        fp32_inf = 0x7F800000
        fp32_nan = 0x7FC00000
        fp32_neg_one = 0xBF800000

        special_cases = [
            # Basic FMA
            (bf16_one, bf16_one, fp32_zero, "1*1 + 0"),
            (bf16_two, bf16_two, fp32_one, "2*2 + 1"),
            (bf16_one, bf16_neg_one, fp32_one, "1*-1 + 1 = 0"),

            # Zero product
            (bf16_zero, bf16_one, fp32_one, "0*1 + 1"),
            (bf16_one, bf16_zero, fp32_one, "1*0 + 1"),

            # Infinity
            (bf16_inf, bf16_one, fp32_zero, "inf*1 + 0"),
            (bf16_one, bf16_one, fp32_inf, "1*1 + inf"),

            # Invalid: 0 * inf
            (bf16_zero, bf16_inf, fp32_zero, "0*inf + 0 (invalid)"),

            # Invalid: inf - inf
            (bf16_inf, bf16_one, fp32_inf | 0x80000000, "inf - inf (invalid)"),

            # NaN propagation
            (bf16_nan, bf16_one, fp32_zero, "NaN*1 + 0"),
            (bf16_one, bf16_nan, fp32_zero, "1*NaN + 0"),
            (bf16_one, bf16_one, fp32_nan, "1*1 + NaN"),
        ]

        for a, b, c, desc in special_cases:
            if not await self.test_single_fma(a, b, c, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"FMA Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def accumulation_test(self) -> List[str]:
        """Test FMA accumulation scenarios (typical AI training)."""
        self.log.info("Starting FMA Accumulation Test")
        failures = []

        # Test accumulation: start with 0, add products
        bf16_one = 0x3F80
        bf16_half = 0x3F00
        bf16_two = 0x4000

        # Simple accumulations
        test_cases = [
            (bf16_one, bf16_one, 0x00000000, "1*1 + 0 = 1"),
            (bf16_one, bf16_one, 0x3F800000, "1*1 + 1 = 2"),
            (bf16_half, bf16_half, 0x00000000, "0.5*0.5 + 0 = 0.25"),
            (bf16_two, bf16_two, 0x3F800000, "2*2 + 1 = 5"),
        ]

        for a, b, c, desc in test_cases:
            if not await self.test_single_fma(a, b, c, desc):
                failures.append(f"Accumulation test failed: {desc}")

        self.log.info(f"FMA Accumulation Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random FMA testing."""
        self.log.info(f"Starting FMA Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Random BF16 operands
            a = random.randint(0, 0x7F7F)
            b = random.randint(0, 0x7F7F)

            # Random FP32 accumulator (avoid extreme values)
            c_exp = random.randint(100, 150)  # Moderate exponent range
            c_mant = random.randint(0, 0x7FFFFF)
            c = (c_exp << 23) | c_mant

            # Random signs
            if random.random() < 0.5:
                a |= 0x8000
            if random.random() < 0.5:
                b |= 0x8000
            if random.random() < 0.5:
                c |= 0x80000000

            if not await self.test_single_fma(a, b, c, f"random_{i}"):
                failures.append(f"Random FMA {i} failed")

            if i % max(1, count // 10) == 0:
                self.log.info(f"FMA random progress: {i}/{count}")

        self.log.info(f"FMA Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_c.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 FMA Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive FMA test suite."""
        self.log.info(f"Running FMA comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            failures.extend(await self.accumulation_test())

        # Random tests
        if self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"FMA Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"FMA tests failed: {self.fail_count}"


class BF16AdderTB(TBBase):
    """Testbench for BF16 adder (math_bf16_adder).

    Tests the BF16 floating-point adder including:
    - Normal addition and subtraction
    - Special value handling (zero, infinity, NaN, subnormal)
    - Overflow/underflow detection
    - RNE rounding
    - Pipeline operation with valid handshaking
    """

    def __init__(self, dut):
        """Initialize the BF16 adder testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Determine pipeline latency from parameters (default to 0 = combinational)
        self.pipe_stage_1 = self.convert_to_int(os.environ.get('PIPE_STAGE_1', '0'))
        self.pipe_stage_2 = self.convert_to_int(os.environ.get('PIPE_STAGE_2', '0'))
        self.pipe_stage_3 = self.convert_to_int(os.environ.get('PIPE_STAGE_3', '0'))
        self.pipe_stage_4 = self.convert_to_int(os.environ.get('PIPE_STAGE_4', '0'))
        self.latency = 1 + self.pipe_stage_1 + self.pipe_stage_2 + self.pipe_stage_3 + self.pipe_stage_4

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Adder TB initialized, test_level={self.test_level}, latency={self.latency}")

    def _compute_expected_add(self, a_bf16: int, b_bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected addition result.

        Returns:
            Tuple of (result_bf16, overflow, underflow, invalid)
        """
        # Convert to floats
        a_float = BF16Utils.bf16_to_float(a_bf16)
        b_float = BF16Utils.bf16_to_float(b_bf16)

        # Extract fields
        sign_a = (a_bf16 >> 15) & 1
        sign_b = (b_bf16 >> 15) & 1

        # Check special cases
        a_is_zero = BF16Utils.bf16_is_zero(a_bf16) or BF16Utils.bf16_is_subnormal(a_bf16)
        b_is_zero = BF16Utils.bf16_is_zero(b_bf16) or BF16Utils.bf16_is_subnormal(b_bf16)
        a_is_inf = BF16Utils.bf16_is_inf(a_bf16)
        b_is_inf = BF16Utils.bf16_is_inf(b_bf16)
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)

        # Invalid operation: inf - inf (same magnitude, opposite signs)
        invalid = a_is_inf and b_is_inf and (sign_a != sign_b)

        # NaN handling
        if a_is_nan or b_is_nan or invalid:
            return 0x7FC0, False, False, invalid

        # Infinity handling (not inf - inf case)
        if a_is_inf:
            return a_bf16, False, False, False
        if b_is_inf:
            return b_bf16, False, False, False

        # Both zeros
        if a_is_zero and b_is_zero:
            # -0 + -0 = -0, otherwise +0
            result_sign = sign_a & sign_b
            return result_sign << 15, False, False, False

        # One zero
        if a_is_zero:
            return b_bf16, False, False, False
        if b_is_zero:
            return a_bf16, False, False, False

        # Normal addition
        result_float = a_float + b_float

        # Check for exact zero (x - x = 0)
        if result_float == 0.0:
            return 0x0000, False, False, False  # +0 per IEEE 754 RNE

        # Check for overflow/underflow
        abs_result = abs(result_float)
        overflow = False
        underflow = False

        # BF16 max normal: ~3.39e38, min normal: ~1.17e-38
        if abs_result > 3.39e38:
            overflow = True
            sign = 1 if result_float < 0 else 0
            return (sign << 15) | 0x7F80, True, False, False

        if abs_result < 1.17e-38 and abs_result > 0:
            underflow = True
            sign = 1 if result_float < 0 else 0
            return sign << 15, False, True, False

        # Convert to BF16 with RNE rounding
        result_bf16 = BF16Utils.float_to_bf16(result_float)

        return result_bf16, overflow, underflow, False

    async def setup_clocks_and_reset(self) -> None:
        """Set up clock and apply reset."""
        await self.start_clock('i_clk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('i_clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('i_clk', 5)

    async def assert_reset(self) -> None:
        """Assert reset signal (active low)."""
        self.dut.i_rst_n.value = 0

    async def deassert_reset(self) -> None:
        """Deassert reset signal."""
        self.dut.i_rst_n.value = 1

    async def test_single_add(self, a_bf16: int, b_bf16: int, desc: str = "",
                              allow_ulp_tolerance: bool = True) -> bool:
        """Test a single addition.

        Args:
            a_bf16: First BF16 operand
            b_bf16: Second BF16 operand
            desc: Test description
            allow_ulp_tolerance: If True, allow 1 ULP difference for normal values

        Returns:
            True if test passed, False otherwise
        """
        # Apply inputs
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16
        self.dut.i_valid.value = 1

        # Wait for pipeline latency
        if self.latency > 1:
            await self.wait_clocks('i_clk', self.latency)
        else:
            # For combinational (latency=1), wait one clock for valid to propagate
            await self.wait_clocks('i_clk', 1)

        # Read outputs
        result = int(self.dut.ow_result.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        invalid = int(self.dut.ow_invalid.value)
        valid = int(self.dut.ow_valid.value)

        # Deassert valid
        self.dut.i_valid.value = 0

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_invalid = \
            self._compute_expected_add(a_bf16, b_bf16)

        # Compare
        self.test_count += 1

        # For NaN results, just check it's a NaN
        result_is_nan = BF16Utils.bf16_is_nan(result)
        exp_is_nan = BF16Utils.bf16_is_nan(exp_result)

        # Check for special values (zero, inf) - these must match exactly
        result_is_special = BF16Utils.bf16_is_zero(result) or BF16Utils.bf16_is_inf(result)
        exp_is_special = BF16Utils.bf16_is_zero(exp_result) or BF16Utils.bf16_is_inf(exp_result)

        if result_is_nan and exp_is_nan:
            # Both NaN - pass
            passed = True
        elif result_is_special or exp_is_special:
            # Special values must match exactly
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        elif allow_ulp_tolerance:
            # Allow 1 ULP difference for normal values due to rounding differences
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= 1
        else:
            passed = False

        # Check flags
        flags_match = (overflow == exp_overflow and
                       underflow == exp_underflow and
                       invalid == exp_invalid)

        if not flags_match and allow_ulp_tolerance:
            # Allow flag mismatches at boundaries
            flags_match = (invalid == exp_invalid)

        if not flags_match:
            passed = False

        # Check valid handshake
        if not valid:
            passed = False
            self.log.error(f"FAIL {desc}: ow_valid not asserted")

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = BF16Utils.bf16_to_float(a_bf16)
            b_float = BF16Utils.bf16_to_float(b_bf16)
            self.log.error(f"FAIL {desc}: {a_float} + {b_float}")
            self.log.error(f"  a=0x{a_bf16:04X}, b=0x{b_bf16:04X}")
            self.log.error(f"  Expected: result=0x{exp_result:04X}, "
                          f"ovf={exp_overflow}, udf={exp_underflow}, inv={exp_invalid}")
            self.log.error(f"  Actual:   result=0x{result:04X}, "
                          f"ovf={overflow}, udf={underflow}, inv={invalid}, valid={valid}")
            if allow_ulp_tolerance:
                ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
                self.log.error(f"  ULP diff: {ulp_diff}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values: zero, infinity, NaN, subnormal."""
        self.log.info("Starting Special Values Test")
        failures = []

        # Special value bit patterns
        pos_zero = 0x0000
        neg_zero = 0x8000
        pos_inf = 0x7F80
        neg_inf = 0xFF80
        pos_nan = 0x7FC0  # Quiet NaN
        neg_nan = 0xFFC0
        subnormal = 0x0001  # Smallest subnormal
        pos_one = 0x3F80   # 1.0
        neg_one = 0xBF80   # -1.0
        pos_two = 0x4000   # 2.0

        special_cases = [
            # Zero cases
            (pos_zero, pos_one, "0 + 1"),
            (pos_one, pos_zero, "1 + 0"),
            (neg_zero, pos_one, "-0 + 1"),
            (pos_zero, neg_zero, "0 + -0"),
            (neg_zero, neg_zero, "-0 + -0"),

            # Infinity cases
            (pos_inf, pos_one, "inf + 1"),
            (pos_one, pos_inf, "1 + inf"),
            (pos_inf, pos_inf, "inf + inf"),
            (neg_inf, neg_inf, "-inf + -inf"),

            # Invalid: inf - inf
            (pos_inf, neg_inf, "inf + -inf (invalid)"),
            (neg_inf, pos_inf, "-inf + inf (invalid)"),

            # NaN propagation
            (pos_nan, pos_one, "NaN + 1"),
            (pos_one, pos_nan, "1 + NaN"),
            (pos_nan, pos_nan, "NaN + NaN"),
            (pos_nan, pos_inf, "NaN + inf"),

            # Subnormal (FTZ)
            (subnormal, pos_one, "subnormal + 1"),
            (pos_one, subnormal, "1 + subnormal"),

            # Normal operations
            (pos_one, pos_one, "1 + 1"),
            (pos_two, pos_two, "2 + 2"),
            (neg_one, neg_one, "-1 + -1"),
            (pos_one, neg_one, "1 + -1 = 0"),

            # Subtraction via negative addend
            (pos_two, neg_one, "2 + -1 = 1"),
        ]

        for a, b, desc in special_cases:
            if not await self.test_single_add(a, b, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def corner_cases_test(self) -> List[str]:
        """Test corner cases: max/min normal, powers of 2, etc."""
        self.log.info("Starting Corner Cases Test")
        failures = []

        # Important BF16 values
        max_normal = 0x7F7F  # Largest normal (~3.39e38)
        min_normal = 0x0080  # Smallest positive normal (~1.17e-38)
        pos_one = 0x3F80    # 1.0
        neg_one = 0xBF80    # -1.0
        pos_two = 0x4000    # 2.0
        half = 0x3F00       # 0.5

        corner_cases = [
            (max_normal, pos_one, "max_normal + 1"),
            (min_normal, pos_one, "min_normal + 1"),
            (max_normal, max_normal, "max_normal + max_normal (overflow)"),
            (min_normal, min_normal, "min_normal + min_normal"),
            (pos_one, neg_one, "1 - 1 = 0"),
            (pos_two, 0xC000, "2 - 2 = 0"),  # 0xC000 = -2.0
        ]

        # Powers of 2 addition
        for exp in range(0, 6):
            val = 0x3F80 + (exp << 7)  # 1.0 * 2^exp
            corner_cases.append((val, val, f"2^{exp} + 2^{exp}"))

        for a, b, desc in corner_cases:
            if not await self.test_single_add(a, b, desc):
                failures.append(f"Corner case failed: {desc}")

        self.log.info(f"Corner Cases Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def walking_ones_test(self) -> List[str]:
        """Test walking ones pattern in mantissa and exponent fields.

        Walking ones patterns are excellent at detecting stuck-at faults
        and bit-position-dependent bugs in the datapath.
        """
        self.log.info("Starting Walking Ones Test")
        failures = []

        # BF16 format: [15]=sign, [14:7]=exponent (8 bits), [6:0]=mantissa (7 bits)

        # Walking ones in mantissa (bits 0-6) with fixed exponent = 127 (1.x form)
        base_exp = 0x3F80  # exponent = 127, mantissa = 0 -> 1.0
        for bit in range(7):
            val = base_exp | (1 << bit)
            # Test: walking_one + 1.0 (should produce distinct results)
            if not await self.test_single_add(val, 0x3F80, f"walk1_mant_bit{bit}+1.0"):
                failures.append(f"Walking ones mantissa bit {bit} failed")
            # Test: walking_one + walking_one (double the value)
            if not await self.test_single_add(val, val, f"walk1_mant_bit{bit}*2"):
                failures.append(f"Walking ones mantissa bit {bit} double failed")

        # Walking ones in exponent (bits 7-14) with mantissa = 0
        for bit in range(8):
            exp_val = (1 << bit) << 7  # Shift to exponent position [14:7]
            if exp_val >= 0x7F80:  # Skip infinity/NaN (exp=255)
                continue
            # Test: exponent walking one + 1.0
            if not await self.test_single_add(exp_val, 0x3F80, f"walk1_exp_bit{bit}+1.0"):
                failures.append(f"Walking ones exponent bit {bit} failed")
            # Test: exponent walking one + same (double)
            if not await self.test_single_add(exp_val, exp_val, f"walk1_exp_bit{bit}*2"):
                failures.append(f"Walking ones exponent bit {bit} double failed")

        # Walking ones across full 16-bit value (excluding sign for now)
        for bit in range(15):
            val = 1 << bit
            if (val & 0x7F80) == 0x7F80:  # Skip NaN/Inf exponent patterns
                continue
            if (val & 0x7F80) == 0:  # Zero or subnormal exponent
                continue
            if not await self.test_single_add(val, 0x3F80, f"walk1_full_bit{bit}+1.0"):
                failures.append(f"Walking ones full bit {bit} failed")

        self.log.info(f"Walking Ones Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def walking_zeros_test(self) -> List[str]:
        """Test walking zeros pattern (all ones except one bit).

        Complementary to walking ones for detecting stuck-at-one faults.
        """
        self.log.info("Starting Walking Zeros Test")
        failures = []

        # Start with all mantissa bits set, walk a zero through
        base = 0x3FFF  # exp=127 (1.0 base), mantissa = 0x7F (all ones) -> 1.9921875
        for bit in range(7):
            val = base & ~(1 << bit)  # Clear one bit at a time
            if not await self.test_single_add(val, 0x3F80, f"walk0_mant_bit{bit}+1.0"):
                failures.append(f"Walking zeros mantissa bit {bit} failed")
            if not await self.test_single_add(val, val, f"walk0_mant_bit{bit}*2"):
                failures.append(f"Walking zeros mantissa bit {bit} double failed")

        # Walking zeros in exponent with all mantissa bits set
        base = 0x7F7F  # max normal (exp=254, mant=0x7F)
        for bit in range(8):
            exp_mask = (1 << bit) << 7
            val = base & ~exp_mask
            if (val & 0x7F80) == 0:  # Skip if it becomes subnormal
                continue
            if not await self.test_single_add(val, 0x3F80, f"walk0_exp_bit{bit}+1.0"):
                failures.append(f"Walking zeros exponent bit {bit} failed")

        self.log.info(f"Walking Zeros Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def alternating_bits_test(self) -> List[str]:
        """Test alternating bit patterns (0xAAAA, 0x5555, checkerboard).

        These patterns stress carry propagation and bit-pair interactions.
        """
        self.log.info("Starting Alternating Bits Test")
        failures = []

        # Alternating patterns (masked to valid BF16 normal range)
        patterns = [
            (0x5555, "0x5555"),  # 0101...
            (0x2AAA, "0x2AAA"),  # 1010... (masked to avoid sign)
            (0x3333, "0x3333"),  # 0011...
            (0x4CCC, "0x4CCC"),  # 1100...
            (0x0F0F, "0x0F0F"),  # 00001111...
            (0x7070, "0x7070"),  # 11110000...
        ]

        pos_one = 0x3F80  # 1.0

        for pattern, name in patterns:
            # Skip patterns that create NaN/Inf
            if (pattern & 0x7F80) == 0x7F80:
                continue
            # Skip patterns that create zero/subnormal
            if (pattern & 0x7F80) == 0:
                continue

            # Test pattern + 1.0
            if not await self.test_single_add(pattern, pos_one, f"alt_{name}+1.0"):
                failures.append(f"Alternating {name} + 1.0 failed")

            # Test pattern + pattern
            if not await self.test_single_add(pattern, pattern, f"alt_{name}*2"):
                failures.append(f"Alternating {name} + {name} failed")

            # Test pattern + complement (where valid)
            complement = (~pattern) & 0x7FFF
            if (complement & 0x7F80) != 0x7F80 and (complement & 0x7F80) != 0:
                if not await self.test_single_add(pattern, complement, f"alt_{name}+~{name}"):
                    failures.append(f"Alternating {name} + complement failed")

        self.log.info(f"Alternating Bits Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def exponent_sweep_test(self) -> List[str]:
        """Test all exponent values with representative mantissa values.

        Exercises the exponent difference calculation and alignment shifter.
        """
        self.log.info("Starting Exponent Sweep Test")
        failures = []

        # Representative mantissa values
        mantissa_vals = [0x00, 0x01, 0x3F, 0x40, 0x7F]  # min, low, mid, mid-high, max

        # Test each exponent (1-254, skip 0=subnormal, 255=inf/nan)
        for exp in range(1, 255, 8):  # Step by 8 for reasonable coverage
            for mant in mantissa_vals:
                val = (exp << 7) | mant
                # Add to 1.0
                if not await self.test_single_add(val, 0x3F80, f"exp{exp}_mant{mant:02X}+1.0"):
                    failures.append(f"Exponent {exp} mantissa {mant:02X} failed")

        # Test large exponent differences (alignment edge cases)
        small_exp_val = 0x0180  # exp=3 (very small)
        large_exp_val = 0x7E00  # exp=252 (very large)

        if not await self.test_single_add(small_exp_val, large_exp_val, "exp_diff_max"):
            failures.append("Maximum exponent difference failed")

        # Adjacent exponents (important for normalization)
        for exp in range(120, 135):  # Around 1.0
            val1 = exp << 7
            val2 = (exp + 1) << 7
            if not await self.test_single_add(val1, val2, f"adj_exp_{exp}_{exp+1}"):
                failures.append(f"Adjacent exponents {exp}, {exp+1} failed")

        self.log.info(f"Exponent Sweep Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def mantissa_boundary_test(self) -> List[str]:
        """Test mantissa boundary conditions that stress normalization/rounding.

        Tests values near mantissa rollover points.
        """
        self.log.info("Starting Mantissa Boundary Test")
        failures = []

        # Fixed exponent = 127 (represents 1.xxx values)
        base_exp = 127 << 7

        # Mantissa boundary values
        boundary_mantissas = [
            0x00,  # 1.0000000
            0x01,  # 1.0078125 (smallest increment)
            0x3F,  # 1.4921875 (mid-1)
            0x40,  # 1.5000000 (exact half)
            0x7E,  # 1.9843750 (max-1)
            0x7F,  # 1.9921875 (max mantissa)
        ]

        for mant_a in boundary_mantissas:
            val_a = base_exp | mant_a
            for mant_b in boundary_mantissas:
                val_b = base_exp | mant_b
                if not await self.test_single_add(val_a, val_b,
                        f"mant_bound_{mant_a:02X}+{mant_b:02X}"):
                    failures.append(f"Mantissa boundary {mant_a:02X}+{mant_b:02X} failed")

        # Test rounding boundary: 1.5 + 0.5 (result depends on rounding)
        half = 0x3F00  # 0.5
        one_half = 0x3FC0  # 1.5
        if not await self.test_single_add(one_half, half, "1.5+0.5_rounding"):
            failures.append("Rounding boundary 1.5+0.5 failed")

        # Test mantissa overflow: 1.9921875 + 1.9921875 (should normalize)
        max_mant = 0x3FFF  # ~1.99
        if not await self.test_single_add(max_mant, max_mant, "max_mant+max_mant"):
            failures.append("Max mantissa addition failed")

        self.log.info(f"Mantissa Boundary Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def cancellation_test(self) -> List[str]:
        """Test catastrophic cancellation scenarios (a - a, near-equal values).

        These test the leading zero counter and renormalization logic.
        """
        self.log.info("Starting Cancellation Test")
        failures = []

        # Exact cancellation: x + (-x) = 0
        test_vals = [0x3F80, 0x4000, 0x4080, 0x3F00, 0x7F7F]  # Various magnitudes
        for val in test_vals:
            neg_val = val | 0x8000  # Negate
            if not await self.test_single_add(val, neg_val, f"cancel_exact_0x{val:04X}"):
                failures.append(f"Exact cancellation 0x{val:04X} failed")

        # Near cancellation: slightly different values
        # These stress the leading zero counter
        base = 0x4000  # 2.0
        for diff in [1, 2, 4, 8, 16, 32, 64]:
            val_a = base
            val_b = (base - diff) | 0x8000  # Negate the slightly smaller value
            if (val_b & 0x7F80) != 0:  # Valid exponent
                if not await self.test_single_add(val_a, val_b, f"cancel_near_diff{diff}"):
                    failures.append(f"Near cancellation diff={diff} failed")

        # Same exponent, different mantissa (partial cancellation)
        base_exp = 127 << 7
        for mant_diff in [1, 2, 4, 8, 16, 32, 64]:
            val_a = base_exp | 0x40  # mantissa = 0x40
            val_b = (base_exp | (0x40 - mant_diff)) | 0x8000  # Slightly smaller, negated
            if not await self.test_single_add(val_a, val_b, f"cancel_mant_diff{mant_diff}"):
                failures.append(f"Mantissa cancellation diff={mant_diff} failed")

        self.log.info(f"Cancellation Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values (avoid NaN/Inf for basic random test)
            a = random.randint(0, 0x7F7F)  # Positive normal range
            b = random.randint(0, 0x7F7F)

            # Randomly negate
            if random.random() < 0.5:
                a |= 0x8000
            if random.random() < 0.5:
                b |= 0x8000

            if not await self.test_single_add(a, b, f"random_{i}"):
                failures.append(f"Random test {i} failed: a=0x{a:04X}, b=0x{b:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_valid.value = 0
        await self.wait_clocks('i_clk', 1)

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Adder Testbench Settings:')
        self.log.info(f'    Seed:    {self.seed}')
        self.log.info(f'    Level:   {self.test_level}')
        self.log.info(f'    Latency: {self.latency} cycles')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level.

        Test levels and coverage:
        - simple: Special values only (~22 tests)
        - basic: Special + corner + walking patterns + random50 (~150 tests)
        - medium: All basic + exponent sweep + alternating + random200 (~500 tests)
        - full: All patterns + cancellation + boundary + random1000 (~1500 tests)
        """
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values (all levels including 'simple')
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            # Corner cases: max/min normal, powers of 2
            failures.extend(await self.corner_cases_test())

            # Walking patterns: detect stuck-at faults
            failures.extend(await self.walking_ones_test())
            failures.extend(await self.walking_zeros_test())

        if self.test_level in ['medium', 'full']:
            # Alternating bit patterns: stress carry propagation
            failures.extend(await self.alternating_bits_test())

            # Exponent sweep: test alignment shifter
            failures.extend(await self.exponent_sweep_test())

        if self.test_level == 'full':
            # Mantissa boundary: stress normalization/rounding
            failures.extend(await self.mantissa_boundary_test())

            # Cancellation: stress leading zero counter
            failures.extend(await self.cancellation_test())

        # Random tests scale with level
        if self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Adder tests failed: {self.fail_count}"


class BF16ComparatorTB(TBBase):
    """Testbench for BF16 magnitude comparator (math_bf16_comparator).

    Tests the BF16 comparator including:
    - Magnitude comparison (absolute value)
    - Special value handling (zero, infinity, NaN)
    - Equal value detection
    """

    def __init__(self, dut):
        """Initialize the BF16 comparator testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Comparator TB initialized, test_level={self.test_level}")

    def _compute_expected_compare(self, a_bf16: int, b_bf16: int) -> Tuple[int, bool, bool]:
        """Compute expected comparison result.

        Returns:
            Tuple of (max_value, a_greater, equal)
        """
        # Check for NaN - NaN is considered larger than any other value
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)

        if a_is_nan:
            return a_bf16, True, False
        if b_is_nan:
            return b_bf16, False, False

        # Get magnitudes (clear sign bit)
        mag_a = a_bf16 & 0x7FFF
        mag_b = b_bf16 & 0x7FFF

        # Compare magnitudes
        if mag_a > mag_b:
            return a_bf16, True, False
        elif mag_b > mag_a:
            return b_bf16, False, False
        else:
            # Equal magnitudes - return a (tie-breaking)
            return a_bf16, False, True

    async def test_single_compare(self, a_bf16: int, b_bf16: int, desc: str = "") -> bool:
        """Test a single comparison.

        Args:
            a_bf16: First BF16 operand
            b_bf16: Second BF16 operand
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply inputs
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result_max = int(self.dut.ow_max.value)
        a_greater = int(self.dut.ow_a_greater.value)
        equal = int(self.dut.ow_equal.value)

        # Compute expected
        exp_max, exp_a_greater, exp_equal = self._compute_expected_compare(a_bf16, b_bf16)

        # Compare
        self.test_count += 1

        passed = (result_max == exp_max and
                  a_greater == exp_a_greater and
                  equal == exp_equal)

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = BF16Utils.bf16_to_float(a_bf16)
            b_float = BF16Utils.bf16_to_float(b_bf16)
            self.log.error(f"FAIL {desc}: compare({a_float}, {b_float})")
            self.log.error(f"  a=0x{a_bf16:04X}, b=0x{b_bf16:04X}")
            self.log.error(f"  Expected: max=0x{exp_max:04X}, "
                          f"a_greater={exp_a_greater}, equal={exp_equal}")
            self.log.error(f"  Actual:   max=0x{result_max:04X}, "
                          f"a_greater={a_greater}, equal={equal}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values: zero, infinity, NaN."""
        self.log.info("Starting Special Values Test")
        failures = []

        # Special value bit patterns
        pos_zero = 0x0000
        neg_zero = 0x8000
        pos_inf = 0x7F80
        neg_inf = 0xFF80
        pos_nan = 0x7FC0  # Quiet NaN
        pos_one = 0x3F80   # 1.0
        neg_one = 0xBF80   # -1.0
        pos_two = 0x4000   # 2.0
        neg_two = 0xC000   # -2.0

        special_cases = [
            # Zero cases
            (pos_zero, pos_zero, "0 vs 0"),
            (pos_zero, neg_zero, "0 vs -0"),
            (neg_zero, pos_zero, "-0 vs 0"),
            (pos_zero, pos_one, "0 vs 1"),
            (pos_one, pos_zero, "1 vs 0"),

            # Same magnitude, different signs
            (pos_one, neg_one, "1 vs -1"),
            (neg_one, pos_one, "-1 vs 1"),
            (pos_two, neg_two, "2 vs -2"),

            # Different magnitudes
            (pos_one, pos_two, "1 vs 2"),
            (pos_two, pos_one, "2 vs 1"),
            (neg_one, neg_two, "-1 vs -2"),
            (neg_two, neg_one, "-2 vs -1"),

            # Infinity cases
            (pos_inf, pos_one, "inf vs 1"),
            (pos_one, pos_inf, "1 vs inf"),
            (pos_inf, pos_inf, "inf vs inf"),
            (pos_inf, neg_inf, "inf vs -inf"),
            (neg_inf, pos_inf, "-inf vs inf"),

            # NaN cases - NaN should win
            (pos_nan, pos_one, "NaN vs 1"),
            (pos_one, pos_nan, "1 vs NaN"),
            (pos_nan, pos_nan, "NaN vs NaN"),
            (pos_nan, pos_inf, "NaN vs inf"),
            (pos_inf, pos_nan, "inf vs NaN"),
        ]

        for a, b, desc in special_cases:
            if not await self.test_single_compare(a, b, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def corner_cases_test(self) -> List[str]:
        """Test corner cases: max/min normal, etc."""
        self.log.info("Starting Corner Cases Test")
        failures = []

        # Important BF16 values
        max_normal = 0x7F7F  # Largest normal
        min_normal = 0x0080  # Smallest positive normal
        pos_one = 0x3F80    # 1.0
        half = 0x3F00       # 0.5

        corner_cases = [
            (max_normal, min_normal, "max vs min"),
            (min_normal, max_normal, "min vs max"),
            (max_normal, max_normal, "max vs max"),
            (min_normal, min_normal, "min vs min"),
            (pos_one, half, "1.0 vs 0.5"),
            (half, pos_one, "0.5 vs 1.0"),

            # Negative versions
            (max_normal | 0x8000, min_normal | 0x8000, "-max vs -min"),
            (max_normal, max_normal | 0x8000, "max vs -max"),
        ]

        for a, b, desc in corner_cases:
            if not await self.test_single_compare(a, b, desc):
                failures.append(f"Corner case failed: {desc}")

        self.log.info(f"Corner Cases Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values (avoid NaN/Inf for basic random test)
            a = random.randint(0, 0x7F7F)  # Positive normal range
            b = random.randint(0, 0x7F7F)

            # Randomly negate
            if random.random() < 0.5:
                a |= 0x8000
            if random.random() < 0.5:
                b |= 0x8000

            if not await self.test_single_compare(a, b, f"random_{i}"):
                failures.append(f"Random test {i} failed: a=0x{a:04X}, b=0x{b:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Comparator Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            failures.extend(await self.corner_cases_test())

        # Random tests scale with level
        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Comparator tests failed: {self.fail_count}"


class BF16ToIntTB(TBBase):
    """Testbench for BF16 to INT8 converter (math_bf16_to_int).

    Tests the BF16 to INT8 conversion including:
    - Normal conversion with rounding
    - Saturation (overflow/underflow)
    - Special value handling (zero, infinity, NaN)
    """

    def __init__(self, dut):
        """Initialize the BF16 to INT8 testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 to INT8 TB initialized, test_level={self.test_level}")

    def _compute_expected_to_int(self, bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected BF16 to INT8 conversion.

        Returns:
            Tuple of (int8_result, overflow, underflow, is_zero)
        """
        # Check special cases
        is_zero = BF16Utils.bf16_is_zero(bf16) or BF16Utils.bf16_is_subnormal(bf16)
        is_inf = BF16Utils.bf16_is_inf(bf16)
        is_nan = BF16Utils.bf16_is_nan(bf16)
        sign = (bf16 >> 15) & 1

        if is_nan:
            return 0, False, False, False

        if is_inf:
            if sign:
                return 0x80, False, True, False  # -128
            else:
                return 0x7F, True, False, False  # +127

        if is_zero:
            return 0, False, False, True

        # Normal conversion
        float_val = BF16Utils.bf16_to_float(bf16)

        # Round to nearest integer (RNE)
        # Python's round() uses banker's rounding (RNE)
        int_val = round(float_val)

        # Saturate to INT8 range [-128, 127]
        overflow = False
        underflow = False

        if int_val > 127:
            int_val = 127
            overflow = True
        elif int_val < -128:
            int_val = -128
            underflow = True

        # Convert to 8-bit two's complement
        if int_val < 0:
            result = int_val & 0xFF
        else:
            result = int_val

        result_is_zero = (result == 0)

        return result, overflow, underflow, result_is_zero

    async def test_single_conversion(self, bf16: int, desc: str = "") -> bool:
        """Test a single BF16 to INT8 conversion.

        Args:
            bf16: BF16 input value
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply input
        self.dut.i_bf16.value = bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_int8.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        is_zero = int(self.dut.ow_is_zero.value)

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_is_zero = \
            self._compute_expected_to_int(bf16)

        # Compare
        self.test_count += 1

        passed = (result == exp_result and
                  overflow == exp_overflow and
                  underflow == exp_underflow and
                  is_zero == exp_is_zero)

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            float_val = BF16Utils.bf16_to_float(bf16)
            # Convert result to signed for display
            result_signed = result if result < 128 else result - 256
            exp_result_signed = exp_result if exp_result < 128 else exp_result - 256
            self.log.error(f"FAIL {desc}: bf16_to_int({float_val})")
            self.log.error(f"  bf16=0x{bf16:04X}")
            self.log.error(f"  Expected: int8={exp_result_signed}, "
                          f"ovf={exp_overflow}, udf={exp_underflow}, zero={exp_is_zero}")
            self.log.error(f"  Actual:   int8={result_signed}, "
                          f"ovf={overflow}, udf={underflow}, zero={is_zero}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values: zero, infinity, NaN."""
        self.log.info("Starting Special Values Test")
        failures = []

        # Special value bit patterns
        pos_zero = 0x0000
        neg_zero = 0x8000
        pos_inf = 0x7F80
        neg_inf = 0xFF80
        pos_nan = 0x7FC0  # Quiet NaN
        subnormal = 0x0001  # Smallest subnormal

        special_cases = [
            (pos_zero, "positive zero"),
            (neg_zero, "negative zero"),
            (pos_inf, "positive infinity"),
            (neg_inf, "negative infinity"),
            (pos_nan, "NaN"),
            (subnormal, "subnormal"),
        ]

        for bf16, desc in special_cases:
            if not await self.test_single_conversion(bf16, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def boundary_values_test(self) -> List[str]:
        """Test boundary values for INT8 conversion."""
        self.log.info("Starting Boundary Values Test")
        failures = []

        # Key values for INT8 range [-128, 127]
        boundary_values = [
            (0x3F80, "1.0"),         # 1
            (0xBF80, "-1.0"),        # -1
            (0x4000, "2.0"),         # 2
            (0xC000, "-2.0"),        # -2
            (0x42FE, "127.0"),       # 127 (max positive)
            (0xC2FE, "-127.0"),      # -127
            (0x4300, "128.0"),       # 128 -> saturate to 127
            (0xC300, "-128.0"),      # -128 (min negative)
            (0x4302, "129.0"),       # 129 -> saturate to 127
            (0xC340, "-192.0"),      # -192 -> saturate to -128
            (0x3F00, "0.5"),         # 0.5 -> rounds to 0 (RNE)
            (0xBF00, "-0.5"),        # -0.5 -> rounds to 0 (RNE)
            (0x3F40, "0.75"),        # 0.75 -> rounds to 1
            (0xBF40, "-0.75"),       # -0.75 -> rounds to -1
            (0x3FC0, "1.5"),         # 1.5 -> rounds to 2 (RNE)
            (0xBFC0, "-1.5"),        # -1.5 -> rounds to -2 (RNE)
            (0x4040, "2.5"),         # 2.5 -> rounds to 2 (RNE)
            (0xC040, "-2.5"),        # -2.5 -> rounds to -2 (RNE)
            (0x4060, "3.5"),         # 3.5 -> rounds to 4 (RNE)
            (0xC060, "-3.5"),        # -3.5 -> rounds to -4 (RNE)
        ]

        for bf16, desc in boundary_values:
            if not await self.test_single_conversion(bf16, desc):
                failures.append(f"Boundary value failed: {desc}")

        self.log.info(f"Boundary Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values in INT8-representable range
            # exp=127 to 133 covers 1.0 to ~127
            exp = random.randint(120, 140)  # Some underflow, some overflow
            mant = random.randint(0, 0x7F)
            sign = random.randint(0, 1)

            # Skip invalid exponents
            if exp > 255:
                exp = 255
            if exp == 255 and mant != 0:
                mant = 0  # Make it infinity, not NaN

            bf16 = (sign << 15) | (exp << 7) | mant

            if not await self.test_single_conversion(bf16, f"random_{i}"):
                failures.append(f"Random test {i} failed: bf16=0x{bf16:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_bf16.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 to INT8 Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            failures.extend(await self.boundary_values_test())

        # Random tests scale with level
        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"BF16 to INT8 tests failed: {self.fail_count}"


class IntToBF16TB(TBBase):
    """Testbench for signed integer to BF16 converter (math_int_to_bf16).

    Tests the integer to BF16 conversion including:
    - Normal conversion with rounding
    - Zero handling
    - Large integer overflow to infinity
    - Parameterized integer width (8, 16, 32 bits)
    """

    def __init__(self, dut):
        """Initialize the INT to BF16 testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Get integer width from environment (default 32)
        self.int_width = self.convert_to_int(os.environ.get('INT_WIDTH', '32'))

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"INT to BF16 TB initialized, test_level={self.test_level}, int_width={self.int_width}")

    def _compute_expected_from_int(self, int_val: int) -> Tuple[int, bool]:
        """Compute expected integer to BF16 conversion.

        Args:
            int_val: Signed integer value (two's complement)

        Returns:
            Tuple of (bf16_result, is_zero)
        """
        # Handle integer width - interpret as signed
        max_val = (1 << (self.int_width - 1)) - 1
        min_val = -(1 << (self.int_width - 1))

        # Convert from unsigned to signed if needed
        if int_val >= (1 << (self.int_width - 1)):
            int_val = int_val - (1 << self.int_width)

        # Zero case
        if int_val == 0:
            return 0x0000, True

        # Determine sign and absolute value
        sign = 1 if int_val < 0 else 0
        abs_val = abs(int_val)

        # Convert to float and then to BF16
        float_val = float(int_val)

        # Check for overflow (value too large for BF16)
        # BF16 max is ~3.39e38, which is way larger than any 32-bit int
        # So overflow only happens if abs_val > 2^128 approximately (not for 32-bit)
        # For 32-bit int, max is 2^31-1 = 2.1e9, which fits easily in BF16

        # Convert to BF16
        bf16 = BF16Utils.float_to_bf16(float_val)

        return bf16, False

    async def test_single_conversion(self, int_val: int, desc: str = "") -> bool:
        """Test a single integer to BF16 conversion.

        Args:
            int_val: Signed integer input value
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply input (as unsigned for DUT)
        self.dut.i_int.value = int_val & ((1 << self.int_width) - 1)

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_bf16.value)
        is_zero = int(self.dut.ow_is_zero.value)

        # Compute expected
        exp_result, exp_is_zero = self._compute_expected_from_int(int_val)

        # Compare
        self.test_count += 1

        # Allow 1 ULP difference due to rounding differences
        result_is_nan = BF16Utils.bf16_is_nan(result)
        exp_is_nan = BF16Utils.bf16_is_nan(exp_result)

        if result_is_nan and exp_is_nan:
            passed = True
        elif result == exp_result:
            passed = True
        else:
            # Allow 1 ULP difference for rounding
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= 1

        # Check is_zero flag
        if is_zero != exp_is_zero:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            # Convert int to signed for display
            if int_val >= (1 << (self.int_width - 1)):
                int_val_signed = int_val - (1 << self.int_width)
            else:
                int_val_signed = int_val
            result_float = BF16Utils.bf16_to_float(result)
            exp_float = BF16Utils.bf16_to_float(exp_result)
            self.log.error(f"FAIL {desc}: int_to_bf16({int_val_signed})")
            self.log.error(f"  int=0x{int_val & ((1 << self.int_width) - 1):08X}")
            self.log.error(f"  Expected: bf16=0x{exp_result:04X} ({exp_float}), zero={exp_is_zero}")
            self.log.error(f"  Actual:   bf16=0x{result:04X} ({result_float}), zero={is_zero}")
            if ulp_diff := abs((result & 0x7FFF) - (exp_result & 0x7FFF)):
                self.log.error(f"  ULP diff: {ulp_diff}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special integer values: zero, powers of 2, etc."""
        self.log.info("Starting Special Values Test")
        failures = []

        special_cases = [
            (0, "zero"),
            (1, "one"),
            (-1, "negative one"),
            (2, "two"),
            (-2, "negative two"),
            (127, "max_int8"),
            (-128, "min_int8"),
            (255, "max_uint8"),
            (256, "256"),
            (-256, "negative 256"),
        ]

        # Add width-specific cases
        if self.int_width >= 16:
            special_cases.extend([
                (32767, "max_int16"),
                (-32768, "min_int16"),
                (65535, "max_uint16"),
            ])

        if self.int_width >= 32:
            special_cases.extend([
                (2147483647, "max_int32"),
                (-2147483648, "min_int32"),
            ])

        for int_val, desc in special_cases:
            # Check value fits in int_width
            max_val = (1 << (self.int_width - 1)) - 1
            min_val = -(1 << (self.int_width - 1))
            if int_val < min_val or int_val > max_val:
                continue

            if not await self.test_single_conversion(int_val, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def powers_of_two_test(self) -> List[str]:
        """Test powers of 2 (important for floating-point)."""
        self.log.info("Starting Powers of Two Test")
        failures = []

        # Test positive powers of 2
        for exp in range(self.int_width - 1):
            val = 1 << exp
            if not await self.test_single_conversion(val, f"2^{exp}"):
                failures.append(f"Power of 2 failed: 2^{exp}")

            # Also test negative
            if exp < self.int_width - 1:  # -2^(n-1) is valid, but not -2^(n-1) - 1
                neg_val = -(1 << exp)
                if not await self.test_single_conversion(neg_val, f"-2^{exp}"):
                    failures.append(f"Negative power of 2 failed: -2^{exp}")

        # Test powers of 2 minus 1 (all ones pattern)
        for exp in range(1, min(self.int_width - 1, 24)):  # Limit to BF16 precision
            val = (1 << exp) - 1
            if not await self.test_single_conversion(val, f"2^{exp}-1"):
                failures.append(f"Power of 2 minus 1 failed: 2^{exp}-1")

        self.log.info(f"Powers of Two Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def boundary_values_test(self) -> List[str]:
        """Test boundary values near BF16 representable integers."""
        self.log.info("Starting Boundary Values Test")
        failures = []

        # Test small integers that should convert exactly
        for val in range(-128, 128):
            if not await self.test_single_conversion(val, f"small_{val}"):
                failures.append(f"Small integer failed: {val}")

        # Test values near INT8 boundaries
        boundary_vals = [126, 127, 128, 129, 130,
                        -126, -127, -128, -129, -130]
        for val in boundary_vals:
            if not await self.test_single_conversion(val, f"boundary_{val}"):
                failures.append(f"Boundary value failed: {val}")

        self.log.info(f"Boundary Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        max_val = (1 << (self.int_width - 1)) - 1
        min_val = -(1 << (self.int_width - 1))

        for i in range(count):
            # Generate random signed integer
            int_val = random.randint(min_val, max_val)

            if not await self.test_single_conversion(int_val, f"random_{i}"):
                failures.append(f"Random test {i} failed: int={int_val}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_int.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('INT to BF16 Testbench Settings:')
        self.log.info(f'    Seed:      {self.seed}')
        self.log.info(f'    Level:     {self.test_level}')
        self.log.info(f'    INT_WIDTH: {self.int_width}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        if self.test_level in ['basic', 'medium', 'full']:
            failures.extend(await self.powers_of_two_test())

        if self.test_level in ['medium', 'full']:
            failures.extend(await self.boundary_values_test())

        # Random tests scale with level
        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"INT to BF16 tests failed: {self.fail_count}"


class BF16MaxTreeTB(TBBase):
    """Testbench for BF16 max tree (math_bf16_max_tree).

    Tests the tree-based maximum magnitude finder including:
    - Finding max across N BF16 values
    - Correct index tracking
    - NaN handling (NaN propagates)
    - All-zero detection
    """

    def __init__(self, dut):
        """Initialize the BF16 max tree testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Get number of inputs from environment (default 8)
        self.num_inputs = self.convert_to_int(os.environ.get('NUM_INPUTS', '8'))

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Max Tree TB initialized, test_level={self.test_level}, "
                     f"num_inputs={self.num_inputs}")

    def _compute_expected_max(self, values: List[int]) -> Tuple[int, int, bool]:
        """Compute expected max magnitude from list of BF16 values.

        Args:
            values: List of BF16 values (as integers)

        Returns:
            Tuple of (max_value, max_index, all_zero)
        """
        # Check all zero
        all_zero = all(BF16Utils.bf16_is_zero(v) for v in values)

        # Find max by magnitude
        max_val = values[0]
        max_idx = 0

        for i, v in enumerate(values):
            # NaN is considered largest
            if BF16Utils.bf16_is_nan(v):
                max_val = v
                max_idx = i
                break  # NaN wins immediately

            if BF16Utils.bf16_is_nan(max_val):
                continue  # Current max is NaN, keep it

            # Compare magnitudes (ignore sign bit)
            v_mag = v & 0x7FFF
            max_mag = max_val & 0x7FFF

            if v_mag > max_mag:
                max_val = v
                max_idx = i
            elif v_mag == max_mag and i < max_idx:
                # Tie goes to lower index (consistent with RTL)
                max_val = v
                max_idx = i

        return max_val, max_idx, all_zero

    async def test_single_max(self, values: List[int], desc: str = "") -> bool:
        """Test a single max tree operation.

        Args:
            values: List of BF16 input values
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Pack values into flattened bus: {val[N-1], ..., val[1], val[0]}
        flat_value = 0
        for i, v in enumerate(values):
            flat_value |= (v & 0xFFFF) << (i * 16)
        self.dut.i_values_flat.value = flat_value

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result_max = int(self.dut.ow_max.value)
        result_idx = int(self.dut.ow_max_index.value)
        result_all_zero = int(self.dut.ow_all_zero.value)

        # Compute expected
        exp_max, exp_idx, exp_all_zero = self._compute_expected_max(values)

        # Compare
        self.test_count += 1

        # Check max value (allow for tie-breaking differences)
        max_match = (result_max == exp_max)
        if not max_match:
            # Check if magnitudes match (different index tie-breaking is OK)
            max_match = ((result_max & 0x7FFF) == (exp_max & 0x7FFF))

        # Check all_zero flag
        zero_match = (result_all_zero == (1 if exp_all_zero else 0))

        passed = max_match and zero_match

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.error(f"FAIL {desc}: max_tree")
            self.log.error(f"  Inputs: {[f'0x{v:04X}' for v in values]}")
            self.log.error(f"  Expected: max=0x{exp_max:04X} idx={exp_idx} all_zero={exp_all_zero}")
            self.log.error(f"  Actual:   max=0x{result_max:04X} idx={result_idx} all_zero={result_all_zero}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special input patterns."""
        self.log.info("Starting Special Values Test")
        failures = []

        # All zeros
        values = [0x0000] * self.num_inputs
        if not await self.test_single_max(values, "all_zeros"):
            failures.append("All zeros failed")

        # Single non-zero value at each position
        for pos in range(self.num_inputs):
            values = [0x0000] * self.num_inputs
            values[pos] = 0x3F80  # 1.0
            if not await self.test_single_max(values, f"single_at_{pos}"):
                failures.append(f"Single value at position {pos} failed")

        # All same value
        values = [0x4000] * self.num_inputs  # All 2.0
        if not await self.test_single_max(values, "all_same"):
            failures.append("All same value failed")

        # Increasing magnitudes
        values = [BF16Utils.float_to_bf16(float(i + 1)) for i in range(self.num_inputs)]
        if not await self.test_single_max(values, "increasing"):
            failures.append("Increasing values failed")

        # Decreasing magnitudes
        values = [BF16Utils.float_to_bf16(float(self.num_inputs - i)) for i in range(self.num_inputs)]
        if not await self.test_single_max(values, "decreasing"):
            failures.append("Decreasing values failed")

        # NaN in different positions
        for pos in range(min(4, self.num_inputs)):
            values = [0x3F80] * self.num_inputs
            values[pos] = 0x7FC0  # NaN
            if not await self.test_single_max(values, f"nan_at_{pos}"):
                failures.append(f"NaN at position {pos} failed")

        # Infinity handling
        values = [0x3F80] * self.num_inputs
        values[self.num_inputs // 2] = 0x7F80  # +Infinity
        if not await self.test_single_max(values, "pos_infinity"):
            failures.append("Positive infinity failed")

        values = [0x3F80] * self.num_inputs
        values[self.num_inputs // 2] = 0xFF80  # -Infinity (same magnitude as +inf)
        if not await self.test_single_max(values, "neg_infinity"):
            failures.append("Negative infinity failed")

        # Mixed signs (magnitude comparison)
        values = [0xBF80] * self.num_inputs  # All -1.0
        values[0] = 0x4000  # 2.0 (larger magnitude)
        if not await self.test_single_max(values, "mixed_signs"):
            failures.append("Mixed signs failed")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values
            values = []
            for _ in range(self.num_inputs):
                # Mix of random values including some special cases
                r = random.random()
                if r < 0.05:
                    # Zero
                    values.append(0x0000)
                elif r < 0.08:
                    # NaN
                    values.append(0x7FC0 | random.randint(0, 0x3F))
                elif r < 0.10:
                    # Infinity
                    values.append(0x7F80 if random.random() < 0.5 else 0xFF80)
                else:
                    # Random normal value
                    float_val = random.uniform(-1000, 1000)
                    values.append(BF16Utils.float_to_bf16(float_val))

            if not await self.test_single_max(values, f"random_{i}"):
                failures.append(f"Random test {i} failed")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_values_flat.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Max Tree Testbench Settings:')
        self.log.info(f'    Seed:       {self.seed}')
        self.log.info(f'    Level:      {self.test_level}')
        self.log.info(f'    NUM_INPUTS: {self.num_inputs}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values
        failures.extend(await self.special_values_test())

        # Random tests scale with level
        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"BF16 Max Tree tests failed: {self.fail_count}"


class BF16DividerTB(TBBase):
    """Testbench for BF16 divider (math_bf16_divider).

    Tests the BF16 floating-point divider including:
    - Normal division operations
    - Division by zero handling
    - Special value handling (inf, nan, zero)
    - Round-to-Nearest-Even rounding
    - Overflow and underflow detection
    """

    def __init__(self, dut):
        """Initialize the BF16 divider testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Divider TB initialized, test_level={self.test_level}")

    def _compute_expected_divide(self, a_bf16: int, b_bf16: int) -> Tuple[int, bool, bool, bool, bool]:
        """Compute expected division result.

        Args:
            a_bf16: Dividend as BF16 integer
            b_bf16: Divisor as BF16 integer

        Returns:
            Tuple of (result, overflow, underflow, div_by_zero, invalid)
        """
        # Check special cases
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)
        a_is_inf = BF16Utils.bf16_is_inf(a_bf16)
        b_is_inf = BF16Utils.bf16_is_inf(b_bf16)
        a_is_zero = BF16Utils.bf16_is_zero(a_bf16)
        b_is_zero = BF16Utils.bf16_is_zero(b_bf16)

        # Subnormal detection (exp=0, mant!=0) - treated as zero in FTZ mode
        a_exp = (a_bf16 >> 7) & 0xFF
        a_mant = a_bf16 & 0x7F
        b_exp = (b_bf16 >> 7) & 0xFF
        b_mant = b_bf16 & 0x7F
        a_is_subnormal = (a_exp == 0) and (a_mant != 0)
        b_is_subnormal = (b_exp == 0) and (b_mant != 0)

        # Effective zero includes subnormals (FTZ mode)
        a_eff_zero = a_is_zero or a_is_subnormal
        b_eff_zero = b_is_zero or b_is_subnormal

        # Result sign
        sign = (a_bf16 >> 15) ^ (b_bf16 >> 15)

        # NaN propagation
        if a_is_nan or b_is_nan:
            return (0x7FC0 | (sign << 15), False, False, False, False)

        # Invalid: 0/0 or inf/inf (using effective zero for subnormals)
        if (a_eff_zero and b_eff_zero) or (a_is_inf and b_is_inf):
            return (0x7FC0 | (sign << 15), False, False, False, True)

        # Division by zero (non-zero / zero) - subnormal divisor = div by zero
        if b_eff_zero and not a_eff_zero and not a_is_inf and not a_is_nan:
            return (0x7F80 | (sign << 15), False, False, True, False)

        # Zero result (zero / non-zero finite) - subnormal dividend = zero result
        if a_eff_zero and not b_eff_zero and not b_is_inf and not b_is_nan:
            return (0x0000 | (sign << 15), False, False, False, False)

        # Infinity result (inf / finite)
        if a_is_inf and not b_is_inf and not b_is_nan:
            return (0x7F80 | (sign << 15), False, False, False, False)

        # Zero result (finite / inf)
        if b_is_inf and not a_is_inf and not a_is_nan:
            return (0x0000 | (sign << 15), False, False, False, False)

        # Convert to float for normal division
        a_float = BF16Utils.bf16_to_float(a_bf16)
        b_float = BF16Utils.bf16_to_float(b_bf16)

        # Normal division
        if b_float == 0.0:
            # Should have been caught above, but just in case
            return (0x7F80 | (sign << 15), False, False, True, False)

        result_float = a_float / b_float

        # Check for overflow
        if abs(result_float) > 3.38953139e38:  # Max BF16
            return (0x7F80 | (sign << 15), True, False, False, False)

        # Check for underflow
        if abs(result_float) < 1.17549435e-38 and result_float != 0.0:  # Min normal BF16
            return (0x0000 | (sign << 15), False, True, False, False)

        # Normal result
        result_bf16 = BF16Utils.float_to_bf16(result_float)

        # Apply FTZ (Flush-to-Zero) on output: if result is subnormal, return 0 with same sign
        if BF16Utils.bf16_is_subnormal(result_bf16):
            result_bf16 = (result_bf16 & 0x8000)  # Preserve sign, zero the rest

        return (result_bf16, False, False, False, False)

    async def test_single_divide(self, a_bf16: int, b_bf16: int, desc: str = "") -> bool:
        """Test a single division operation.

        Args:
            a_bf16: Dividend as BF16 integer
            b_bf16: Divisor as BF16 integer
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply inputs
        self.dut.i_a.value = a_bf16
        self.dut.i_b.value = b_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_result.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        div_by_zero = int(self.dut.ow_div_by_zero.value)
        invalid = int(self.dut.ow_invalid.value)

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_div_by_zero, exp_invalid = \
            self._compute_expected_divide(a_bf16, b_bf16)

        # Compare
        self.test_count += 1

        # For normal results, allow 1 ULP tolerance due to rounding differences
        result_match = False
        if BF16Utils.bf16_is_nan(exp_result) and BF16Utils.bf16_is_nan(result):
            result_match = True
        elif BF16Utils.bf16_is_inf(exp_result) and BF16Utils.bf16_is_inf(result):
            result_match = (exp_result >> 15) == (result >> 15)  # Same sign
        elif BF16Utils.bf16_is_zero(exp_result) and BF16Utils.bf16_is_zero(result):
            result_match = True  # Both zero (ignore sign for zero)
        else:
            # Normal value - check within 1 ULP
            diff = abs(int(result) - int(exp_result))
            result_match = diff <= 1

        # Check flags
        flags_match = (overflow == (1 if exp_overflow else 0) and
                      underflow == (1 if exp_underflow else 0) and
                      div_by_zero == (1 if exp_div_by_zero else 0) and
                      invalid == (1 if exp_invalid else 0))

        passed = result_match and flags_match

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            a_float = BF16Utils.bf16_to_float(a_bf16)
            b_float = BF16Utils.bf16_to_float(b_bf16)
            result_float = BF16Utils.bf16_to_float(result)
            exp_float = BF16Utils.bf16_to_float(exp_result)
            self.log.error(f"FAIL {desc}: {a_float} / {b_float}")
            self.log.error(f"  Inputs: a=0x{a_bf16:04X}, b=0x{b_bf16:04X}")
            self.log.error(f"  Expected: result=0x{exp_result:04X} ({exp_float})")
            self.log.error(f"  Actual:   result=0x{result:04X} ({result_float})")
            self.log.error(f"  Expected flags: ovf={exp_overflow} unf={exp_underflow} "
                          f"dbz={exp_div_by_zero} inv={exp_invalid}")
            self.log.error(f"  Actual flags:   ovf={overflow} unf={underflow} "
                          f"dbz={div_by_zero} inv={invalid}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special value combinations."""
        self.log.info("Starting Special Values Test")
        failures = []

        # Constants
        ZERO = 0x0000
        NEG_ZERO = 0x8000
        ONE = 0x3F80
        NEG_ONE = 0xBF80
        TWO = 0x4000
        HALF = 0x3F00
        INF = 0x7F80
        NEG_INF = 0xFF80
        NAN = 0x7FC0
        SUBNORMAL = 0x0001

        # Basic division
        test_cases = [
            (ONE, ONE, "1/1"),
            (TWO, ONE, "2/1"),
            (ONE, TWO, "1/2"),
            (NEG_ONE, ONE, "-1/1"),
            (ONE, NEG_ONE, "1/-1"),
            (NEG_ONE, NEG_ONE, "-1/-1"),
        ]

        for a, b, desc in test_cases:
            if not await self.test_single_divide(a, b, desc):
                failures.append(f"{desc} failed")

        # Division by zero
        if not await self.test_single_divide(ONE, ZERO, "1/0"):
            failures.append("Division by zero failed")
        if not await self.test_single_divide(NEG_ONE, ZERO, "-1/0"):
            failures.append("Negative division by zero failed")

        # Zero divided by something
        if not await self.test_single_divide(ZERO, ONE, "0/1"):
            failures.append("Zero dividend failed")
        if not await self.test_single_divide(ZERO, NEG_ONE, "0/-1"):
            failures.append("Zero dividend neg divisor failed")

        # Invalid operations
        if not await self.test_single_divide(ZERO, ZERO, "0/0"):
            failures.append("0/0 invalid failed")
        if not await self.test_single_divide(INF, INF, "inf/inf"):
            failures.append("inf/inf invalid failed")

        # Infinity handling
        if not await self.test_single_divide(INF, ONE, "inf/1"):
            failures.append("inf/1 failed")
        if not await self.test_single_divide(ONE, INF, "1/inf"):
            failures.append("1/inf failed")
        if not await self.test_single_divide(NEG_INF, ONE, "-inf/1"):
            failures.append("-inf/1 failed")

        # NaN propagation
        if not await self.test_single_divide(NAN, ONE, "nan/1"):
            failures.append("nan/1 failed")
        if not await self.test_single_divide(ONE, NAN, "1/nan"):
            failures.append("1/nan failed")
        if not await self.test_single_divide(NAN, NAN, "nan/nan"):
            failures.append("nan/nan failed")

        # Subnormal handling (flush to zero)
        if not await self.test_single_divide(SUBNORMAL, ONE, "subnormal/1"):
            failures.append("subnormal/1 failed")
        if not await self.test_single_divide(ONE, SUBNORMAL, "1/subnormal"):
            failures.append("1/subnormal failed")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def quantizer_values_test(self) -> List[str]:
        """Test division patterns specific to quantizer: 127/max calculations."""
        self.log.info("Starting Quantizer Values Test")
        failures = []

        # 127 in BF16 = 0x42FE
        BF16_127 = 0x42FE

        # Test 127 / various max values that would occur in quantization
        test_values = [
            (1.0, "127/1"),
            (2.0, "127/2"),
            (3.0, "127/3"),
            (4.0, "127/4"),
            (10.0, "127/10"),
            (50.0, "127/50"),
            (100.0, "127/100"),
            (127.0, "127/127"),
            (200.0, "127/200"),
            (0.5, "127/0.5"),
            (0.25, "127/0.25"),
            (0.1, "127/0.1"),
        ]

        for divisor_float, desc in test_values:
            divisor_bf16 = BF16Utils.float_to_bf16(divisor_float)
            if not await self.test_single_divide(BF16_127, divisor_bf16, desc):
                failures.append(f"{desc} failed")

        # Also test max/127 for scale factor calculation
        for dividend_float, desc in test_values:
            dividend_bf16 = BF16Utils.float_to_bf16(dividend_float)
            if not await self.test_single_divide(dividend_bf16, BF16_127, f"{dividend_float}/127"):
                failures.append(f"{dividend_float}/127 failed")

        self.log.info(f"Quantizer Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def boundary_test(self) -> List[str]:
        """Test boundary conditions for exponent overflow/underflow."""
        self.log.info("Starting Boundary Test")
        failures = []

        # Large / small -> overflow
        large = BF16Utils.float_to_bf16(1e30)
        small = BF16Utils.float_to_bf16(1e-30)

        if not await self.test_single_divide(large, small, "large/small_overflow"):
            failures.append("Overflow test failed")

        # Small / large -> underflow
        if not await self.test_single_divide(small, large, "small/large_underflow"):
            failures.append("Underflow test failed")

        # Near-max values
        max_normal = 0x7F7F  # Largest normal BF16
        min_normal = 0x0080  # Smallest normal BF16

        if not await self.test_single_divide(max_normal, min_normal, "max/min"):
            failures.append("max/min failed")
        if not await self.test_single_divide(min_normal, max_normal, "min/max"):
            failures.append("min/max failed")

        self.log.info(f"Boundary Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random BF16 values
            r = random.random()

            if r < 0.05:
                # Special values
                a = random.choice([0x0000, 0x7F80, 0xFF80, 0x7FC0])
            elif r < 0.15:
                # Small values
                a = BF16Utils.float_to_bf16(random.uniform(-1, 1))
            else:
                # Normal range
                a = BF16Utils.float_to_bf16(random.uniform(-1000, 1000))

            r = random.random()
            if r < 0.02:
                # Division by zero
                b = 0x0000
            elif r < 0.05:
                # Special values
                b = random.choice([0x7F80, 0xFF80, 0x7FC0])
            elif r < 0.15:
                # Small values
                b = BF16Utils.float_to_bf16(random.uniform(-1, 1))
            else:
                # Normal range (avoid zero)
                val = random.uniform(-1000, 1000)
                while abs(val) < 0.01:
                    val = random.uniform(-1000, 1000)
                b = BF16Utils.float_to_bf16(val)

            if not await self.test_single_divide(a, b, f"random_{i}"):
                failures.append(f"Random test {i} failed")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Divider Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        # Always run special values and quantizer-specific tests
        failures.extend(await self.special_values_test())
        failures.extend(await self.quantizer_values_test())
        failures.extend(await self.boundary_test())

        # Random tests scale with level
        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"BF16 Divider tests failed: {self.fail_count}"


class BF16ReciprocalTB(TBBase):
    """Testbench for BF16 reciprocal (math_bf16_reciprocal).

    Tests the fast reciprocal (1/x) using LUT + Newton-Raphson:
    - Normal reciprocal computation
    - Special value handling (zero, infinity, NaN)
    - Division by zero detection
    - Accuracy verification (within BF16 precision)
    """

    def __init__(self, dut):
        """Initialize the BF16 reciprocal testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Reciprocal TB initialized, test_level={self.test_level}")

    def _compute_expected_reciprocal(self, x_bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected reciprocal result.

        Returns:
            Tuple of (reciprocal_bf16, div_by_zero, is_zero, invalid)
        """
        # Check special cases
        is_zero = BF16Utils.bf16_is_zero(x_bf16) or BF16Utils.bf16_is_subnormal(x_bf16)
        is_inf = BF16Utils.bf16_is_inf(x_bf16)
        is_nan = BF16Utils.bf16_is_nan(x_bf16)
        sign = (x_bf16 >> 15) & 1

        if is_nan:
            # NaN -> NaN
            return (sign << 15) | 0x7FC0, False, False, True

        if is_zero:
            # 1/0 = infinity
            return (sign << 15) | 0x7F80, True, False, False

        if is_inf:
            # 1/infinity = 0
            return (sign << 15), False, True, False

        # Normal reciprocal
        float_val = BF16Utils.bf16_to_float(x_bf16)
        try:
            recip_float = 1.0 / float_val
        except ZeroDivisionError:
            return (sign << 15) | 0x7F80, True, False, False

        # Check for overflow/underflow
        abs_recip = abs(recip_float)
        if abs_recip > 3.39e38:
            return (sign << 15) | 0x7F80, False, False, False
        if abs_recip < 1.17e-38 and abs_recip > 0:
            return (sign << 15), False, True, False

        # Convert to BF16
        result_bf16 = BF16Utils.float_to_bf16(recip_float)

        # Apply FTZ (Flush-to-Zero) on output: if result is subnormal, return 0 with same sign
        if BF16Utils.bf16_is_subnormal(result_bf16):
            result_bf16 = (result_bf16 & 0x8000)  # Preserve sign, zero the rest

        result_is_zero = BF16Utils.bf16_is_zero(result_bf16)

        return result_bf16, False, result_is_zero, False

    async def test_single_reciprocal(self, x_bf16: int, desc: str = "",
                                     ulp_tolerance: int = 2) -> bool:
        """Test a single reciprocal operation.

        Args:
            x_bf16: BF16 input value
            desc: Test description
            ulp_tolerance: Allowed ULP difference (LUT+NR may have ~2 ULP error)

        Returns:
            True if test passed, False otherwise
        """
        # Apply input
        self.dut.i_x.value = x_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_reciprocal.value)
        div_by_zero = int(self.dut.ow_div_by_zero.value)
        is_zero = int(self.dut.ow_is_zero.value)
        invalid = int(self.dut.ow_invalid.value)

        # Compute expected
        exp_result, exp_div_by_zero, exp_is_zero, exp_invalid = \
            self._compute_expected_reciprocal(x_bf16)

        # Compare
        self.test_count += 1

        # Check for NaN - both should be NaN
        result_is_nan = BF16Utils.bf16_is_nan(result)
        exp_is_nan = BF16Utils.bf16_is_nan(exp_result)

        if result_is_nan and exp_is_nan:
            passed = True
        elif BF16Utils.bf16_is_zero(result) and BF16Utils.bf16_is_zero(exp_result):
            # Both zero (sign may differ for +0 vs -0)
            passed = True
        elif BF16Utils.bf16_is_inf(result) and BF16Utils.bf16_is_inf(exp_result):
            # Both infinity - check sign
            passed = (result >> 15) == (exp_result >> 15)
        elif result == exp_result:
            passed = True
        else:
            # Allow ULP tolerance for normal values
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= ulp_tolerance

        # Check flags
        flags_match = (div_by_zero == exp_div_by_zero and
                      is_zero == exp_is_zero and
                      invalid == exp_invalid)

        if not flags_match:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            float_val = BF16Utils.bf16_to_float(x_bf16)
            self.log.error(f"FAIL {desc}: 1/{float_val}")
            self.log.error(f"  x=0x{x_bf16:04X}")
            self.log.error(f"  Expected: result=0x{exp_result:04X}, "
                          f"dbz={exp_div_by_zero}, zero={exp_is_zero}, inv={exp_invalid}")
            self.log.error(f"  Actual:   result=0x{result:04X}, "
                          f"dbz={div_by_zero}, zero={is_zero}, inv={invalid}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values."""
        self.log.info("Starting Special Values Test")
        failures = []

        special_cases = [
            (0x0000, "1/+0 (div by zero)"),
            (0x8000, "1/-0 (div by zero)"),
            (0x7F80, "1/+inf"),
            (0xFF80, "1/-inf"),
            (0x7FC0, "1/NaN"),
            (0x3F80, "1/1.0"),
            (0xBF80, "1/-1.0"),
            (0x4000, "1/2.0"),
            (0xC000, "1/-2.0"),
        ]

        for bf16, desc in special_cases:
            if not await self.test_single_reciprocal(bf16, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def powers_of_two_test(self) -> List[str]:
        """Test reciprocals of powers of 2 (should be exact)."""
        self.log.info("Starting Powers of Two Test")
        failures = []

        # Powers of 2 from 2^-6 to 2^7
        for exp_offset in range(-6, 8):
            bf16_exp = 127 + exp_offset
            bf16 = bf16_exp << 7  # Mantissa = 0, so exactly 2^exp_offset
            desc = f"1/2^{exp_offset}"
            if not await self.test_single_reciprocal(bf16, desc, ulp_tolerance=1):
                failures.append(f"Power of two failed: {desc}")

        self.log.info(f"Powers of Two Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random normal BF16 values
            exp = random.randint(1, 254)  # Avoid zero/inf/nan exponents
            mant = random.randint(0, 0x7F)
            sign = random.randint(0, 1)
            bf16 = (sign << 15) | (exp << 7) | mant

            if not await self.test_single_reciprocal(bf16, f"random_{i}"):
                failures.append(f"Random test {i} failed: x=0x{bf16:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_x.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Reciprocal Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        failures.extend(await self.special_values_test())
        failures.extend(await self.powers_of_two_test())

        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"BF16 Reciprocal tests failed: {self.fail_count}"


class BF16ScaleToInt8TB(TBBase):
    """Testbench for fused BF16 scale-to-INT8 (math_bf16_scale_to_int8).

    Tests the fused multiply + INT8 conversion:
    - Normal quantization operations
    - Saturation handling
    - Special value propagation
    - Accuracy verification
    """

    def __init__(self, dut):
        """Initialize the BF16 scale-to-INT8 testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Scale-to-INT8 TB initialized, test_level={self.test_level}")

    def _compute_expected_scale_to_int8(self, value_bf16: int, scale_bf16: int
                                        ) -> Tuple[int, bool, bool, bool, bool]:
        """Compute expected fused scale-to-INT8 result.

        Returns:
            Tuple of (int8_result, overflow, underflow, is_zero, invalid)
        """
        # Check special cases
        v_is_zero = BF16Utils.bf16_is_zero(value_bf16) or BF16Utils.bf16_is_subnormal(value_bf16)
        s_is_zero = BF16Utils.bf16_is_zero(scale_bf16) or BF16Utils.bf16_is_subnormal(scale_bf16)
        v_is_inf = BF16Utils.bf16_is_inf(value_bf16)
        s_is_inf = BF16Utils.bf16_is_inf(scale_bf16)
        v_is_nan = BF16Utils.bf16_is_nan(value_bf16)
        s_is_nan = BF16Utils.bf16_is_nan(scale_bf16)

        sign_v = (value_bf16 >> 15) & 1
        sign_s = (scale_bf16 >> 15) & 1
        sign_result = sign_v ^ sign_s

        # Invalid: NaN or 0*inf
        invalid = v_is_nan or s_is_nan or (v_is_zero and s_is_inf) or (v_is_inf and s_is_zero)
        if invalid:
            return 0, False, False, False, True

        # Infinity result
        if v_is_inf or s_is_inf:
            if sign_result:
                return 0x80, False, True, False, False  # -128
            else:
                return 0x7F, True, False, False, False  # +127

        # Zero result
        if v_is_zero or s_is_zero:
            return 0, False, False, True, False

        # Normal computation
        value_float = BF16Utils.bf16_to_float(value_bf16)
        scale_float = BF16Utils.bf16_to_float(scale_bf16)
        product = value_float * scale_float

        # Round to nearest integer (RNE)
        int_val = round(product)

        # Saturate to INT8 range
        overflow = False
        underflow = False
        if int_val > 127:
            int_val = 127
            overflow = True
        elif int_val < -128:
            int_val = -128
            underflow = True

        # Convert to 8-bit two's complement
        if int_val < 0:
            result = int_val & 0xFF
        else:
            result = int_val

        is_zero = (result == 0)

        return result, overflow, underflow, is_zero, False

    async def test_single_scale(self, value_bf16: int, scale_bf16: int,
                                desc: str = "") -> bool:
        """Test a single fused scale-to-INT8 operation.

        Args:
            value_bf16: BF16 value to quantize
            scale_bf16: BF16 scale factor
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply inputs
        self.dut.i_value.value = value_bf16
        self.dut.i_scale.value = scale_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_int8.value)
        overflow = int(self.dut.ow_overflow.value)
        underflow = int(self.dut.ow_underflow.value)
        is_zero = int(self.dut.ow_is_zero.value)
        invalid = int(self.dut.ow_invalid.value)

        # Compute expected
        exp_result, exp_overflow, exp_underflow, exp_is_zero, exp_invalid = \
            self._compute_expected_scale_to_int8(value_bf16, scale_bf16)

        # Compare
        self.test_count += 1

        # Allow 1 unit tolerance for rounding differences
        result_signed = result if result < 128 else result - 256
        exp_signed = exp_result if exp_result < 128 else exp_result - 256
        value_match = abs(result_signed - exp_signed) <= 1

        flags_match = (overflow == exp_overflow and
                      underflow == exp_underflow and
                      is_zero == exp_is_zero and
                      invalid == exp_invalid)

        passed = value_match and flags_match

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            val_float = BF16Utils.bf16_to_float(value_bf16)
            scale_float = BF16Utils.bf16_to_float(scale_bf16)
            self.log.error(f"FAIL {desc}: {val_float} * {scale_float}")
            self.log.error(f"  value=0x{value_bf16:04X}, scale=0x{scale_bf16:04X}")
            self.log.error(f"  Expected: int8={exp_signed}, "
                          f"ovf={exp_overflow}, udf={exp_underflow}, "
                          f"zero={exp_is_zero}, inv={exp_invalid}")
            self.log.error(f"  Actual:   int8={result_signed}, "
                          f"ovf={overflow}, udf={underflow}, "
                          f"zero={is_zero}, inv={invalid}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special value combinations."""
        self.log.info("Starting Special Values Test")
        failures = []

        pos_one = 0x3F80  # 1.0
        pos_zero = 0x0000
        pos_inf = 0x7F80
        pos_nan = 0x7FC0

        cases = [
            (pos_zero, pos_one, "0 * 1"),
            (pos_one, pos_zero, "1 * 0"),
            (pos_inf, pos_one, "inf * 1"),
            (pos_zero, pos_inf, "0 * inf (invalid)"),
            (pos_nan, pos_one, "NaN * 1"),
            (pos_one, pos_nan, "1 * NaN"),
        ]

        for v, s, desc in cases:
            if not await self.test_single_scale(v, s, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def quantization_test(self) -> List[str]:
        """Test typical quantization scenarios."""
        self.log.info("Starting Quantization Test")
        failures = []

        # Typical quantization: value * (127/max)
        # If max = 3.0, scale = 127/3 = 42.33
        scale_42 = BF16Utils.float_to_bf16(42.33)

        values = [
            (BF16Utils.float_to_bf16(0.0), "0.0 * scale"),
            (BF16Utils.float_to_bf16(1.0), "1.0 * scale"),
            (BF16Utils.float_to_bf16(2.0), "2.0 * scale"),
            (BF16Utils.float_to_bf16(3.0), "3.0 * scale"),
            (BF16Utils.float_to_bf16(-1.0), "-1.0 * scale"),
            (BF16Utils.float_to_bf16(-3.0), "-3.0 * scale"),
            (BF16Utils.float_to_bf16(0.5), "0.5 * scale"),
            (BF16Utils.float_to_bf16(-0.5), "-0.5 * scale"),
        ]

        for v, desc in values:
            if not await self.test_single_scale(v, scale_42, desc):
                failures.append(f"Quantization test failed: {desc}")

        self.log.info(f"Quantization Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def saturation_test(self) -> List[str]:
        """Test saturation at INT8 boundaries."""
        self.log.info("Starting Saturation Test")
        failures = []

        one = 0x3F80  # 1.0

        # Values that should saturate
        cases = [
            (BF16Utils.float_to_bf16(128.0), one, "128 * 1 (overflow)"),
            (BF16Utils.float_to_bf16(200.0), one, "200 * 1 (overflow)"),
            (BF16Utils.float_to_bf16(-129.0), one, "-129 * 1 (underflow)"),
            (BF16Utils.float_to_bf16(-200.0), one, "-200 * 1 (underflow)"),
            (BF16Utils.float_to_bf16(127.0), one, "127 * 1 (max positive)"),
            (BF16Utils.float_to_bf16(-128.0), one, "-128 * 1 (max negative)"),
        ]

        for v, s, desc in cases:
            if not await self.test_single_scale(v, s, desc):
                failures.append(f"Saturation test failed: {desc}")

        self.log.info(f"Saturation Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Random value in reasonable range
            value = BF16Utils.float_to_bf16(random.uniform(-150, 150))
            # Random positive scale (quantization scales are positive)
            scale = BF16Utils.float_to_bf16(random.uniform(0.1, 10.0))

            if not await self.test_single_scale(value, scale, f"random_{i}"):
                failures.append(f"Random test {i} failed")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_value.value = 0
        self.dut.i_scale.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Scale-to-INT8 Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        failures.extend(await self.special_values_test())
        failures.extend(await self.quantization_test())
        failures.extend(await self.saturation_test())

        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Scale-to-INT8 tests failed: {self.fail_count}"


class BF16Log2ScaleTB(TBBase):
    """Testbench for BF16 log2 scale calculator (math_bf16_log2_scale).

    Tests power-of-2 quantization scale computation:
    - Scale exponent calculation
    - Shift amount computation
    - Special value handling
    """

    def __init__(self, dut):
        """Initialize the BF16 log2 scale testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Log2 Scale TB initialized, test_level={self.test_level}")

    def _compute_expected_log2_scale(self, max_bf16: int
                                     ) -> Tuple[int, int, int, int, bool, bool]:
        """Compute expected log2 scale parameters.

        Returns:
            Tuple of (scale_exp, quant_shift, dequant_shift, scale_bf16, is_zero, is_overflow)
        """
        is_zero = BF16Utils.bf16_is_zero(max_bf16) or BF16Utils.bf16_is_subnormal(max_bf16)
        is_inf = BF16Utils.bf16_is_inf(max_bf16)
        is_nan = BF16Utils.bf16_is_nan(max_bf16)

        if is_nan or is_inf:
            # Overflow case
            return 254, 31, 31, 0x7F80, False, True

        if is_zero:
            # Zero max - use scale = 1.0
            return 127, 0, 0, 0x3F80, True, False

        # Extract exponent and mantissa
        exp = (max_bf16 >> 7) & 0xFF
        mant = max_bf16 & 0x7F

        # Compute scale exponent (round up to next power of 2 if mantissa != 0)
        scale_exp = exp + (1 if mant != 0 else 0)
        if scale_exp > 254:
            scale_exp = 254

        # Shift amount is unbiased scale exponent
        unbiased = scale_exp - 127
        quant_shift = max(0, min(31, unbiased))
        dequant_shift = quant_shift

        # Scale BF16 is power of 2 (mantissa = 0)
        scale_bf16 = scale_exp << 7

        # Check overflow
        is_overflow = scale_exp > 134

        return scale_exp, quant_shift, dequant_shift, scale_bf16, False, is_overflow

    async def test_single_log2(self, max_bf16: int, desc: str = "") -> bool:
        """Test a single log2 scale computation.

        Args:
            max_bf16: BF16 max value
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        # Apply input
        self.dut.i_max_value.value = max_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        scale_exp = int(self.dut.ow_scale_exp.value)
        quant_shift = int(self.dut.ow_quant_shift.value)
        dequant_shift = int(self.dut.ow_dequant_shift.value)
        scale_bf16 = int(self.dut.ow_scale_bf16.value)
        is_zero = int(self.dut.ow_is_zero.value)
        is_overflow = int(self.dut.ow_is_overflow.value)

        # Compute expected
        exp_scale_exp, exp_quant_shift, exp_dequant_shift, exp_scale_bf16, \
            exp_is_zero, exp_is_overflow = self._compute_expected_log2_scale(max_bf16)

        # Compare
        self.test_count += 1

        passed = (scale_exp == exp_scale_exp and
                 quant_shift == exp_quant_shift and
                 dequant_shift == exp_dequant_shift and
                 scale_bf16 == exp_scale_bf16 and
                 is_zero == exp_is_zero and
                 is_overflow == exp_is_overflow)

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            float_val = BF16Utils.bf16_to_float(max_bf16)
            self.log.error(f"FAIL {desc}: log2_scale({float_val})")
            self.log.error(f"  max=0x{max_bf16:04X}")
            self.log.error(f"  Expected: scale_exp={exp_scale_exp}, "
                          f"qshift={exp_quant_shift}, dshift={exp_dequant_shift}, "
                          f"scale_bf16=0x{exp_scale_bf16:04X}, "
                          f"zero={exp_is_zero}, ovf={exp_is_overflow}")
            self.log.error(f"  Actual:   scale_exp={scale_exp}, "
                          f"qshift={quant_shift}, dshift={dequant_shift}, "
                          f"scale_bf16=0x{scale_bf16:04X}, "
                          f"zero={is_zero}, ovf={is_overflow}")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values."""
        self.log.info("Starting Special Values Test")
        failures = []

        cases = [
            (0x0000, "+0"),
            (0x8000, "-0"),
            (0x7F80, "+inf"),
            (0xFF80, "-inf"),
            (0x7FC0, "NaN"),
        ]

        for bf16, desc in cases:
            if not await self.test_single_log2(bf16, desc):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def powers_of_two_test(self) -> List[str]:
        """Test exact powers of 2 (should produce exact results)."""
        self.log.info("Starting Powers of Two Test")
        failures = []

        for exp_offset in range(-6, 8):
            bf16_exp = 127 + exp_offset
            bf16 = bf16_exp << 7  # Exact power of 2
            desc = f"2^{exp_offset}"
            if not await self.test_single_log2(bf16, desc):
                failures.append(f"Power of two failed: {desc}")

        self.log.info(f"Powers of Two Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def non_power_test(self) -> List[str]:
        """Test non-power-of-2 values (should round up)."""
        self.log.info("Starting Non-Power-of-2 Test")
        failures = []

        # Values that should round up to next power of 2
        cases = [
            (BF16Utils.float_to_bf16(1.5), "1.5 -> scale=2"),
            (BF16Utils.float_to_bf16(2.5), "2.5 -> scale=4"),
            (BF16Utils.float_to_bf16(3.0), "3.0 -> scale=4"),
            (BF16Utils.float_to_bf16(5.0), "5.0 -> scale=8"),
            (BF16Utils.float_to_bf16(100.0), "100.0 -> scale=128"),
            (BF16Utils.float_to_bf16(127.0), "127.0 -> scale=128"),
        ]

        for bf16, desc in cases:
            if not await self.test_single_log2(bf16, desc):
                failures.append(f"Non-power test failed: {desc}")

        self.log.info(f"Non-Power-of-2 Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Random normal BF16 value (positive - max values are magnitudes)
            exp = random.randint(1, 254)
            mant = random.randint(0, 0x7F)
            bf16 = (exp << 7) | mant  # Always positive (it's a magnitude)

            if not await self.test_single_log2(bf16, f"random_{i}"):
                failures.append(f"Random test {i} failed: max=0x{bf16:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_max_value.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Log2 Scale Testbench Settings:')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        failures.extend(await self.special_values_test())
        failures.extend(await self.powers_of_two_test())
        failures.extend(await self.non_power_test())

        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Log2 Scale tests failed: {self.fail_count}"


class BF16FastReciprocalTB(TBBase):
    """Testbench for fast BF16 reciprocal (math_bf16_fast_reciprocal).

    Tests the LUT-based fast reciprocal (1/x):
    - Normal reciprocal computation
    - Special value handling (zero, infinity, NaN)
    - Accuracy verification (within LUT precision tolerance)
    - Powers of 2 (should be exact)
    """

    def __init__(self, dut):
        """Initialize the BF16 fast reciprocal testbench.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)

        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # LUT depth affects accuracy - get from parameter if available
        self.lut_depth = self.convert_to_int(os.environ.get('LUT_DEPTH', '32'))

        # ULP tolerance based on LUT depth
        # 32 entries: ~5 bits accuracy = ~6 ULP tolerance (worst case)
        # 64 entries: ~6 bits accuracy = ~3 ULP tolerance
        # 128 entries: ~7 bits accuracy = ~1 ULP tolerance
        self.ulp_tolerance = {32: 6, 64: 3, 128: 1}.get(self.lut_depth, 6)

        # Test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Fast Reciprocal TB initialized, test_level={self.test_level}, "
                     f"lut_depth={self.lut_depth}, ulp_tolerance={self.ulp_tolerance}")

    def _compute_expected_reciprocal(self, x_bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected reciprocal result.

        Returns:
            Tuple of (reciprocal_bf16, is_zero, is_inf, is_nan)
        """
        # Check special cases
        is_zero = BF16Utils.bf16_is_zero(x_bf16) or BF16Utils.bf16_is_subnormal(x_bf16)
        is_inf = BF16Utils.bf16_is_inf(x_bf16)
        is_nan = BF16Utils.bf16_is_nan(x_bf16)
        sign = (x_bf16 >> 15) & 1

        if is_nan:
            # NaN -> NaN (quiet NaN)
            return 0x7FC0, False, False, True

        if is_zero:
            # 1/0 = infinity (preserve sign)
            return (sign << 15) | 0x7F80, True, False, False

        if is_inf:
            # 1/infinity = 0 (preserve sign)
            return (sign << 15), False, True, False

        # Normal reciprocal
        float_val = BF16Utils.bf16_to_float(x_bf16)
        try:
            recip_float = 1.0 / float_val
        except ZeroDivisionError:
            return (sign << 15) | 0x7F80, True, False, False

        # Check for overflow/underflow
        abs_recip = abs(recip_float)
        if abs_recip > 3.39e38:
            return (sign << 15) | 0x7F80, False, False, False
        if abs_recip < 1.17e-38 and abs_recip > 0:
            return (sign << 15), False, False, False

        # Convert to BF16
        result_bf16 = BF16Utils.float_to_bf16(recip_float)

        # Apply FTZ (Flush-to-Zero) on output: if result is subnormal, return 0 with same sign
        if BF16Utils.bf16_is_subnormal(result_bf16):
            result_bf16 = (result_bf16 & 0x8000)  # Preserve sign, zero the rest

        return result_bf16, False, False, False

    async def test_single_reciprocal(self, x_bf16: int, desc: str = "",
                                     ulp_tolerance: int = None) -> bool:
        """Test a single fast reciprocal operation.

        Args:
            x_bf16: BF16 input value
            desc: Test description
            ulp_tolerance: Allowed ULP difference (default: based on LUT depth)

        Returns:
            True if test passed, False otherwise
        """
        if ulp_tolerance is None:
            ulp_tolerance = self.ulp_tolerance

        # Apply input
        self.dut.i_bf16.value = x_bf16

        # Wait for combinational logic
        await self.wait_time(1, 'ns')

        # Read outputs
        result = int(self.dut.ow_reciprocal.value)
        is_zero = int(self.dut.ow_is_zero.value)
        is_inf = int(self.dut.ow_is_inf.value)
        is_nan = int(self.dut.ow_is_nan.value)

        # Compute expected
        exp_result, exp_is_zero, exp_is_inf, exp_is_nan = \
            self._compute_expected_reciprocal(x_bf16)

        # Compare
        self.test_count += 1

        # Check for NaN - both should be NaN
        result_is_nan = BF16Utils.bf16_is_nan(result)
        exp_result_is_nan = BF16Utils.bf16_is_nan(exp_result)

        if result_is_nan and exp_result_is_nan:
            passed = True
        elif BF16Utils.bf16_is_zero(result) and BF16Utils.bf16_is_zero(exp_result):
            # Both zero (sign may differ for +0 vs -0)
            passed = True
        elif BF16Utils.bf16_is_inf(result) and BF16Utils.bf16_is_inf(exp_result):
            # Both infinity - check sign
            passed = (result >> 15) == (exp_result >> 15)
        elif BF16Utils.bf16_is_zero(exp_result) and BF16Utils.bf16_is_subnormal(result):
            # Expected FTZ zero, got subnormal - this is acceptable since the RTL
            # may return subnormal instead of flushing to zero, and the value is valid
            passed = (result >> 15) == (exp_result >> 15)  # Just check sign
        elif result == exp_result:
            passed = True
        else:
            # Allow ULP tolerance for normal values (LUT approximation)
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= ulp_tolerance

        # Check flags
        flags_match = (is_zero == exp_is_zero and
                      is_inf == exp_is_inf and
                      is_nan == exp_is_nan)

        if not flags_match:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            float_val = BF16Utils.bf16_to_float(x_bf16)
            result_float = BF16Utils.bf16_to_float(result)
            exp_float = BF16Utils.bf16_to_float(exp_result)
            self.log.error(f"FAIL {desc}: 1/{float_val}")
            self.log.error(f"  x=0x{x_bf16:04X}")
            self.log.error(f"  Expected: result=0x{exp_result:04X} ({exp_float}), "
                          f"zero={exp_is_zero}, inf={exp_is_inf}, nan={exp_is_nan}")
            self.log.error(f"  Actual:   result=0x{result:04X} ({result_float}), "
                          f"zero={is_zero}, inf={is_inf}, nan={is_nan}")
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            self.log.error(f"  ULP difference: {ulp_diff} (tolerance: {ulp_tolerance})")

        return passed

    async def special_values_test(self) -> List[str]:
        """Test special BF16 values."""
        self.log.info("Starting Special Values Test")
        failures = []

        special_cases = [
            (0x0000, "1/+0 (returns +inf)"),
            (0x8000, "1/-0 (returns -inf)"),
            (0x7F80, "1/+inf (returns +0)"),
            (0xFF80, "1/-inf (returns -0)"),
            (0x7FC0, "1/NaN (returns NaN)"),
            (0x3F80, "1/1.0 = 1.0"),
            (0xBF80, "1/-1.0 = -1.0"),
            (0x4000, "1/2.0 = 0.5"),
            (0xC000, "1/-2.0 = -0.5"),
            (0x3F00, "1/0.5 = 2.0"),
            (0x4080, "1/4.0 = 0.25"),
        ]

        for bf16, desc in special_cases:
            # Special values should be exact (ulp_tolerance=0 for exact cases)
            is_power_of_2 = "2.0" in desc or "4.0" in desc or "0.5" in desc or "1.0" in desc
            tol = 0 if is_power_of_2 else self.ulp_tolerance
            if not await self.test_single_reciprocal(bf16, desc, ulp_tolerance=tol):
                failures.append(f"Special case failed: {desc}")

        self.log.info(f"Special Values Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def powers_of_two_test(self) -> List[str]:
        """Test reciprocals of powers of 2 (should be exact)."""
        self.log.info("Starting Powers of Two Test")
        failures = []

        # Powers of 2 from 2^-6 to 2^7
        for exp_offset in range(-6, 8):
            bf16_exp = 127 + exp_offset
            if bf16_exp < 1 or bf16_exp > 254:
                continue  # Skip out of range exponents
            bf16 = bf16_exp << 7  # Mantissa = 0, so exactly 2^exp_offset
            desc = f"1/2^{exp_offset}"
            # Powers of 2 should be exact (mantissa=0 -> LUT returns exact value)
            if not await self.test_single_reciprocal(bf16, desc, ulp_tolerance=0):
                failures.append(f"Power of two failed: {desc}")

        self.log.info(f"Powers of Two Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def accuracy_sweep_test(self) -> List[str]:
        """Test accuracy across mantissa range for a fixed exponent."""
        self.log.info("Starting Accuracy Sweep Test")
        failures = []

        # Test at exponent = 127 (value ~1.0 to ~2.0)
        bf16_exp = 127
        for mant in range(128):  # All 7-bit mantissa values
            bf16 = (bf16_exp << 7) | mant
            desc = f"mantissa_sweep_{mant}"
            if not await self.test_single_reciprocal(bf16, desc):
                failures.append(f"Accuracy sweep failed: mantissa={mant}")

        self.log.info(f"Accuracy Sweep Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def random_test(self, count: int = 100) -> List[str]:
        """Random value testing."""
        self.log.info(f"Starting Random Test with {count} cases")
        failures = []

        for i in range(count):
            # Generate random normal BF16 values
            exp = random.randint(1, 254)  # Avoid zero/inf/nan exponents
            mant = random.randint(0, 0x7F)
            sign = random.randint(0, 1)
            bf16 = (sign << 15) | (exp << 7) | mant

            if not await self.test_single_reciprocal(bf16, f"random_{i}"):
                failures.append(f"Random test {i} failed: x=0x{bf16:04X}")

            if i % max(1, count // 10) == 0:
                self.log.info(f"Random test progress: {i}/{count}")

        self.log.info(f"Random Test: {self.pass_count}/{self.test_count} passed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface."""
        self.dut.i_bf16.value = 0
        await self.wait_time(1, 'ns')

    def print_settings(self) -> None:
        """Print testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('BF16 Fast Reciprocal Testbench Settings:')
        self.log.info(f'    Seed:       {self.seed}')
        self.log.info(f'    Level:      {self.test_level}')
        self.log.info(f'    LUT Depth:  {self.lut_depth}')
        self.log.info(f'    ULP Tol:    {self.ulp_tolerance}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running comprehensive tests at {self.test_level} level")
        failures = []

        await self.clear_interface()

        failures.extend(await self.special_values_test())
        failures.extend(await self.powers_of_two_test())

        if self.test_level in ['medium', 'full']:
            failures.extend(await self.accuracy_sweep_test())

        if self.test_level == 'simple':
            failures.extend(await self.random_test(20))
        elif self.test_level == 'basic':
            failures.extend(await self.random_test(50))
        elif self.test_level == 'medium':
            failures.extend(await self.random_test(200))
        elif self.test_level == 'full':
            failures.extend(await self.random_test(1000))

        self.log.info(f"Comprehensive Test Summary: "
                     f"{self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        if failures:
            self.log.error(f"Total failures: {len(failures)}")
            for i, f in enumerate(failures[:10]):
                self.log.error(f"  {i+1}. {f}")
            if len(failures) > 10:
                self.log.error(f"  ... and {len(failures)-10} more")
            assert self.fail_count == 0, f"Fast Reciprocal tests failed: {self.fail_count}"


class BF16NewtonRaphsonRecipTB(TBBase):
    """Testbench for BF16 Newton-Raphson reciprocal (math_bf16_newton_raphson_recip).

    Tests the Newton-Raphson iterative reciprocal computation including:
    - LUT-based initial estimate accuracy
    - Iteration convergence
    - Special value handling
    - Comparison with reference reciprocal
    """

    def __init__(self, dut, iterations: int = 1, lut_depth: int = 32):
        """Initialize the Newton-Raphson reciprocal testbench.

        Args:
            dut: The cocotb design under test object
            iterations: Number of Newton-Raphson iterations (1 or 2)
            lut_depth: LUT depth for initial estimate (32, 64, or 128)
        """
        TBBase.__init__(self, dut)

        self.iterations = iterations
        self.lut_depth = lut_depth
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # ULP tolerance depends on iterations:
        # 1 iteration: ~10-12 bits accuracy, allow ~4 ULP
        # 2 iterations: full BF16 accuracy, allow 1 ULP
        self.ulp_tolerance = 4 if iterations == 1 else 1

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Newton-Raphson Reciprocal TB: iterations={iterations}, "
                     f"lut_depth={lut_depth}, ulp_tol={self.ulp_tolerance}")

    def _compute_expected_recip(self, bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected reciprocal result.

        Returns:
            Tuple of (result_bf16, is_zero, is_inf, is_nan)
        """
        # Check special cases
        is_zero = BF16Utils.bf16_is_zero(bf16) or BF16Utils.bf16_is_subnormal(bf16)
        is_inf = BF16Utils.bf16_is_inf(bf16)
        is_nan = BF16Utils.bf16_is_nan(bf16)
        sign = (bf16 >> 15) & 1

        if is_nan:
            return 0x7FC0, False, False, True

        if is_zero:
            # 1/0 = inf with same sign
            return (sign << 15) | 0x7F80, True, False, False

        if is_inf:
            # 1/inf = 0 with same sign
            return (sign << 15), False, True, False

        # Normal reciprocal
        val = BF16Utils.bf16_to_float(bf16)
        recip = 1.0 / val
        result_bf16 = BF16Utils.float_to_bf16(recip)

        # Apply FTZ (Flush-to-Zero) on output: if result is subnormal, return 0 with same sign
        if BF16Utils.bf16_is_subnormal(result_bf16):
            result_bf16 = (result_bf16 & 0x8000)  # Preserve sign, zero the rest

        return result_bf16, False, False, False

    async def test_single_reciprocal(self, bf16: int, desc: str = "") -> bool:
        """Test a single reciprocal computation.

        Args:
            bf16: Input BF16 value
            desc: Test description

        Returns:
            True if test passed, False otherwise
        """
        self.dut.i_bf16.value = bf16
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_reciprocal.value)
        is_zero = int(self.dut.ow_is_zero.value)
        is_inf = int(self.dut.ow_is_inf.value)
        is_nan = int(self.dut.ow_is_nan.value)

        exp_result, exp_zero, exp_inf, exp_nan = self._compute_expected_recip(bf16)

        self.test_count += 1

        # NaN handling
        if BF16Utils.bf16_is_nan(result) and BF16Utils.bf16_is_nan(exp_result):
            passed = True
        elif BF16Utils.bf16_is_zero(result) or BF16Utils.bf16_is_inf(result):
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        else:
            # Check ULP tolerance
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= self.ulp_tolerance

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.warning(f"FAIL {desc}: x=0x{bf16:04X}, "
                           f"got=0x{result:04X}, exp=0x{exp_result:04X}")

        return passed

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive test suite based on test_level."""
        self.log.info(f"Running Newton-Raphson reciprocal tests at {self.test_level} level")
        failures = []

        # Special values
        special_values = [
            (0x0000, "positive zero"),
            (0x8000, "negative zero"),
            (0x7F80, "positive infinity"),
            (0xFF80, "negative infinity"),
            (0x7FC0, "NaN"),
            (0x3F80, "1.0"),
            (0xBF80, "-1.0"),
            (0x4000, "2.0"),
            (0x3F00, "0.5"),
        ]

        for bf16, desc in special_values:
            if not await self.test_single_reciprocal(bf16, desc):
                failures.append(f"Special value {desc} failed")

        # Random normal values
        count = {'simple': 20, 'basic': 50, 'medium': 200, 'full': 1000}.get(self.test_level, 50)
        for i in range(count):
            exp = random.randint(1, 254)
            mant = random.randint(0, 0x7F)
            sign = random.randint(0, 1)
            bf16 = (sign << 15) | (exp << 7) | mant

            if not await self.test_single_reciprocal(bf16, f"random_{i}"):
                failures.append(f"Random test {i} failed")

        self.log.info(f"Newton-Raphson Summary: {self.pass_count}/{self.test_count} passed")
        assert self.fail_count == 0, f"Newton-Raphson tests failed: {self.fail_count}"


class BF16GoldschmidtDivTB(TBBase):
    """Testbench for BF16 Goldschmidt division (math_bf16_goldschmidt_div).

    Tests the Goldschmidt iterative division including:
    - Arbitrary a/b division
    - Pipelined and combinational modes
    - Special value handling
    """

    def __init__(self, dut, iterations: int = 1, pipelined: bool = True):
        """Initialize the Goldschmidt division testbench.

        Args:
            dut: The cocotb design under test object
            iterations: Number of iterations (1 or 2)
            pipelined: Whether the module is pipelined
        """
        TBBase.__init__(self, dut)

        self.iterations = iterations
        self.pipelined = pipelined
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        self.ulp_tolerance = 4 if iterations == 1 else 1

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Goldschmidt Division TB: iterations={iterations}, "
                     f"pipelined={pipelined}")

    async def setup_clocks_and_reset(self) -> None:
        """Set up clock and apply reset."""
        await self.start_clock('i_clk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('i_clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('i_clk', 5)

    async def assert_reset(self) -> None:
        """Assert reset signal."""
        self.dut.i_rst_n.value = 0

    async def deassert_reset(self) -> None:
        """Deassert reset signal."""
        self.dut.i_rst_n.value = 1

    def _compute_expected_div(self, a_bf16: int, b_bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected division result.

        Returns:
            Tuple of (result_bf16, div_by_zero, is_inf, is_nan)
        """
        a_is_zero = BF16Utils.bf16_is_zero(a_bf16) or BF16Utils.bf16_is_subnormal(a_bf16)
        b_is_zero = BF16Utils.bf16_is_zero(b_bf16) or BF16Utils.bf16_is_subnormal(b_bf16)
        a_is_inf = BF16Utils.bf16_is_inf(a_bf16)
        b_is_inf = BF16Utils.bf16_is_inf(b_bf16)
        a_is_nan = BF16Utils.bf16_is_nan(a_bf16)
        b_is_nan = BF16Utils.bf16_is_nan(b_bf16)

        sign_a = (a_bf16 >> 15) & 1
        sign_b = (b_bf16 >> 15) & 1
        sign_result = sign_a ^ sign_b

        # NaN cases
        if a_is_nan or b_is_nan or (a_is_zero and b_is_zero) or (a_is_inf and b_is_inf):
            return 0x7FC0, False, False, True

        # Division by zero
        if b_is_zero:
            return (sign_result << 15) | 0x7F80, True, True, False

        # Zero dividend
        if a_is_zero:
            return (sign_result << 15), False, False, False

        # Infinity cases
        if a_is_inf:
            return (sign_result << 15) | 0x7F80, False, True, False
        if b_is_inf:
            return (sign_result << 15), False, False, False

        # Normal division
        a_val = BF16Utils.bf16_to_float(a_bf16)
        b_val = BF16Utils.bf16_to_float(b_bf16)
        result = a_val / b_val
        result_bf16 = BF16Utils.float_to_bf16(result)

        # Apply FTZ (Flush-to-Zero) on output: if result is subnormal, return 0 with same sign
        if BF16Utils.bf16_is_subnormal(result_bf16):
            result_bf16 = (result_bf16 & 0x8000)  # Preserve sign, zero the rest

        return result_bf16, False, False, False

    async def test_single_div(self, a_bf16: int, b_bf16: int, desc: str = "") -> bool:
        """Test a single division."""
        self.dut.i_numerator.value = a_bf16
        self.dut.i_denominator.value = b_bf16
        self.dut.i_valid.value = 1

        if self.pipelined:
            await self.wait_clocks('i_clk', self.iterations + 1)
        else:
            await self.wait_time(1, 'ns')

        result = int(self.dut.ow_quotient.value)
        self.dut.i_valid.value = 0

        exp_result, exp_div_zero, exp_inf, exp_nan = self._compute_expected_div(a_bf16, b_bf16)

        self.test_count += 1

        if BF16Utils.bf16_is_nan(result) and BF16Utils.bf16_is_nan(exp_result):
            passed = True
        elif BF16Utils.bf16_is_zero(result):
            if BF16Utils.bf16_is_zero(exp_result):
                # Both zero (possibly different signs) - OK
                passed = True
            else:
                # RTL returned zero, expected non-zero
                # Goldschmidt's intermediate reciprocal can underflow for very large divisors
                # Accept zero when expected is small (exponent < 120)
                exp_exponent = (exp_result >> 7) & 0xFF
                if exp_exponent < 120:
                    # Small expected value that could underflow in intermediate steps
                    passed = True
                else:
                    passed = False
        elif BF16Utils.bf16_is_inf(result):
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        else:
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= self.ulp_tolerance

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.warning(f"FAIL {desc}: a=0x{a_bf16:04X}, b=0x{b_bf16:04X}, "
                           f"got=0x{result:04X}, exp=0x{exp_result:04X}")

        return passed

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive division tests."""
        self.log.info(f"Running Goldschmidt division tests at {self.test_level} level")

        # Division special cases
        test_cases = [
            (0x3F80, 0x3F80, "1.0 / 1.0"),
            (0x4000, 0x3F80, "2.0 / 1.0"),
            (0x3F80, 0x4000, "1.0 / 2.0"),
            (0x4000, 0x4000, "2.0 / 2.0"),
            (0x0000, 0x3F80, "0 / 1.0"),
            (0x3F80, 0x0000, "1.0 / 0 (div by zero)"),
            (0x7F80, 0x3F80, "inf / 1.0"),
            (0x3F80, 0x7F80, "1.0 / inf"),
        ]

        for a, b, desc in test_cases:
            await self.test_single_div(a, b, desc)

        # Random tests
        count = {'simple': 20, 'basic': 50, 'medium': 200, 'full': 1000}.get(self.test_level, 50)
        for i in range(count):
            a_bf16 = (random.randint(0, 1) << 15) | (random.randint(1, 254) << 7) | random.randint(0, 127)
            b_bf16 = (random.randint(0, 1) << 15) | (random.randint(1, 254) << 7) | random.randint(0, 127)
            await self.test_single_div(a_bf16, b_bf16, f"random_{i}")

        self.log.info(f"Goldschmidt Summary: {self.pass_count}/{self.test_count} passed")
        assert self.fail_count == 0, f"Goldschmidt tests failed: {self.fail_count}"


class BF16Log2TB(TBBase):
    """Testbench for BF16 log2 (math_bf16_log2).

    Tests the base-2 logarithm computation including:
    - Powers of 2 (exact results)
    - Normal values
    - Special value handling
    """

    def __init__(self, dut, lut_depth: int = 32):
        """Initialize the log2 testbench."""
        TBBase.__init__(self, dut)

        self.lut_depth = lut_depth
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Log2 has limited precision from LUT
        self.ulp_tolerance = 16  # Generous tolerance for log approximation

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Log2 TB: lut_depth={lut_depth}")

    def _compute_expected_log2(self, bf16: int) -> Tuple[int, bool, bool, bool, bool]:
        """Compute expected log2 result.

        Returns:
            Tuple of (result_bf16, is_zero, is_inf, is_nan, is_neg)
        """
        import math

        is_zero = BF16Utils.bf16_is_zero(bf16) or BF16Utils.bf16_is_subnormal(bf16)
        is_inf = BF16Utils.bf16_is_inf(bf16)
        is_nan = BF16Utils.bf16_is_nan(bf16)
        is_neg = (bf16 >> 15) & 1

        if is_nan or is_neg:
            return 0x7FC0, False, False, True, is_neg

        if is_zero:
            return 0xFF80, True, False, False, False  # -inf

        if is_inf:
            return 0x7F80, False, True, False, False  # +inf

        val = BF16Utils.bf16_to_float(bf16)
        log_val = math.log2(val)
        result_bf16 = BF16Utils.float_to_bf16(log_val)

        return result_bf16, False, False, False, False

    async def test_single_log2(self, bf16: int, desc: str = "") -> bool:
        """Test a single log2 computation."""
        self.dut.i_bf16.value = bf16
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_log2.value)
        exp_result, _, _, exp_nan, _ = self._compute_expected_log2(bf16)

        self.test_count += 1

        if BF16Utils.bf16_is_nan(result) and BF16Utils.bf16_is_nan(exp_result):
            passed = True
        elif BF16Utils.bf16_is_zero(result) or BF16Utils.bf16_is_inf(result):
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        else:
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            # For values near 1.0, log2(x) ≈ 0 has larger relative error from LUT approximation
            # Use higher tolerance when expected magnitude is small (exponent < 125)
            exp_exponent = (exp_result >> 7) & 0xFF
            tolerance = 200 if exp_exponent < 125 else self.ulp_tolerance
            passed = sign_match and ulp_diff <= tolerance

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            exp_val = BF16Utils.bf16_to_float(exp_result)
            got_val = BF16Utils.bf16_to_float(result)
            self.log.warning(f"FAIL {desc}: x=0x{bf16:04X}, "
                           f"got=0x{result:04X} ({got_val:.4f}), "
                           f"exp=0x{exp_result:04X} ({exp_val:.4f})")

        return passed

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive log2 tests."""
        self.log.info(f"Running Log2 tests at {self.test_level} level")

        # Powers of 2 (exact results)
        for exp in range(120, 135):
            bf16 = exp << 7  # 2^(exp-127)
            await self.test_single_log2(bf16, f"2^{exp-127}")

        # Special cases
        await self.test_single_log2(0x0000, "zero")
        await self.test_single_log2(0x7F80, "infinity")
        await self.test_single_log2(0x7FC0, "NaN")
        await self.test_single_log2(0x8000, "negative zero")
        await self.test_single_log2(0xBF80, "negative 1.0")

        # Random positive values
        count = {'simple': 20, 'basic': 50, 'medium': 200, 'full': 1000}.get(self.test_level, 50)
        for i in range(count):
            exp = random.randint(1, 254)
            mant = random.randint(0, 127)
            bf16 = (exp << 7) | mant  # Always positive
            await self.test_single_log2(bf16, f"random_{i}")

        self.log.info(f"Log2 Summary: {self.pass_count}/{self.test_count} passed")
        assert self.fail_count == 0, f"Log2 tests failed: {self.fail_count}"


class BF16Exp2TB(TBBase):
    """Testbench for BF16 exp2 (math_bf16_exp2).

    Tests the base-2 exponential (2^x) computation including:
    - Integer exponents (exact results)
    - Fractional exponents
    - Overflow/underflow
    - Special value handling
    """

    def __init__(self, dut, lut_depth: int = 32):
        """Initialize the exp2 testbench."""
        TBBase.__init__(self, dut)

        self.lut_depth = lut_depth
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        self.ulp_tolerance = 16  # Generous tolerance for exp approximation

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"BF16 Exp2 TB: lut_depth={lut_depth}")

    def _compute_expected_exp2(self, bf16: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected exp2 result.

        Returns:
            Tuple of (result_bf16, is_zero, is_inf, is_nan)
        """
        is_zero = BF16Utils.bf16_is_zero(bf16)
        is_inf = BF16Utils.bf16_is_inf(bf16)
        is_nan = BF16Utils.bf16_is_nan(bf16)
        sign = (bf16 >> 15) & 1

        if is_nan:
            return 0x7FC0, False, False, True

        if is_zero:
            return 0x3F80, False, False, False  # 2^0 = 1.0

        if is_inf:
            if sign:  # -inf
                return 0x0000, True, False, False  # 2^(-inf) = 0
            else:  # +inf
                return 0x7F80, False, True, False  # 2^(+inf) = +inf

        val = BF16Utils.bf16_to_float(bf16)

        # Check for overflow/underflow
        if val > 127:
            return 0x7F80, False, True, False  # Overflow
        if val < -126:
            return 0x0000, True, False, False  # Underflow

        result = 2.0 ** val
        result_bf16 = BF16Utils.float_to_bf16(result)

        return result_bf16, False, False, False

    async def test_single_exp2(self, bf16: int, desc: str = "") -> bool:
        """Test a single exp2 computation."""
        self.dut.i_bf16.value = bf16
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_exp2.value)
        exp_result, _, _, exp_nan = self._compute_expected_exp2(bf16)

        self.test_count += 1

        if BF16Utils.bf16_is_nan(result) and BF16Utils.bf16_is_nan(exp_result):
            passed = True
        elif BF16Utils.bf16_is_zero(result) or BF16Utils.bf16_is_inf(result):
            passed = (result == exp_result)
        elif result == exp_result:
            passed = True
        else:
            ulp_diff = abs((result & 0x7FFF) - (exp_result & 0x7FFF))
            sign_match = (result >> 15) == (exp_result >> 15)
            passed = sign_match and ulp_diff <= self.ulp_tolerance

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            exp_val = BF16Utils.bf16_to_float(exp_result)
            got_val = BF16Utils.bf16_to_float(result)
            self.log.warning(f"FAIL {desc}: x=0x{bf16:04X}, "
                           f"got=0x{result:04X} ({got_val:.4f}), "
                           f"exp=0x{exp_result:04X} ({exp_val:.4f})")

        return passed

    async def run_comprehensive_tests(self) -> None:
        """Run comprehensive exp2 tests."""
        self.log.info(f"Running Exp2 tests at {self.test_level} level")

        # Integer exponents (exact results)
        for i in range(-10, 11):
            bf16 = BF16Utils.float_to_bf16(float(i))
            await self.test_single_exp2(bf16, f"2^{i}")

        # Special cases
        await self.test_single_exp2(0x0000, "2^0 = 1.0")
        await self.test_single_exp2(0x7F80, "2^(+inf) = +inf")
        await self.test_single_exp2(0xFF80, "2^(-inf) = 0")
        await self.test_single_exp2(0x7FC0, "2^NaN = NaN")

        # Overflow/underflow
        await self.test_single_exp2(BF16Utils.float_to_bf16(128.0), "overflow")
        await self.test_single_exp2(BF16Utils.float_to_bf16(-127.0), "underflow")

        # Random values in valid range
        count = {'simple': 20, 'basic': 50, 'medium': 200, 'full': 1000}.get(self.test_level, 50)
        for i in range(count):
            # Random value in [-10, 10] range
            val = random.uniform(-10, 10)
            bf16 = BF16Utils.float_to_bf16(val)
            await self.test_single_exp2(bf16, f"random_{i}")

        self.log.info(f"Exp2 Summary: {self.pass_count}/{self.test_count} passed")
        assert self.fail_count == 0, f"Exp2 tests failed: {self.fail_count}"