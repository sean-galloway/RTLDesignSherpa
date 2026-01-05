# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FPTesting
# Purpose: IEEE 754 Floating-Point Testing Module for FP32, FP16, FP8 E4M3, FP8 E5M2
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-01-02

"""IEEE 754 Floating-Point Testing Module

This module provides testbenches for IEEE 754 floating-point arithmetic units.
Supports testing of:
- FP32 (single precision): 1 sign, 8 exp (bias=127), 23 mantissa
- FP16 (half precision): 1 sign, 5 exp (bias=15), 10 mantissa
- FP8 E4M3 (ML format): 1 sign, 4 exp (bias=7), 3 mantissa, no infinity
- FP8 E5M2 (ML format): 1 sign, 5 exp (bias=15), 2 mantissa

Operations:
- Arithmetic: Multiplier, Adder, FMA
- Conversions: Between all format pairs
- Activations: ReLU, Leaky ReLU, Sigmoid, Tanh, GELU, SiLU, Softmax
- Comparisons: Comparator, Max, Min, Clamp, Max/Min Tree
"""
import os
import random
import struct
import math
from typing import List, Tuple, Dict, Any, Optional
from dataclasses import dataclass
from enum import Enum

from cocotb.triggers import Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


# =============================================================================
# Format Definitions
# =============================================================================

@dataclass
class FPFormat:
    """Floating-point format specification."""
    name: str
    bits: int
    exp_bits: int
    mant_bits: int
    bias: int
    has_infinity: bool  # FP8 E4M3 uses exp=15, mant=7 as NaN (no infinity)

    @property
    def exp_max(self) -> int:
        return (1 << self.exp_bits) - 1

    @property
    def mant_max(self) -> int:
        return (1 << self.mant_bits) - 1


# Standard format definitions
FP32 = FPFormat('fp32', 32, 8, 23, 127, True)
FP16 = FPFormat('fp16', 16, 5, 10, 15, True)
BF16 = FPFormat('bf16', 16, 8, 7, 127, True)
FP8_E4M3 = FPFormat('fp8_e4m3', 8, 4, 3, 7, False)
FP8_E5M2 = FPFormat('fp8_e5m2', 8, 5, 2, 15, True)

FORMATS = {
    'fp32': FP32,
    'fp16': FP16,
    'bf16': BF16,
    'fp8_e4m3': FP8_E4M3,
    'fp8_e5m2': FP8_E5M2,
}


# =============================================================================
# FP Utilities - Generic for all formats
# =============================================================================

class FPUtils:
    """Utility class for IEEE 754 floating-point operations."""

    @staticmethod
    def float_to_fp32(f: float) -> int:
        """Convert Python float to FP32 bit representation."""
        if f != f:  # NaN
            return 0x7FC00000
        if f == float('inf'):
            return 0x7F800000
        if f == float('-inf'):
            return 0xFF800000
        try:
            fp32_bytes = struct.pack('>f', f)
        except OverflowError:
            return 0xFF800000 if f < 0 else 0x7F800000
        return struct.unpack('>I', fp32_bytes)[0]

    @staticmethod
    def fp32_to_float(fp32: int) -> float:
        """Convert FP32 bit representation to Python float."""
        fp32_bytes = struct.pack('>I', fp32 & 0xFFFFFFFF)
        return struct.unpack('>f', fp32_bytes)[0]

    @staticmethod
    def float_to_fp16(f: float) -> int:
        """Convert Python float to FP16 bit representation with RNE rounding."""
        if f != f:  # NaN
            return 0x7E00  # Canonical qNaN
        if f == float('inf'):
            return 0x7C00
        if f == float('-inf'):
            return 0xFC00

        # Convert to FP32 first
        fp32 = FPUtils.float_to_fp32(f)
        sign = (fp32 >> 31) & 1
        exp = (fp32 >> 23) & 0xFF
        mant = fp32 & 0x7FFFFF

        if exp == 0xFF:  # Inf or NaN in FP32
            if mant == 0:
                return (sign << 15) | 0x7C00
            else:
                return (sign << 15) | 0x7E00

        # Rebias exponent: FP32 bias=127, FP16 bias=15
        new_exp = exp - 127 + 15

        if new_exp >= 31:  # Overflow -> infinity
            return (sign << 15) | 0x7C00
        elif new_exp <= 0:  # Underflow -> zero (FTZ)
            return sign << 15

        # Round mantissa from 23 to 10 bits (RNE)
        shift = 13
        round_bit = (mant >> (shift - 1)) & 1
        sticky = (mant & ((1 << (shift - 1)) - 1)) != 0
        mant16 = mant >> shift

        # RNE rounding
        if round_bit and (sticky or (mant16 & 1)):
            mant16 += 1
            if mant16 >= 0x400:  # Mantissa overflow
                mant16 = 0
                new_exp += 1
                if new_exp >= 31:
                    return (sign << 15) | 0x7C00

        return (sign << 15) | (new_exp << 10) | (mant16 & 0x3FF)

    @staticmethod
    def fp16_to_float(fp16: int) -> float:
        """Convert FP16 bit representation to Python float."""
        sign = (fp16 >> 15) & 1
        exp = (fp16 >> 10) & 0x1F
        mant = fp16 & 0x3FF

        if exp == 0x1F:
            if mant == 0:
                return float('-inf') if sign else float('inf')
            else:
                return float('nan')
        if exp == 0:
            if mant == 0:
                return -0.0 if sign else 0.0
            # Subnormal -> flush to zero
            return -0.0 if sign else 0.0

        # Normal: convert to FP32
        fp32_exp = exp - 15 + 127
        fp32_mant = mant << 13
        fp32 = (sign << 31) | (fp32_exp << 23) | fp32_mant
        return FPUtils.fp32_to_float(fp32)

    @staticmethod
    def float_to_fp8_e4m3(f: float) -> int:
        """Convert Python float to FP8 E4M3 bit representation.

        E4M3 format: 1 sign, 4 exponent (bias=7), 3 mantissa
        - NO infinity representation
        - exp=15, mant=7 is NaN
        - exp=15, mant=0-6 are valid max normals (256 to 448)
        - Max representable value: (1 + 6/8) * 2^8 = 1.75 * 256 = 448
        """
        if f != f:  # NaN
            return 0x7F  # E4M3 NaN: exp=15, mant=7

        # E4M3 max normal is 448.0 (exp=15, mant=6)
        # Values > 448 saturate to max normal
        if abs(f) > 448.0:
            sign = 1 if f < 0 else 0
            return (sign << 7) | 0x7E  # Max normal (exp=15, mant=6)

        sign = 1 if f < 0 else 0
        f = abs(f)

        if f == 0:
            return sign << 7

        # Get exponent and mantissa
        if f < 2**-6:  # Min normal is 2^(1-7) = 2^-6
            return sign << 7  # Underflow to zero (FTZ)

        exp_unbiased = int(math.floor(math.log2(f)))
        exp = exp_unbiased + 7  # bias=7

        if exp <= 0:
            return sign << 7  # Underflow

        # Mantissa: f = (1 + m/8) * 2^exp_unbiased
        mant_float = f / (2 ** exp_unbiased) - 1.0
        mant = int(round(mant_float * 8))  # 3-bit mantissa with RNE

        # Handle mantissa overflow from rounding
        if mant >= 8:
            mant = 0
            exp += 1

        # Handle exponent overflow (exp > 15 or exp=15 with mant=7 which is NaN)
        if exp > 15:
            return (sign << 7) | 0x7E  # Saturate to max normal
        if exp == 15 and mant >= 7:
            # mant=7 at exp=15 is NaN pattern, saturate to mant=6
            return (sign << 7) | 0x7E  # Max normal (exp=15, mant=6)

        return (sign << 7) | (exp << 3) | (mant & 0x7)

    @staticmethod
    def fp8_e4m3_to_float(fp8: int) -> float:
        """Convert FP8 E4M3 bit representation to Python float."""
        sign = (fp8 >> 7) & 1
        exp = (fp8 >> 3) & 0xF
        mant = fp8 & 0x7

        if exp == 15 and mant == 7:
            return float('nan')
        if exp == 0:
            if mant == 0:
                return -0.0 if sign else 0.0
            return -0.0 if sign else 0.0  # FTZ

        # Normal
        value = (1.0 + mant / 8.0) * (2 ** (exp - 7))
        return -value if sign else value

    @staticmethod
    def float_to_fp8_e5m2(f: float) -> int:
        """Convert Python float to FP8 E5M2 bit representation."""
        if f != f:  # NaN
            return 0x7F  # Canonical NaN
        if f == float('inf'):
            return 0x7C
        if f == float('-inf'):
            return 0xFC

        sign = 1 if f < 0 else 0
        f = abs(f)

        if f == 0:
            return sign << 7

        # Max normal: (1 + 3/4) * 2^15 = 57344
        # Overflow threshold: max + ULP/2 = 57344 + 4096 = 61440
        if f > 61440:
            return (sign << 7) | 0x7C  # Infinity

        if f < 2**-14:  # Min normal is 2^(1-15) = 2^-14
            return sign << 7  # Underflow

        exp_unbiased = int(math.floor(math.log2(f)))
        exp = exp_unbiased + 15  # bias=15

        if exp >= 31:
            return (sign << 7) | 0x7C
        if exp <= 0:
            return sign << 7

        # Mantissa: 2-bit
        mant_float = f / (2 ** exp_unbiased) - 1.0
        mant = int(round(mant_float * 4))
        if mant >= 4:
            mant = 0
            exp += 1
            if exp >= 31:
                return (sign << 7) | 0x7C

        return (sign << 7) | (exp << 2) | (mant & 0x3)

    @staticmethod
    def fp8_e5m2_to_float(fp8: int) -> float:
        """Convert FP8 E5M2 bit representation to Python float."""
        sign = (fp8 >> 7) & 1
        exp = (fp8 >> 2) & 0x1F
        mant = fp8 & 0x3

        if exp == 31:
            if mant == 0:
                return float('-inf') if sign else float('inf')
            else:
                return float('nan')
        if exp == 0:
            if mant == 0:
                return -0.0 if sign else 0.0
            return -0.0 if sign else 0.0  # FTZ

        # Normal
        value = (1.0 + mant / 4.0) * (2 ** (exp - 15))
        return -value if sign else value

    @staticmethod
    def convert_float(f: float, fmt: FPFormat) -> int:
        """Convert Python float to specified format."""
        if fmt.name == 'fp32':
            return FPUtils.float_to_fp32(f)
        elif fmt.name == 'fp16':
            return FPUtils.float_to_fp16(f)
        elif fmt.name == 'bf16':
            # BF16 is upper 16 bits of FP32 with RNE rounding
            fp32 = FPUtils.float_to_fp32(f)
            # Handle special cases first
            exp = (fp32 >> 23) & 0xFF
            if exp == 0xFF:  # Inf or NaN
                return (fp32 >> 16) & 0xFFFF
            # Apply RNE rounding
            # Round bit is bit 15, sticky is bits 14-0
            round_bit = (fp32 >> 15) & 1
            sticky = (fp32 & 0x7FFF) != 0
            bf16 = (fp32 >> 16) & 0xFFFF
            # RNE: round up if round=1 and (sticky=1 or lsb=1)
            if round_bit and (sticky or (bf16 & 1)):
                bf16 += 1
                # Check for mantissa overflow -> infinity
                if (bf16 & 0x7F80) == 0x7F80:  # exp became 0xFF
                    bf16 = (bf16 & 0x8000) | 0x7F80  # Set to infinity
            return bf16
        elif fmt.name == 'fp8_e4m3':
            return FPUtils.float_to_fp8_e4m3(f)
        elif fmt.name == 'fp8_e5m2':
            return FPUtils.float_to_fp8_e5m2(f)
        else:
            raise ValueError(f"Unknown format: {fmt.name}")

    @staticmethod
    def to_float(bits: int, fmt: FPFormat) -> float:
        """Convert bit representation to Python float."""
        if fmt.name == 'fp32':
            return FPUtils.fp32_to_float(bits)
        elif fmt.name == 'fp16':
            return FPUtils.fp16_to_float(bits)
        elif fmt.name == 'bf16':
            # BF16: 1 sign, 8 exp, 7 mant
            sign = (bits >> 15) & 1
            exp = (bits >> 7) & 0xFF
            mant = bits & 0x7F
            # Handle subnormals with FTZ (flush to zero)
            if exp == 0:
                return -0.0 if sign else 0.0
            # Handle infinity and NaN
            if exp == 0xFF:
                if mant == 0:
                    return float('-inf') if sign else float('inf')
                else:
                    return float('nan')
            # Normal: extend to FP32
            fp32 = (bits & 0xFFFF) << 16
            return FPUtils.fp32_to_float(fp32)
        elif fmt.name == 'fp8_e4m3':
            return FPUtils.fp8_e4m3_to_float(bits)
        elif fmt.name == 'fp8_e5m2':
            return FPUtils.fp8_e5m2_to_float(bits)
        else:
            raise ValueError(f"Unknown format: {fmt.name}")

    @staticmethod
    def is_zero(bits: int, fmt: FPFormat) -> bool:
        """Check if value is zero (positive or negative)."""
        mask = (1 << (fmt.bits - 1)) - 1  # All bits except sign
        return (bits & mask) == 0

    @staticmethod
    def is_subnormal(bits: int, fmt: FPFormat) -> bool:
        """Check if value is subnormal."""
        exp_mask = ((1 << fmt.exp_bits) - 1) << fmt.mant_bits
        mant_mask = (1 << fmt.mant_bits) - 1
        exp = (bits & exp_mask) >> fmt.mant_bits
        mant = bits & mant_mask
        return exp == 0 and mant != 0

    @staticmethod
    def apply_ftz(bits: int, fmt: FPFormat) -> int:
        """Apply Flush-To-Zero: convert subnormal to signed zero."""
        if FPUtils.is_subnormal(bits, fmt):
            sign = (bits >> (fmt.bits - 1)) & 1
            return sign << (fmt.bits - 1)  # Signed zero
        return bits

    @staticmethod
    def is_inf(bits: int, fmt: FPFormat) -> bool:
        """Check if value is infinity."""
        if not fmt.has_infinity:
            return False
        exp_mask = ((1 << fmt.exp_bits) - 1) << fmt.mant_bits
        mant_mask = (1 << fmt.mant_bits) - 1
        exp = (bits & exp_mask) >> fmt.mant_bits
        mant = bits & mant_mask
        return exp == fmt.exp_max and mant == 0

    @staticmethod
    def is_nan(bits: int, fmt: FPFormat) -> bool:
        """Check if value is NaN."""
        exp_mask = ((1 << fmt.exp_bits) - 1) << fmt.mant_bits
        mant_mask = (1 << fmt.mant_bits) - 1
        exp = (bits & exp_mask) >> fmt.mant_bits
        mant = bits & mant_mask

        if fmt.has_infinity:
            return exp == fmt.exp_max and mant != 0
        else:
            # FP8 E4M3: NaN is exp=15, mant=7
            return exp == fmt.exp_max and mant == fmt.mant_max

    @staticmethod
    def get_fields(bits: int, fmt: FPFormat) -> Tuple[int, int, int]:
        """Extract (sign, exponent, mantissa) fields."""
        sign = (bits >> (fmt.bits - 1)) & 1
        exp_mask = (1 << fmt.exp_bits) - 1
        mant_mask = (1 << fmt.mant_bits) - 1
        exp = (bits >> fmt.mant_bits) & exp_mask
        mant = bits & mant_mask
        return sign, exp, mant

    @staticmethod
    def to_float_exact(bits: int, fmt: FPFormat) -> float:
        """Convert bit representation to Python float WITHOUT flush-to-zero.

        Use this for comparison operations where subnormals should be
        compared by their actual values, not flushed to zero.
        """
        sign, exp, mant = FPUtils.get_fields(bits, fmt)

        # Handle special cases
        if exp == fmt.exp_max:
            if fmt.has_infinity:
                if mant == 0:
                    return float('-inf') if sign else float('inf')
                else:
                    return float('nan')
            else:
                # FP8 E4M3: exp=15, mant=7 is NaN
                if mant == fmt.mant_max:
                    return float('nan')

        # Zero
        if exp == 0 and mant == 0:
            return -0.0 if sign else 0.0

        # Subnormal - compute actual value (NOT flush to zero!)
        if exp == 0:
            # Subnormal: value = (-1)^sign * 2^(1-bias) * (0.mantissa)
            # = (-1)^sign * 2^(1-bias) * (mant / 2^mant_bits)
            value = (mant / (1 << fmt.mant_bits)) * (2 ** (1 - fmt.bias))
            return -value if sign else value

        # Normal: value = (-1)^sign * 2^(exp-bias) * (1.mantissa)
        value = (1.0 + mant / (1 << fmt.mant_bits)) * (2 ** (exp - fmt.bias))
        return -value if sign else value

    @staticmethod
    def make_value(sign: int, exp: int, mant: int, fmt: FPFormat) -> int:
        """Construct value from (sign, exponent, mantissa) fields."""
        exp_mask = (1 << fmt.exp_bits) - 1
        mant_mask = (1 << fmt.mant_bits) - 1
        return ((sign & 1) << (fmt.bits - 1)) | ((exp & exp_mask) << fmt.mant_bits) | (mant & mant_mask)


# =============================================================================
# Test Value Generators
# =============================================================================

class FPTestValues:
    """Generate test values for floating-point testing."""

    @staticmethod
    def get_special_values(fmt: FPFormat) -> List[int]:
        """Get special values for a format: zeros, infinities, NaNs, subnormals."""
        values = []

        # Zeros
        values.append(0)  # +0
        values.append(1 << (fmt.bits - 1))  # -0

        # Infinities (if supported)
        if fmt.has_infinity:
            pos_inf = fmt.exp_max << fmt.mant_bits
            values.append(pos_inf)  # +inf
            values.append(pos_inf | (1 << (fmt.bits - 1)))  # -inf

        # NaN
        if fmt.has_infinity:
            nan = (fmt.exp_max << fmt.mant_bits) | 1
        else:
            # E4M3: NaN is exp=15, mant=7
            nan = (fmt.exp_max << fmt.mant_bits) | fmt.mant_max
        values.append(nan)

        # Subnormals (min positive subnormal)
        values.append(1)  # Smallest positive subnormal

        return values

    @staticmethod
    def get_normal_values(fmt: FPFormat) -> List[int]:
        """Get typical normal values: 1.0, powers of 2, max normal, min normal."""
        values = []

        # 1.0
        one = fmt.bias << fmt.mant_bits
        values.append(one)
        values.append(one | (1 << (fmt.bits - 1)))  # -1.0

        # Max normal
        max_exp = fmt.exp_max - 1 if fmt.has_infinity else fmt.exp_max - 1
        max_mant = fmt.mant_max if fmt.has_infinity else fmt.mant_max - 1
        max_normal = (max_exp << fmt.mant_bits) | max_mant
        values.append(max_normal)

        # Min normal
        min_normal = 1 << fmt.mant_bits
        values.append(min_normal)

        # Powers of 2
        for exp_offset in [-2, -1, 1, 2]:
            exp = fmt.bias + exp_offset
            if 1 <= exp < fmt.exp_max:
                values.append(exp << fmt.mant_bits)

        return values

    @staticmethod
    def get_random_values(fmt: FPFormat, count: int = 100) -> List[int]:
        """Generate random valid values."""
        values = []
        for _ in range(count):
            sign = random.randint(0, 1)
            # Random normal exponent (avoid 0 and max)
            exp = random.randint(1, fmt.exp_max - 1)
            mant = random.randint(0, fmt.mant_max)
            value = FPUtils.make_value(sign, exp, mant, fmt)
            values.append(value)
        return values

    @staticmethod
    def get_all_test_values(fmt: FPFormat, test_level: str = 'basic') -> List[int]:
        """Get all test values for a given test level."""
        values = []

        if test_level == 'simple':
            values.extend(FPTestValues.get_special_values(fmt))
            values.extend(FPTestValues.get_normal_values(fmt)[:4])
        elif test_level == 'basic':
            values.extend(FPTestValues.get_special_values(fmt))
            values.extend(FPTestValues.get_normal_values(fmt))
            values.extend(FPTestValues.get_random_values(fmt, 50))
        elif test_level == 'medium':
            values.extend(FPTestValues.get_special_values(fmt))
            values.extend(FPTestValues.get_normal_values(fmt))
            values.extend(FPTestValues.get_random_values(fmt, 200))
        elif test_level == 'full':
            values.extend(FPTestValues.get_special_values(fmt))
            values.extend(FPTestValues.get_normal_values(fmt))
            values.extend(FPTestValues.get_random_values(fmt, 1000))
        else:
            values.extend(FPTestValues.get_special_values(fmt))
            values.extend(FPTestValues.get_normal_values(fmt))

        return values


# =============================================================================
# Base Testbench for FP Modules
# =============================================================================

class FPBaseTB(TBBase):
    """Base testbench for all floating-point modules."""

    def __init__(self, dut, fmt: FPFormat):
        TBBase.__init__(self, dut)
        self.fmt = fmt
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        # Statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"{fmt.name.upper()} TB initialized, test_level={self.test_level}")

    def print_settings(self):
        """Print testbench configuration."""
        self.log.info(f"Format: {self.fmt.name}")
        self.log.info(f"Bits: {self.fmt.bits}, Exp: {self.fmt.exp_bits}, Mant: {self.fmt.mant_bits}")
        self.log.info(f"Bias: {self.fmt.bias}, Has Infinity: {self.fmt.has_infinity}")
        self.log.info(f"Test Level: {self.test_level}")
        self.log.info(f"Seed: {self.seed}")

    def format_value(self, value: int) -> str:
        """Format a value for logging."""
        float_val = FPUtils.to_float(value, self.fmt)
        return f"0x{value:0{self.fmt.bits//4}X} ({float_val})"

    def check_result(self, actual: int, expected: int, desc: str = "",
                     allow_ulp: bool = True) -> bool:
        """Check result with optional ULP tolerance."""
        self.test_count += 1

        actual_nan = FPUtils.is_nan(actual, self.fmt)
        expected_nan = FPUtils.is_nan(expected, self.fmt)

        if actual_nan and expected_nan:
            self.pass_count += 1
            return True

        actual_zero = FPUtils.is_zero(actual, self.fmt)
        expected_zero = FPUtils.is_zero(expected, self.fmt)
        actual_special = actual_zero or FPUtils.is_inf(actual, self.fmt)
        expected_special = expected_zero or FPUtils.is_inf(expected, self.fmt)

        if actual_special or expected_special:
            # Treat +0 and -0 as equivalent (common in ML workloads)
            if actual_zero and expected_zero:
                passed = True
            else:
                passed = (actual == expected)
        elif actual == expected:
            passed = True
        elif allow_ulp:
            # 1 ULP tolerance for normal values
            mask = (1 << (self.fmt.bits - 1)) - 1
            ulp_diff = abs((actual & mask) - (expected & mask))
            sign_match = (actual >> (self.fmt.bits - 1)) == (expected >> (self.fmt.bits - 1))
            passed = sign_match and ulp_diff <= 1
        else:
            passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            self.log.error(f"FAIL {desc}: got {self.format_value(actual)}, "
                          f"expected {self.format_value(expected)}")

        return passed

    def print_summary(self):
        """Print test summary."""
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, "
                     f"{self.fail_count} failed")
        if self.test_count > 0:
            rate = 100.0 * self.pass_count / self.test_count
            self.log.info(f"Pass rate: {rate:.2f}%")


# =============================================================================
# Multiplier Testbench
# =============================================================================

class FPMultiplierTB(FPBaseTB):
    """Testbench for floating-point multiplier modules."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Multiplier TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, a: int, b: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected multiplication result."""
        # Apply FTZ (Flush-To-Zero) to inputs - RTL treats subnormal inputs as zero
        a_ftz = FPUtils.apply_ftz(a, self.fmt)
        b_ftz = FPUtils.apply_ftz(b, self.fmt)

        a_float = FPUtils.to_float(a_ftz, self.fmt)
        b_float = FPUtils.to_float(b_ftz, self.fmt)

        a_is_zero = FPUtils.is_zero(a_ftz, self.fmt)
        b_is_zero = FPUtils.is_zero(b_ftz, self.fmt)
        a_is_inf = FPUtils.is_inf(a, self.fmt)
        b_is_inf = FPUtils.is_inf(b, self.fmt)
        a_is_nan = FPUtils.is_nan(a, self.fmt)
        b_is_nan = FPUtils.is_nan(b, self.fmt)

        sign_a = (a >> (self.fmt.bits - 1)) & 1
        sign_b = (b >> (self.fmt.bits - 1)) & 1
        sign_result = sign_a ^ sign_b

        invalid = (a_is_zero and b_is_inf) or (b_is_zero and a_is_inf)

        if a_is_nan or b_is_nan or invalid:
            nan = FPUtils.make_value(sign_result, self.fmt.exp_max,
                                    1 if self.fmt.has_infinity else self.fmt.mant_max, self.fmt)
            return nan, False, False, invalid

        if a_is_inf or b_is_inf:
            inf = FPUtils.make_value(sign_result, self.fmt.exp_max, 0, self.fmt)
            return inf, False, False, False

        if a_is_zero or b_is_zero:
            return sign_result << (self.fmt.bits - 1), False, False, False

        result_float = a_float * b_float
        result = FPUtils.convert_float(result_float, self.fmt)

        # Apply FTZ (Flush-To-Zero) for subnormal results
        result = FPUtils.apply_ftz(result, self.fmt)

        # Check overflow/underflow
        overflow = FPUtils.is_inf(result, self.fmt) and not (a_is_inf or b_is_inf)
        underflow = FPUtils.is_zero(result, self.fmt) and result_float != 0

        return result, overflow, underflow, False

    async def test_single(self, a: int, b: int, desc: str = "") -> bool:
        """Test a single multiplication."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected, _, _, _ = self.compute_expected(a, b)

        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info("Starting comprehensive multiplier tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        # Test all pairs from special and normal values
        for i, a in enumerate(values[:20]):  # First 20 are special/normal
            for b in values[:20]:
                await self.test_single(a, b, f"pair_{i}")

        # Test random values
        for i, a in enumerate(values[20:]):
            b = random.choice(values)
            await self.test_single(a, b, f"random_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Adder Testbench
# =============================================================================

class FPAdderTB(FPBaseTB):
    """Testbench for floating-point adder modules."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Adder TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, a: int, b: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected addition result."""
        # Apply FTZ (Flush-To-Zero) to inputs - RTL treats subnormal inputs as zero
        a_ftz = FPUtils.apply_ftz(a, self.fmt)
        b_ftz = FPUtils.apply_ftz(b, self.fmt)

        a_float = FPUtils.to_float(a_ftz, self.fmt)
        b_float = FPUtils.to_float(b_ftz, self.fmt)

        a_is_nan = FPUtils.is_nan(a, self.fmt)
        b_is_nan = FPUtils.is_nan(b, self.fmt)
        a_is_inf = FPUtils.is_inf(a, self.fmt)
        b_is_inf = FPUtils.is_inf(b, self.fmt)

        sign_a = (a >> (self.fmt.bits - 1)) & 1
        sign_b = (b >> (self.fmt.bits - 1)) & 1

        # Invalid: inf + (-inf)
        invalid = a_is_inf and b_is_inf and (sign_a != sign_b)

        if a_is_nan or b_is_nan or invalid:
            nan = FPUtils.make_value(0, self.fmt.exp_max,
                                    1 if self.fmt.has_infinity else self.fmt.mant_max, self.fmt)
            return nan, False, False, invalid

        if a_is_inf:
            return a, False, False, False
        if b_is_inf:
            return b, False, False, False

        result_float = a_float + b_float
        result = FPUtils.convert_float(result_float, self.fmt)

        # Apply FTZ (Flush-To-Zero) for subnormal results
        result = FPUtils.apply_ftz(result, self.fmt)

        overflow = FPUtils.is_inf(result, self.fmt) and not (a_is_inf or b_is_inf)
        underflow = FPUtils.is_zero(result, self.fmt) and result_float != 0

        return result, overflow, underflow, False

    async def test_single(self, a: int, b: int, desc: str = "") -> bool:
        """Test a single addition."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected, _, _, _ = self.compute_expected(a, b)

        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info("Starting comprehensive adder tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, a in enumerate(values[:20]):
            for b in values[:20]:
                await self.test_single(a, b, f"pair_{i}")

        for i, a in enumerate(values[20:]):
            b = random.choice(values)
            await self.test_single(a, b, f"random_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Comparator Testbench
# =============================================================================

class FPComparatorTB(FPBaseTB):
    """Testbench for floating-point comparator modules."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Comparator TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, a: int, b: int) -> Dict[str, bool]:
        """Compute expected comparison results."""
        a_nan = FPUtils.is_nan(a, self.fmt)
        b_nan = FPUtils.is_nan(b, self.fmt)

        if a_nan or b_nan:
            return {'eq': False, 'lt': False, 'gt': False,
                    'le': False, 'ge': False, 'ne': False, 'unord': True}

        # Use to_float_exact for comparisons - subnormals should be compared
        # by actual value, NOT flushed to zero
        a_float = FPUtils.to_float_exact(a, self.fmt)
        b_float = FPUtils.to_float_exact(b, self.fmt)

        # Handle +0 == -0
        if a_float == 0 and b_float == 0:
            return {'eq': True, 'lt': False, 'gt': False,
                    'le': True, 'ge': True, 'ne': False, 'unord': False}

        eq = a_float == b_float
        lt = a_float < b_float
        gt = a_float > b_float

        return {
            'eq': eq,
            'lt': lt,
            'gt': gt,
            'le': eq or lt,
            'ge': eq or gt,
            'ne': not eq,
            'unord': False
        }

    async def test_single(self, a: int, b: int, desc: str = "") -> bool:
        """Test a single comparison."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        await self.wait_time(1, 'ns')

        expected = self.compute_expected(a, b)

        results = {
            'eq': int(self.dut.ow_eq.value),
            'lt': int(self.dut.ow_lt.value),
            'gt': int(self.dut.ow_gt.value),
            'le': int(self.dut.ow_le.value),
            'ge': int(self.dut.ow_ge.value),
            'ne': int(self.dut.ow_ne.value),
            'unord': int(self.dut.ow_unord.value)
        }

        self.test_count += 1
        passed = True

        for key in expected:
            if results[key] != int(expected[key]):
                self.log.error(f"FAIL {desc}: {key} got {results[key]}, expected {int(expected[key])}")
                passed = False

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1

        return passed

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info("Starting comprehensive comparator tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, a in enumerate(values[:20]):
            for b in values[:20]:
                await self.test_single(a, b, f"pair_{i}")

        for i, a in enumerate(values[20:]):
            b = random.choice(values)
            await self.test_single(a, b, f"random_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Max/Min Testbench
# =============================================================================

class FPMaxMinTB(FPBaseTB):
    """Testbench for floating-point max/min modules."""

    def __init__(self, dut, fmt: FPFormat, is_max: bool = True):
        super().__init__(dut, fmt)
        self.is_max = is_max
        op = "Max" if is_max else "Min"
        self.log.info(f"FP {op} TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, a: int, b: int) -> int:
        """Compute expected max/min result."""
        a_nan = FPUtils.is_nan(a, self.fmt)
        b_nan = FPUtils.is_nan(b, self.fmt)

        # NaN handling: return non-NaN
        if a_nan:
            return b
        if b_nan:
            return a

        # Use to_float_exact for comparisons - subnormals should be compared
        # by actual value, NOT flushed to zero
        a_float = FPUtils.to_float_exact(a, self.fmt)
        b_float = FPUtils.to_float_exact(b, self.fmt)

        # Handle +0 vs -0
        if a_float == 0 and b_float == 0:
            if self.is_max:
                # max(+0, -0) = +0
                return a if (a >> (self.fmt.bits - 1)) == 0 else b
            else:
                # min(+0, -0) = -0
                return a if (a >> (self.fmt.bits - 1)) == 1 else b

        if self.is_max:
            return a if a_float >= b_float else b
        else:
            return a if a_float <= b_float else b

    async def test_single(self, a: int, b: int, desc: str = "") -> bool:
        """Test a single max/min operation."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(a, b)

        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        op = "max" if self.is_max else "min"
        self.log.info(f"Starting comprehensive {op} tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, a in enumerate(values[:20]):
            for b in values[:20]:
                await self.test_single(a, b, f"pair_{i}")

        for i, a in enumerate(values[20:]):
            b = random.choice(values)
            await self.test_single(a, b, f"random_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Clamp Testbench
# =============================================================================

class FPClampTB(FPBaseTB):
    """Testbench for floating-point clamp modules."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Clamp TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_x.value = 0
        self.dut.i_min.value = 0
        self.dut.i_max.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, x: int, min_val: int, max_val: int) -> int:
        """Compute expected clamp result."""
        x_nan = FPUtils.is_nan(x, self.fmt)
        min_nan = FPUtils.is_nan(min_val, self.fmt)
        max_nan = FPUtils.is_nan(max_val, self.fmt)

        if x_nan or min_nan or max_nan:
            return x  # Propagate NaN

        # Use to_float_exact for comparisons - subnormals should be compared
        # by actual value, NOT flushed to zero
        x_float = FPUtils.to_float_exact(x, self.fmt)
        min_float = FPUtils.to_float_exact(min_val, self.fmt)
        max_float = FPUtils.to_float_exact(max_val, self.fmt)

        if x_float < min_float:
            return min_val
        elif x_float > max_float:
            return max_val
        else:
            return x

    async def test_single(self, x: int, min_val: int, max_val: int, desc: str = "") -> bool:
        """Test a single clamp operation."""
        self.dut.i_x.value = x
        self.dut.i_min.value = min_val
        self.dut.i_max.value = max_val
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x, min_val, max_val)

        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info("Starting comprehensive clamp tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        # Create valid min/max pairs (ensure min <= max using actual float values)
        # Filter out NaN and infinity for min/max bounds, use normal values
        normal_vals = FPTestValues.get_normal_values(self.fmt)
        min_max_pairs = []

        # Use sensible ranges with normal values
        if len(normal_vals) >= 4:
            # -1.0 to 1.0 (common range)
            min_max_pairs.append((normal_vals[1], normal_vals[0]))  # -1.0 to 1.0
            # Use min normal to max normal
            if len(normal_vals) >= 3:
                min_max_pairs.append((normal_vals[3], normal_vals[2]))  # min_normal to max_normal

        # Also test with zero as a bound
        min_max_pairs.append((0, normal_vals[0]))  # 0 to 1.0

        for i, x in enumerate(values[:20]):
            for min_val, max_val in min_max_pairs:
                await self.test_single(x, min_val, max_val, f"clamp_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Activation Function Testbenches
# =============================================================================

class FPReluTB(FPBaseTB):
    """Testbench for ReLU activation."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP ReLU TB for {fmt.name}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, x: int) -> int:
        """ReLU: max(0, x)"""
        if FPUtils.is_nan(x, self.fmt):
            return x

        # Check sign bit directly - positive values (including subnormals) pass through
        sign = (x >> (self.fmt.bits - 1)) & 1
        if sign == 1:  # Negative
            return 0
        # Positive (including +0 and positive subnormals)
        return x

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting ReLU tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"relu_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


class FPLeakyReluTB(FPBaseTB):
    """Testbench for Leaky ReLU activation."""

    def __init__(self, dut, fmt: FPFormat, alpha_shift: int = 4):  # RTL uses 2^-4
        super().__init__(dut, fmt)
        self.alpha_shift = alpha_shift
        self.alpha = 2 ** (-alpha_shift)
        self.log.info(f"FP Leaky ReLU TB for {fmt.name}, alpha_shift={alpha_shift} (alpha={self.alpha})")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, x: int) -> int:
        """Leaky ReLU matching RTL's exponent-decrement implementation.

        RTL behavior:
        - NaN: propagate unchanged
        - Zero: return zero
        - Positive: pass through unchanged
        - Negative: scale by alpha via exponent decrement (exp - ALPHA_SHIFT)
                   with underflow clamping to 0
        """
        # Handle NaN
        if FPUtils.is_nan(x, self.fmt):
            return x

        # Handle zero
        if FPUtils.is_zero(x, self.fmt):
            return 0

        # Check sign bit - positive values pass through
        sign = (x >> (self.fmt.bits - 1)) & 1
        if sign == 0:
            return x

        # Negative: scale by alpha via exponent decrement (matches RTL exactly)
        exp_mask = (1 << self.fmt.exp_bits) - 1
        mant_mask = (1 << self.fmt.mant_bits) - 1

        exp = (x >> self.fmt.mant_bits) & exp_mask
        mant = x & mant_mask

        # RTL: w_scaled_exp = (w_exp > ALPHA_SHIFT) ? (w_exp - ALPHA_SHIFT) : 0
        if exp > self.alpha_shift:
            scaled_exp = exp - self.alpha_shift
        else:
            scaled_exp = 0

        # Reconstruct: {sign, scaled_exp, mant}
        return (sign << (self.fmt.bits - 1)) | (scaled_exp << self.fmt.mant_bits) | mant

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting Leaky ReLU tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"leaky_relu_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# FMA Testbench
# =============================================================================

class FPFMATB(FPBaseTB):
    """Testbench for floating-point FMA (Fused Multiply-Add) modules."""

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP FMA TB for {fmt.name}")

    async def clear_interface(self):
        """Clear input interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_c.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, a: int, b: int, c: int) -> Tuple[int, bool, bool, bool]:
        """Compute expected FMA result: a*b + c."""
        # Apply FTZ (Flush-To-Zero) to inputs - RTL treats subnormal inputs as zero
        a_ftz = FPUtils.apply_ftz(a, self.fmt)
        b_ftz = FPUtils.apply_ftz(b, self.fmt)
        c_ftz = FPUtils.apply_ftz(c, self.fmt)

        a_float = FPUtils.to_float(a_ftz, self.fmt)
        b_float = FPUtils.to_float(b_ftz, self.fmt)
        c_float = FPUtils.to_float(c_ftz, self.fmt)

        a_is_zero = FPUtils.is_zero(a_ftz, self.fmt)
        b_is_zero = FPUtils.is_zero(b_ftz, self.fmt)
        a_is_inf = FPUtils.is_inf(a, self.fmt)
        b_is_inf = FPUtils.is_inf(b, self.fmt)
        c_is_inf = FPUtils.is_inf(c, self.fmt)
        a_is_nan = FPUtils.is_nan(a, self.fmt)
        b_is_nan = FPUtils.is_nan(b, self.fmt)
        c_is_nan = FPUtils.is_nan(c, self.fmt)

        sign_a = (a >> (self.fmt.bits - 1)) & 1
        sign_b = (b >> (self.fmt.bits - 1)) & 1
        sign_c = (c >> (self.fmt.bits - 1)) & 1
        sign_product = sign_a ^ sign_b

        # Invalid: 0*inf or inf*0
        invalid_mult = (a_is_zero and b_is_inf) or (b_is_zero and a_is_inf)

        # Product sign for determining inf+(-inf) invalid case
        product_is_inf = a_is_inf or b_is_inf
        invalid_add = product_is_inf and c_is_inf and (sign_product != sign_c)

        invalid = invalid_mult or invalid_add

        if a_is_nan or b_is_nan or c_is_nan or invalid:
            nan = FPUtils.make_value(0, self.fmt.exp_max,
                                    1 if self.fmt.has_infinity else self.fmt.mant_max, self.fmt)
            return nan, False, False, invalid

        # Product is infinity
        if product_is_inf:
            if c_is_inf and sign_product == sign_c:
                inf = FPUtils.make_value(sign_product, self.fmt.exp_max, 0, self.fmt)
                return inf, False, False, False
            inf = FPUtils.make_value(sign_product, self.fmt.exp_max, 0, self.fmt)
            return inf, False, False, False

        # c is infinity, product is not
        if c_is_inf:
            return c, False, False, False

        # Normal computation - use Python's high precision
        result_float = a_float * b_float + c_float
        result = FPUtils.convert_float(result_float, self.fmt)

        # Apply FTZ (Flush-To-Zero) for subnormal results
        result = FPUtils.apply_ftz(result, self.fmt)

        overflow = FPUtils.is_inf(result, self.fmt) and not (a_is_inf or b_is_inf or c_is_inf)
        underflow = FPUtils.is_zero(result, self.fmt) and result_float != 0

        return result, overflow, underflow, False

    async def test_single(self, a: int, b: int, c: int, desc: str = "") -> bool:
        """Test a single FMA operation."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        self.dut.i_c.value = c
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected, _, _, _ = self.compute_expected(a, b, c)

        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info("Starting comprehensive FMA tests")

        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        # Test triples from special and normal values
        for i, a in enumerate(values[:10]):
            for b in values[:10]:
                for c in values[:5]:
                    await self.test_single(a, b, c, f"triple_{i}")

        # Random combinations
        for i in range(min(100, len(values))):
            a = random.choice(values)
            b = random.choice(values)
            c = random.choice(values)
            await self.test_single(a, b, c, f"random_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Additional Activation Function Testbenches
# =============================================================================

class FPSigmoidTB(FPBaseTB):
    """Testbench for Sigmoid activation: 1 / (1 + exp(-x)).

    RTL uses piecewise approximation:
    - NaN: propagate
    - |x| >= 4 (saturated): 0 or 1
    - |x| < 0.25 (near_zero): 0.5
    - Medium range: 0.375 (negative) or 0.625 (positive)
    """

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Sigmoid TB for {fmt.name}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def _extract_fields(self, x: int) -> tuple:
        """Extract sign, exp, mant from format."""
        sign = (x >> (self.fmt.bits - 1)) & 1
        exp = (x >> self.fmt.mant_bits) & ((1 << self.fmt.exp_bits) - 1)
        mant = x & ((1 << self.fmt.mant_bits) - 1)
        return sign, exp, mant

    def _make_value(self, sign: int, exp: int, mant: int) -> int:
        """Construct value from fields."""
        return (sign << (self.fmt.bits - 1)) | (exp << self.fmt.mant_bits) | mant

    def compute_expected(self, x: int) -> int:
        """Sigmoid matching RTL piecewise approximation."""
        if FPUtils.is_nan(x, self.fmt):
            return x

        sign, exp, mant = self._extract_fields(x)
        bias = self.fmt.bias
        exp_max = self.fmt.exp_max

        # Special case detection
        is_zero = (exp == 0) and (mant == 0)
        is_subnormal = (exp == 0) and (mant != 0)
        is_inf = (exp == exp_max) and (mant == 0)

        # Thresholds: |x| >= 4 means exp >= bias+2
        saturated = (exp >= bias + 2)
        # |x| < 0.25 means exp < bias-2
        near_zero = (exp < bias - 2) or is_zero or is_subnormal

        # Constants
        ZERO = 0
        HALF = self._make_value(0, bias - 1, 0)  # 0.5
        ONE = self._make_value(0, bias, 0)  # 1.0

        if is_inf or saturated:
            return ZERO if sign else ONE
        elif near_zero:
            return HALF
        else:
            # Medium range: 0.375 (negative) or 0.625 (positive)
            # 0.375 = 0.5 - 0.125 = 2^-1 - 2^-3, approx as exp=bias-2 with mant
            # 0.625 = 0.5 + 0.125 = 2^-1 + 2^-3, approx as exp=bias-1 with mant
            half_mant = 1 << (self.fmt.mant_bits - 1)  # 0.5 in mantissa field
            if sign:
                return self._make_value(0, bias - 2, half_mant)  # ~0.375
            else:
                return self._make_value(0, bias - 1, half_mant)  # ~0.625

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting Sigmoid tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"sigmoid_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


class FPTanhTB(FPBaseTB):
    """Testbench for Tanh activation.

    RTL uses piecewise approximation:
    - NaN: propagate
    - |x| >= 2 (saturated): ±1
    - |x| < 0.5 (near_zero): x (passthrough)
    - Medium range: ±0.75
    """

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP Tanh TB for {fmt.name}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def _extract_fields(self, x: int) -> tuple:
        """Extract sign, exp, mant from format."""
        sign = (x >> (self.fmt.bits - 1)) & 1
        exp = (x >> self.fmt.mant_bits) & ((1 << self.fmt.exp_bits) - 1)
        mant = x & ((1 << self.fmt.mant_bits) - 1)
        return sign, exp, mant

    def _make_value(self, sign: int, exp: int, mant: int) -> int:
        """Construct value from fields."""
        return (sign << (self.fmt.bits - 1)) | (exp << self.fmt.mant_bits) | mant

    def compute_expected(self, x: int) -> int:
        """Tanh matching RTL piecewise approximation."""
        if FPUtils.is_nan(x, self.fmt):
            return x

        sign, exp, mant = self._extract_fields(x)
        bias = self.fmt.bias
        exp_max = self.fmt.exp_max

        # Special case detection
        is_zero = (exp == 0) and (mant == 0)
        is_subnormal = (exp == 0) and (mant != 0)
        is_inf = (exp == exp_max) and (mant == 0)

        # Thresholds: |x| >= 2 means exp >= bias+1
        saturated = (exp >= bias + 1)
        # |x| < 0.5 means exp < bias-1
        near_zero = (exp < bias - 1) or is_zero or is_subnormal

        # Constants
        POS_ONE = self._make_value(0, bias, 0)  # +1.0
        NEG_ONE = self._make_value(1, bias, 0)  # -1.0

        if is_inf or saturated:
            return NEG_ONE if sign else POS_ONE
        elif near_zero:
            return x  # Passthrough
        else:
            # Medium range: ±0.75
            half_mant = 1 << (self.fmt.mant_bits - 1)  # 0.5 in mantissa field
            return self._make_value(sign, bias - 1, half_mant)  # ±0.75

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting Tanh tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"tanh_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


class FPGeluTB(FPBaseTB):
    """Testbench for GELU activation: x * 0.5 * (1 + erf(x / sqrt(2))).

    RTL uses piecewise approximation:
    - NaN: propagate
    - +inf: +inf, -inf: 0
    - Large negative (|x| >= 4): 0
    - Large positive (|x| >= 4): x
    - Near zero (|x| < 0.25): 0.5 * x
    - Medium negative: -0.125
    - Medium positive: 0.75
    """

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP GELU TB for {fmt.name}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def _extract_fields(self, x: int) -> tuple:
        """Extract sign, exp, mant from format."""
        sign = (x >> (self.fmt.bits - 1)) & 1
        exp = (x >> self.fmt.mant_bits) & ((1 << self.fmt.exp_bits) - 1)
        mant = x & ((1 << self.fmt.mant_bits) - 1)
        return sign, exp, mant

    def _make_value(self, sign: int, exp: int, mant: int) -> int:
        """Construct value from fields."""
        return (sign << (self.fmt.bits - 1)) | (exp << self.fmt.mant_bits) | mant

    def compute_expected(self, x: int) -> int:
        """GELU matching RTL piecewise approximation."""
        if FPUtils.is_nan(x, self.fmt):
            return x

        sign, exp, mant = self._extract_fields(x)
        bias = self.fmt.bias
        exp_max = self.fmt.exp_max

        # Special case detection
        is_zero = (exp == 0) and (mant == 0)
        is_subnormal = (exp == 0) and (mant != 0)
        is_inf = (exp == exp_max) and (mant == 0)

        # Thresholds
        large_pos = (sign == 0) and (exp >= bias + 2)
        large_neg = (sign == 1) and (exp >= bias + 2)
        near_zero = (exp < bias - 2) or is_zero or is_subnormal

        ZERO = 0

        if is_inf:
            return ZERO if sign else x
        elif large_neg:
            return ZERO
        elif large_pos:
            return x
        elif near_zero:
            # 0.5 * x: decrement exponent by 1
            if exp > 1:
                return self._make_value(sign, exp - 1, mant)
            else:
                return ZERO  # Underflow
        else:
            # Medium range
            if sign:
                # Negative medium: -0.125 = -2^-3
                return self._make_value(1, bias - 3, 0)
            else:
                # Positive medium: 0.75
                half_mant = 1 << (self.fmt.mant_bits - 1)
                return self._make_value(0, bias - 1, half_mant)

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting GELU tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"gelu_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


class FPSiluTB(FPBaseTB):
    """Testbench for SiLU (Swish) activation: x * sigmoid(x).

    RTL uses piecewise approximation:
    - NaN: propagate
    - +inf: +inf, -inf: 0
    - Large negative (|x| >= 4): 0
    - Large positive (|x| >= 4): x
    - Near zero (|x| < 0.25): 0.5 * x
    - Medium negative: -0.25
    - Medium positive: 0.75
    """

    def __init__(self, dut, fmt: FPFormat):
        super().__init__(dut, fmt)
        self.log.info(f"FP SiLU TB for {fmt.name}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def _extract_fields(self, x: int) -> tuple:
        """Extract sign, exp, mant from format."""
        sign = (x >> (self.fmt.bits - 1)) & 1
        exp = (x >> self.fmt.mant_bits) & ((1 << self.fmt.exp_bits) - 1)
        mant = x & ((1 << self.fmt.mant_bits) - 1)
        return sign, exp, mant

    def _make_value(self, sign: int, exp: int, mant: int) -> int:
        """Construct value from fields."""
        return (sign << (self.fmt.bits - 1)) | (exp << self.fmt.mant_bits) | mant

    def compute_expected(self, x: int) -> int:
        """SiLU matching RTL piecewise approximation."""
        if FPUtils.is_nan(x, self.fmt):
            return x

        sign, exp, mant = self._extract_fields(x)
        bias = self.fmt.bias
        exp_max = self.fmt.exp_max

        # Special case detection
        is_zero = (exp == 0) and (mant == 0)
        is_subnormal = (exp == 0) and (mant != 0)
        is_inf = (exp == exp_max) and (mant == 0)

        # Thresholds
        large_pos = (sign == 0) and (exp >= bias + 2)
        large_neg = (sign == 1) and (exp >= bias + 2)
        near_zero = (exp < bias - 2) or is_zero or is_subnormal

        ZERO = 0

        if is_inf:
            return ZERO if sign else x
        elif large_neg:
            return ZERO
        elif large_pos:
            return x
        elif near_zero:
            # 0.5 * x: decrement exponent by 1
            if exp > 1:
                return self._make_value(sign, exp - 1, mant)
            else:
                return ZERO  # Underflow
        else:
            # Medium range
            if sign:
                # Negative medium: -0.25 = -2^-2
                return self._make_value(1, bias - 2, 0)
            else:
                # Positive medium: 0.75
                half_mant = 1 << (self.fmt.mant_bits - 1)
                return self._make_value(0, bias - 1, half_mant)

    async def test_single(self, x: int, desc: str = "") -> bool:
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)
        return self.check_result(result, expected, desc)

    async def run_comprehensive_tests(self):
        self.log.info("Starting SiLU tests")
        values = FPTestValues.get_all_test_values(self.fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"silu_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


# =============================================================================
# Format Conversion Testbench
# =============================================================================

class FPConversionTB(TBBase):
    """Testbench for format conversion modules."""

    def __init__(self, dut, src_fmt: FPFormat, dst_fmt: FPFormat):
        TBBase.__init__(self, dut)
        self.src_fmt = src_fmt
        self.dst_fmt = dst_fmt
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"Conversion TB: {src_fmt.name} -> {dst_fmt.name}")

    def print_settings(self):
        """Print testbench configuration."""
        self.log.info(f"Source: {self.src_fmt.name} ({self.src_fmt.bits} bits)")
        self.log.info(f"Dest: {self.dst_fmt.name} ({self.dst_fmt.bits} bits)")
        self.log.info(f"Test Level: {self.test_level}")

    async def clear_interface(self):
        self.dut.i_a.value = 0
        await self.wait_time(1, 'ns')

    def compute_expected(self, x: int) -> int:
        """Compute expected conversion result."""
        # Convert source to float, then to destination format
        x_float = FPUtils.to_float(x, self.src_fmt)
        return FPUtils.convert_float(x_float, self.dst_fmt)

    async def test_single(self, x: int, desc: str = "") -> bool:
        """Test a single conversion."""
        self.dut.i_a.value = x
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        expected = self.compute_expected(x)

        self.test_count += 1

        # NaN handling
        result_nan = FPUtils.is_nan(result, self.dst_fmt)
        expected_nan = FPUtils.is_nan(expected, self.dst_fmt)

        if result_nan and expected_nan:
            self.pass_count += 1
            return True

        # Zero handling: +0 and -0 are equivalent (IEEE 754)
        result_zero = FPUtils.is_zero(result, self.dst_fmt)
        expected_zero = FPUtils.is_zero(expected, self.dst_fmt)
        if result_zero and expected_zero:
            self.pass_count += 1
            return True

        # Infinity must match exactly (same sign)
        result_inf = FPUtils.is_inf(result, self.dst_fmt)
        expected_inf = FPUtils.is_inf(expected, self.dst_fmt)
        if result_inf or expected_inf:
            passed = (result == expected)
        elif result == expected:
            passed = True
        else:
            # Allow 1 ULP tolerance
            mask = (1 << (self.dst_fmt.bits - 1)) - 1
            ulp_diff = abs((result & mask) - (expected & mask))
            sign_match = (result >> (self.dst_fmt.bits - 1)) == (expected >> (self.dst_fmt.bits - 1))
            passed = sign_match and ulp_diff <= 1

        if passed:
            self.pass_count += 1
        else:
            self.fail_count += 1
            src_val = FPUtils.to_float(x, self.src_fmt)
            self.log.error(f"FAIL {desc}: src=0x{x:X} ({src_val}), "
                          f"got 0x{result:X}, expected 0x{expected:X}")

        return passed

    async def run_comprehensive_tests(self):
        """Run all test categories."""
        self.log.info(f"Starting conversion tests: {self.src_fmt.name} -> {self.dst_fmt.name}")

        values = FPTestValues.get_all_test_values(self.src_fmt, self.test_level)

        for i, x in enumerate(values):
            await self.test_single(x, f"conv_{i}")

        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, "
                     f"{self.fail_count} failed")
        assert self.fail_count == 0, f"{self.fail_count} tests failed"
