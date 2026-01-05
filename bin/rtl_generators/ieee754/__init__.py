# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IEEE 754-2008 FP32 Generators
# Purpose: RTL generators for IEEE 754-2008 FP32 (single precision) floating-point arithmetic
#
# Components:
#   - Han-Carlson prefix adder (32/48/72-bit for various FP32 paths)
#   - Dadda tree with 4:2 compressors (24x24 mantissa multiply)
#   - FP32 mantissa multiplier
#   - FP32 exponent adder
#   - FP32 complete multiplier
#   - FP32 adder (pipelined)
#   - FP32 FMA (fused multiply-add)
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from .han_carlson_adder import HanCarlsonAdder, generate_han_carlson_adder
from .dadda_4to2_multiplier import Dadda4to2Multiplier, generate_dadda_4to2_multiplier
# FP32 modules
from .fp32_mantissa_mult import FP32MantissaMult, generate_fp32_mantissa_mult
from .fp32_exponent_adder import FP32ExponentAdder, generate_fp32_exponent_adder
from .fp32_multiplier import FP32Multiplier, generate_fp32_multiplier
from .fp32_adder import generate_fp32_adder
from .fp32_fma import FP32FMA, generate_fp32_fma
# FP16 modules
from .fp16_mantissa_mult import FP16MantissaMult, generate_fp16_mantissa_mult
from .fp16_exponent_adder import FP16ExponentAdder, generate_fp16_exponent_adder
from .fp16_multiplier import FP16Multiplier, generate_fp16_multiplier
from .fp16_adder import generate_fp16_adder
from .fp16_fma import FP16FMA, generate_fp16_fma
# FP8 E4M3 modules
from .fp8_e4m3_mantissa_mult import FP8E4M3MantissaMult, generate_fp8_e4m3_mantissa_mult
from .fp8_e4m3_exponent_adder import FP8E4M3ExponentAdder, generate_fp8_e4m3_exponent_adder
from .fp8_e4m3_multiplier import FP8E4M3Multiplier, generate_fp8_e4m3_multiplier
from .fp8_e4m3_adder import generate_fp8_e4m3_adder
from .fp8_e4m3_fma import FP8E4M3FMA, generate_fp8_e4m3_fma
# FP8 E5M2 modules
from .fp8_e5m2_mantissa_mult import FP8E5M2MantissaMult, generate_fp8_e5m2_mantissa_mult
from .fp8_e5m2_exponent_adder import FP8E5M2ExponentAdder, generate_fp8_e5m2_exponent_adder
from .fp8_e5m2_multiplier import FP8E5M2Multiplier, generate_fp8_e5m2_multiplier
from .fp8_e5m2_adder import generate_fp8_e5m2_adder
from .fp8_e5m2_fma import FP8E5M2FMA, generate_fp8_e5m2_fma
# Format conversions
from .fp_conversions import (
    FORMATS,
    generate_upconvert,
    generate_downconvert,
    generate_same_size_convert,
    generate_conversion,
    generate_all_conversions,
)
# Activation functions
from .fp_activations import (
    generate_relu,
    generate_leaky_relu,
    generate_sigmoid,
    generate_tanh,
    generate_gelu,
    generate_silu,
    generate_softmax,
    generate_all_activations,
)
# Comparison operations
from .fp_comparisons import (
    generate_comparator,
    generate_max,
    generate_min,
    generate_max_tree,
    generate_min_tree,
    generate_clamp,
    generate_all_comparisons,
)

__all__ = [
    # Building blocks
    'HanCarlsonAdder',
    'generate_han_carlson_adder',
    'Dadda4to2Multiplier',
    'generate_dadda_4to2_multiplier',
    # FP32
    'FP32MantissaMult',
    'generate_fp32_mantissa_mult',
    'FP32ExponentAdder',
    'generate_fp32_exponent_adder',
    'FP32Multiplier',
    'generate_fp32_multiplier',
    'generate_fp32_adder',
    'FP32FMA',
    'generate_fp32_fma',
    # FP16
    'FP16MantissaMult',
    'generate_fp16_mantissa_mult',
    'FP16ExponentAdder',
    'generate_fp16_exponent_adder',
    'FP16Multiplier',
    'generate_fp16_multiplier',
    'generate_fp16_adder',
    'FP16FMA',
    'generate_fp16_fma',
    # FP8 E4M3
    'FP8E4M3MantissaMult',
    'generate_fp8_e4m3_mantissa_mult',
    'FP8E4M3ExponentAdder',
    'generate_fp8_e4m3_exponent_adder',
    'FP8E4M3Multiplier',
    'generate_fp8_e4m3_multiplier',
    'generate_fp8_e4m3_adder',
    'FP8E4M3FMA',
    'generate_fp8_e4m3_fma',
    # FP8 E5M2
    'FP8E5M2MantissaMult',
    'generate_fp8_e5m2_mantissa_mult',
    'FP8E5M2ExponentAdder',
    'generate_fp8_e5m2_exponent_adder',
    'FP8E5M2Multiplier',
    'generate_fp8_e5m2_multiplier',
    'generate_fp8_e5m2_adder',
    'FP8E5M2FMA',
    'generate_fp8_e5m2_fma',
    # Format conversions
    'FORMATS',
    'generate_upconvert',
    'generate_downconvert',
    'generate_same_size_convert',
    'generate_conversion',
    'generate_all_conversions',
    # Activation functions
    'generate_relu',
    'generate_leaky_relu',
    'generate_sigmoid',
    'generate_tanh',
    'generate_gelu',
    'generate_silu',
    'generate_softmax',
    'generate_all_activations',
    # Comparison operations
    'generate_comparator',
    'generate_max',
    'generate_min',
    'generate_max_tree',
    'generate_min_tree',
    'generate_clamp',
    'generate_all_comparisons',
]
