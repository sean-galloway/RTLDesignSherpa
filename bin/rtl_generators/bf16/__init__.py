# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BF16 Generators
# Purpose: RTL generators for BF16 (Brain Float 16) arithmetic modules
#
# Components:
#   - Han-Carlson prefix adder (optimal for 16-bit CPA)
#   - Dadda tree with 4:2 compressors (8x8 mantissa multiply)
#   - BF16 mantissa multiplier
#   - BF16 exponent adder
#   - BF16 complete multiplier
#   - BF16 FMA (fused multiply-add) with FP32 accumulator
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

from .han_carlson_adder import HanCarlsonAdder
from .dadda_4to2_multiplier import Dadda4to2Multiplier
from .bf16_mantissa_mult import BF16MantissaMult
from .bf16_exponent_adder import BF16ExponentAdder
from .bf16_multiplier import BF16Multiplier
from .bf16_fma import BF16FMA

__all__ = [
    'HanCarlsonAdder',
    'Dadda4to2Multiplier',
    'BF16MantissaMult',
    'BF16ExponentAdder',
    'BF16Multiplier',
    'BF16FMA',
]
