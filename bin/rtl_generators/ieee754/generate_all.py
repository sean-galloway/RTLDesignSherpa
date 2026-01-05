#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IEEE 754-2008 FP32/FP16/FP8 Generator Master Script
# Purpose: Generate all IEEE 754-2008 floating-point RTL modules
#
# Generated modules:
#   Building Blocks (8 modules):
#     - math_adder_han_carlson_*.sv - Prefix adders (16, 22, 32, 44, 48, 72-bit)
#     - math_multiplier_dadda_4to2_*.sv - Dadda trees (11x11, 24x24)
#
#   FP32 Modules (5 modules):
#     - math_ieee754_2008_fp32_{mantissa_mult,exponent_adder,multiplier,adder,fma}.sv
#
#   FP16 Modules (5 modules):
#     - math_ieee754_2008_fp16_{mantissa_mult,exponent_adder,multiplier,adder,fma}.sv
#
#   FP8 E4M3 Modules (5 modules):
#     - math_fp8_e4m3_{mantissa_mult,exponent_adder,multiplier,adder,fma}.sv
#
#   FP8 E5M2 Modules (5 modules):
#     - math_fp8_e5m2_{mantissa_mult,exponent_adder,multiplier,adder,fma}.sv
#
#   Format Conversions (20 modules):
#     - math_{src}_to_{dst}.sv - All bidirectional conversions between:
#       fp32, fp16, bf16, fp8_e4m3, fp8_e5m2
#
#   Activation Functions (35 modules):
#     - math_{fmt}_{relu,leaky_relu,sigmoid,tanh,gelu,silu,softmax_8}.sv
#
#   Comparison Operations (30 modules):
#     - math_{fmt}_{comparator,max,min,clamp,max_tree_8,min_tree_8}.sv
#
# Usage:
#   python generate_all.py [output_directory]
#
# Default output: rtl/common/
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

import os
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from rtl_generators.ieee754.han_carlson_adder import generate_han_carlson_adder
from rtl_generators.ieee754.dadda_4to2_multiplier import generate_dadda_4to2_multiplier
# FP32
from rtl_generators.ieee754.fp32_mantissa_mult import generate_fp32_mantissa_mult
from rtl_generators.ieee754.fp32_exponent_adder import generate_fp32_exponent_adder
from rtl_generators.ieee754.fp32_multiplier import generate_fp32_multiplier
from rtl_generators.ieee754.fp32_adder import generate_fp32_adder
from rtl_generators.ieee754.fp32_fma import generate_fp32_fma
# FP16
from rtl_generators.ieee754.fp16_mantissa_mult import generate_fp16_mantissa_mult
from rtl_generators.ieee754.fp16_exponent_adder import generate_fp16_exponent_adder
from rtl_generators.ieee754.fp16_multiplier import generate_fp16_multiplier
from rtl_generators.ieee754.fp16_adder import generate_fp16_adder
from rtl_generators.ieee754.fp16_fma import generate_fp16_fma
# FP8 E4M3
from rtl_generators.ieee754.fp8_e4m3_mantissa_mult import generate_fp8_e4m3_mantissa_mult
from rtl_generators.ieee754.fp8_e4m3_exponent_adder import generate_fp8_e4m3_exponent_adder
from rtl_generators.ieee754.fp8_e4m3_multiplier import generate_fp8_e4m3_multiplier
from rtl_generators.ieee754.fp8_e4m3_adder import generate_fp8_e4m3_adder
from rtl_generators.ieee754.fp8_e4m3_fma import generate_fp8_e4m3_fma
# FP8 E5M2
from rtl_generators.ieee754.fp8_e5m2_mantissa_mult import generate_fp8_e5m2_mantissa_mult
from rtl_generators.ieee754.fp8_e5m2_exponent_adder import generate_fp8_e5m2_exponent_adder
from rtl_generators.ieee754.fp8_e5m2_multiplier import generate_fp8_e5m2_multiplier
from rtl_generators.ieee754.fp8_e5m2_adder import generate_fp8_e5m2_adder
from rtl_generators.ieee754.fp8_e5m2_fma import generate_fp8_e5m2_fma
# Format Conversions
from rtl_generators.ieee754.fp_conversions import generate_all_conversions
# Activation Functions
from rtl_generators.ieee754.fp_activations import generate_all_activations
# Comparison Operations
from rtl_generators.ieee754.fp_comparisons import generate_all_comparisons


def generate_building_blocks(output_dir):
    """Generate shared building blocks (Han-Carlson adders, Dadda multipliers)."""
    generated = []

    print('\n=== Building Blocks ===')

    # Han-Carlson adders for various widths
    # 16: FP16 exponent paths
    # 22: FP16 product CPA (11x11=22)
    # 32: FP32 exponent paths
    # 44: FP16 FMA accumulator
    # 48: FP32 product CPA (24x24=48)
    # 72: FP32 FMA accumulator
    for width in [16, 22, 32, 44, 48, 72]:
        print(f'Generating Han-Carlson adder ({width}-bit)...')
        name = generate_han_carlson_adder(width, output_dir)
        generated.append(name)
        print(f'  Created: {name}.sv')

    # Dadda multipliers
    for width in [11, 24]:
        print(f'Generating Dadda 4:2 multiplier ({width}-bit)...')
        name = generate_dadda_4to2_multiplier(width, output_dir)
        generated.append(name)
        print(f'  Created: {name}.sv')

    return generated


def generate_fp32_modules(output_dir):
    """Generate all IEEE 754-2008 FP32 RTL modules."""
    generated = []

    print('\n=== FP32 Modules ===')

    print('Generating FP32 mantissa multiplier...')
    name = generate_fp32_mantissa_mult(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP32 exponent adder...')
    name = generate_fp32_exponent_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP32 multiplier...')
    name = generate_fp32_multiplier(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP32 adder...')
    name = generate_fp32_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP32 FMA...')
    name = generate_fp32_fma(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    return generated


def generate_fp16_modules(output_dir):
    """Generate all IEEE 754-2008 FP16 RTL modules."""
    generated = []

    print('\n=== FP16 Modules ===')

    print('Generating FP16 mantissa multiplier...')
    name = generate_fp16_mantissa_mult(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP16 exponent adder...')
    name = generate_fp16_exponent_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP16 multiplier...')
    name = generate_fp16_multiplier(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP16 adder...')
    name = generate_fp16_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP16 FMA...')
    name = generate_fp16_fma(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    return generated


def generate_fp8_e4m3_modules(output_dir):
    """Generate all FP8 E4M3 RTL modules."""
    generated = []

    print('\n=== FP8 E4M3 Modules ===')

    print('Generating FP8 E4M3 mantissa multiplier...')
    name = generate_fp8_e4m3_mantissa_mult(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E4M3 exponent adder...')
    name = generate_fp8_e4m3_exponent_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E4M3 multiplier...')
    name = generate_fp8_e4m3_multiplier(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E4M3 adder...')
    name = generate_fp8_e4m3_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E4M3 FMA...')
    name = generate_fp8_e4m3_fma(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    return generated


def generate_fp8_e5m2_modules(output_dir):
    """Generate all FP8 E5M2 RTL modules."""
    generated = []

    print('\n=== FP8 E5M2 Modules ===')

    print('Generating FP8 E5M2 mantissa multiplier...')
    name = generate_fp8_e5m2_mantissa_mult(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E5M2 exponent adder...')
    name = generate_fp8_e5m2_exponent_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E5M2 multiplier...')
    name = generate_fp8_e5m2_multiplier(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E5M2 adder...')
    name = generate_fp8_e5m2_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('Generating FP8 E5M2 FMA...')
    name = generate_fp8_e5m2_fma(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    return generated


def generate_all_modules(output_dir):
    """Generate all IEEE 754 RTL modules (FP32 + FP16 + FP8)."""
    print('IEEE 754 FP32/FP16/FP8 RTL Generator')
    print(f'Output directory: {output_dir}')
    print('=' * 60)

    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    generated = []
    generated.extend(generate_building_blocks(output_dir))
    generated.extend(generate_fp32_modules(output_dir))
    generated.extend(generate_fp16_modules(output_dir))
    generated.extend(generate_fp8_e4m3_modules(output_dir))
    generated.extend(generate_fp8_e5m2_modules(output_dir))
    generated.extend(generate_all_conversions(output_dir))
    generated.extend(generate_all_activations(output_dir))
    generated.extend(generate_all_comparisons(output_dir))

    print('=' * 60)
    print(f'Generated {len(generated)} modules total')

    return generated


def print_dependency_order():
    """Print the module dependency order for synthesis."""
    print('\nModule dependency order (bottom-up):')
    print('  Common primitives (existing):')
    print('    - math_adder_half.sv')
    print('    - math_adder_full.sv')
    print('    - math_compressor_4to2.sv')
    print('    - math_prefix_cell.sv')
    print('    - math_prefix_cell_gray.sv')
    print('    - count_leading_zeros.sv')
    print('')
    print('  Building blocks (generated):')
    print('    - math_adder_han_carlson_016.sv')
    print('    - math_adder_han_carlson_032.sv')
    print('    - math_adder_han_carlson_044.sv')
    print('    - math_adder_han_carlson_048.sv')
    print('    - math_adder_han_carlson_072.sv')
    print('    - math_multiplier_dadda_4to2_011.sv')
    print('    - math_multiplier_dadda_4to2_024.sv')
    print('')
    print('  FP32 modules (generated):')
    print('    - math_ieee754_2008_fp32_mantissa_mult.sv')
    print('    - math_ieee754_2008_fp32_exponent_adder.sv')
    print('    - math_ieee754_2008_fp32_multiplier.sv')
    print('    - math_ieee754_2008_fp32_adder.sv')
    print('    - math_ieee754_2008_fp32_fma.sv')
    print('')
    print('  FP16 modules (generated):')
    print('    - math_ieee754_2008_fp16_mantissa_mult.sv')
    print('    - math_ieee754_2008_fp16_exponent_adder.sv')
    print('    - math_ieee754_2008_fp16_multiplier.sv')
    print('    - math_ieee754_2008_fp16_adder.sv')
    print('    - math_ieee754_2008_fp16_fma.sv')
    print('')
    print('  FP8 E4M3 modules (generated):')
    print('    - math_fp8_e4m3_mantissa_mult.sv')
    print('    - math_fp8_e4m3_exponent_adder.sv')
    print('    - math_fp8_e4m3_multiplier.sv')
    print('    - math_fp8_e4m3_adder.sv')
    print('    - math_fp8_e4m3_fma.sv')
    print('')
    print('  FP8 E5M2 modules (generated):')
    print('    - math_fp8_e5m2_mantissa_mult.sv')
    print('    - math_fp8_e5m2_exponent_adder.sv')
    print('    - math_fp8_e5m2_multiplier.sv')
    print('    - math_fp8_e5m2_adder.sv')
    print('    - math_fp8_e5m2_fma.sv')
    print('')
    print('  Format conversions (generated):')
    print('    - math_fp32_to_fp16.sv, math_fp16_to_fp32.sv')
    print('    - math_fp32_to_bf16.sv, math_bf16_to_fp32.sv')
    print('    - math_fp32_to_fp8_e4m3.sv, math_fp8_e4m3_to_fp32.sv')
    print('    - math_fp32_to_fp8_e5m2.sv, math_fp8_e5m2_to_fp32.sv')
    print('    - math_fp16_to_bf16.sv, math_bf16_to_fp16.sv')
    print('    - math_fp16_to_fp8_e4m3.sv, math_fp8_e4m3_to_fp16.sv')
    print('    - math_fp16_to_fp8_e5m2.sv, math_fp8_e5m2_to_fp16.sv')
    print('    - math_bf16_to_fp8_e4m3.sv, math_fp8_e4m3_to_bf16.sv')
    print('    - math_bf16_to_fp8_e5m2.sv, math_fp8_e5m2_to_bf16.sv')
    print('    - math_fp8_e4m3_to_fp8_e5m2.sv, math_fp8_e5m2_to_fp8_e4m3.sv')
    print('')
    print('  Activation functions (generated, 7 per format):')
    print('    - math_{fmt}_relu.sv, math_{fmt}_leaky_relu.sv')
    print('    - math_{fmt}_sigmoid.sv, math_{fmt}_tanh.sv')
    print('    - math_{fmt}_gelu.sv, math_{fmt}_silu.sv')
    print('    - math_{fmt}_softmax_8.sv')
    print('')
    print('  Comparison operations (generated, 6 per format):')
    print('    - math_{fmt}_comparator.sv - Full comparison (EQ/LT/GT/LE/GE/NE/UNORD)')
    print('    - math_{fmt}_max.sv, math_{fmt}_min.sv - Two-value max/min')
    print('    - math_{fmt}_max_tree_8.sv, math_{fmt}_min_tree_8.sv - 8-element reduction')
    print('    - math_{fmt}_clamp.sv - Clamp to [min, max] range')


def main():
    # Get output directory from command line or use default
    if len(sys.argv) > 1:
        output_dir = sys.argv[1]
    else:
        # Default to rtl/common/ relative to repo root
        script_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(os.path.dirname(os.path.dirname(script_dir)))
        output_dir = os.path.join(repo_root, 'rtl', 'common')

    generated = generate_all_modules(output_dir)
    print_dependency_order()

    print('\nTo verify synthesis:')
    print(f'  cd {output_dir}')
    print('  verilator --lint-only math_ieee754_2008_fp32_multiplier.sv')
    print('  verilator --lint-only math_ieee754_2008_fp16_multiplier.sv')
    print('  verilator --lint-only math_fp8_e4m3_multiplier.sv')
    print('  verilator --lint-only math_fp8_e5m2_multiplier.sv')


if __name__ == '__main__':
    main()
