#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BF16 Generator Master Script
# Purpose: Generate all BF16-related RTL modules
#
# Generated modules:
#   1. math_adder_han_carlson_016.sv      - 16-bit Han-Carlson prefix adder (multiplier CPA)
#   2. math_adder_han_carlson_048.sv      - 48-bit Han-Carlson prefix adder (FMA addition)
#   3. math_multiplier_dadda_4to2_008.sv  - 8x8 Dadda tree with 4:2 compressors
#   4. math_bf16_mantissa_mult.sv         - BF16 mantissa multiplier wrapper
#   5. math_bf16_exponent_adder.sv        - BF16 exponent adder
#   6. math_bf16_multiplier.sv            - Complete BF16 multiplier
#   7. math_bf16_fma.sv                   - BF16 FMA with FP32 accumulator
#
# Usage:
#   python generate_all.py [output_directory]
#
# Default output: rtl/common/
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

import os
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from rtl_generators.bf16.han_carlson_adder import generate_han_carlson_adder
from rtl_generators.bf16.dadda_4to2_multiplier import generate_dadda_4to2_multiplier
from rtl_generators.bf16.bf16_mantissa_mult import generate_bf16_mantissa_mult
from rtl_generators.bf16.bf16_exponent_adder import generate_bf16_exponent_adder
from rtl_generators.bf16.bf16_multiplier import generate_bf16_multiplier
from rtl_generators.bf16.bf16_fma import generate_bf16_fma


def generate_all_bf16_modules(output_dir):
    """
    Generate all BF16-related RTL modules.

    Args:
        output_dir: Directory to write generated files

    Returns:
        List of generated module names
    """
    generated = []

    print(f'BF16 RTL Generator')
    print(f'Output directory: {output_dir}')
    print('-' * 50)

    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # 1. Han-Carlson prefix adder (16-bit for multiplier final CPA)
    print('Generating Han-Carlson adder (16-bit)...')
    name = generate_han_carlson_adder(16, output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 2. Han-Carlson prefix adder (48-bit for FMA wide addition)
    print('Generating Han-Carlson adder (48-bit)...')
    name = generate_han_carlson_adder(48, output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 3. Dadda 4:2 multiplier (8-bit for BF16 mantissa)
    print('Generating Dadda 4:2 multiplier (8-bit)...')
    name = generate_dadda_4to2_multiplier(8, output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 4. BF16 mantissa multiplier
    print('Generating BF16 mantissa multiplier...')
    name = generate_bf16_mantissa_mult(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 5. BF16 exponent adder
    print('Generating BF16 exponent adder...')
    name = generate_bf16_exponent_adder(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 6. Complete BF16 multiplier
    print('Generating BF16 multiplier...')
    name = generate_bf16_multiplier(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    # 7. BF16 FMA with FP32 accumulator
    print('Generating BF16 FMA...')
    name = generate_bf16_fma(output_dir)
    generated.append(name)
    print(f'  Created: {name}.sv')

    print('-' * 50)
    print(f'Generated {len(generated)} modules')

    return generated


def print_dependency_order():
    """Print the module dependency order for synthesis."""
    print('\nModule dependency order (bottom-up):')
    print('  1. math_adder_half.sv              (existing)')
    print('  2. math_adder_full.sv              (existing)')
    print('  3. math_compressor_4to2.sv         (existing)')
    print('  4. math_prefix_cell.sv             (existing)')
    print('  5. math_prefix_cell_gray.sv        (existing)')
    print('  6. count_leading_zeros.sv          (existing)')
    print('  7. math_adder_han_carlson_016.sv')
    print('  8. math_adder_han_carlson_048.sv')
    print('  9. math_multiplier_dadda_4to2_008.sv')
    print(' 10. math_bf16_mantissa_mult.sv')
    print(' 11. math_bf16_exponent_adder.sv')
    print(' 12. math_bf16_multiplier.sv')
    print(' 13. math_bf16_fma.sv')


def main():
    # Get output directory from command line or use default
    if len(sys.argv) > 1:
        output_dir = sys.argv[1]
    else:
        # Default to rtl/common/ relative to repo root
        script_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(os.path.dirname(os.path.dirname(script_dir)))
        output_dir = os.path.join(repo_root, 'rtl', 'common')

    generated = generate_all_bf16_modules(output_dir)
    print_dependency_order()

    print('\nTo verify synthesis:')
    print(f'  cd {output_dir}')
    print('  verilator --lint-only math_bf16_multiplier.sv')
    print('  verilator --lint-only math_bf16_fma.sv')


if __name__ == '__main__':
    main()
