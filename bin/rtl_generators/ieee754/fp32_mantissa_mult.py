# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32MantissaMult
# Purpose: IEEE 754-2008 FP32 Mantissa Multiplier Generator
#
# FP32 has a 23-bit explicit mantissa with an implied leading 1 for normalized
# numbers. This creates a 24x24 unsigned multiply:
#   {1, mantissa_a[22:0]} * {1, mantissa_b[22:0]} = 48-bit product
#
# The product is in format 1x.xxxxxx...xxxxxxx or 01.xxxxxx...xxxxxxx
# If MSB is 1, the result needs normalization (right shift + exponent increment)
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP32MantissaMult(Module):
    """
    Generates FP32 mantissa multiplier.

    Features:
    - 24x24 unsigned multiply (23-bit explicit + 1 implied bit)
    - Uses Dadda 4:2 compressor tree
    - Outputs 48-bit product with normalization indicator
    - Round-to-nearest-even (RNE) support with guard/round/sticky bits
    """

    module_str = 'math_ieee754_2008_fp32_mantissa_mult'
    port_str = '''
    input  logic [22:0] i_mant_a,      // 23-bit explicit mantissa A
    input  logic [22:0] i_mant_b,      // 23-bit explicit mantissa B
    input  logic        i_a_is_normal, // A has implied leading 1
    input  logic        i_b_is_normal, // B has implied leading 1
    output logic [47:0] ow_product,    // 48-bit raw product
    output logic        ow_needs_norm, // 1 if product >= 2.0 (MSB set)
    output logic [22:0] ow_mant_out,   // 23-bit result mantissa (post-norm)
    output logic        ow_round_bit,  // Round bit for RNE
    output logic        ow_sticky_bit  // Sticky bit for RNE
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_mantissa_extension(self):
        """Extend 23-bit mantissa to 24-bit with implied leading bit."""
        self.comment('Extend mantissa with implied leading 1 for normalized numbers')
        self.instruction('wire [23:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};')
        self.instruction('wire [23:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};')
        self.instruction('')

    def generate_multiplier_instantiation(self):
        """Instantiate the 24x24 Dadda multiplier."""
        self.comment('24x24 unsigned multiply using Dadda tree with 4:2 compressors')
        self.instruction('math_multiplier_dadda_4to2_024 u_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(ow_product)')
        self.instruction(');')
        self.instruction('')

    def generate_normalization_detection(self):
        """Detect if product needs normalization."""
        self.comment('Normalization detection')
        self.comment('Product is in range [0, 4) before normalization')
        self.comment('If MSB (bit 47) is set: product >= 2.0, needs right shift')
        self.instruction('assign ow_needs_norm = ow_product[47];')
        self.instruction('')

    def generate_mantissa_extraction(self):
        """Extract 23-bit result mantissa based on normalization."""
        self.comment('Extract result mantissa')
        self.comment('If needs_norm: take bits [46:24] (after implied 1)')
        self.comment('If not: take bits [45:23] (no shift needed)')
        self.instruction('')
        self.comment('Normalized case:     1x.xxxxxxx...xxxxxxx -> take [46:24]')
        self.comment('Non-normalized case: 01.xxxxxxx...xxxxxxx -> take [45:23]')
        self.instruction('assign ow_mant_out = ow_needs_norm ? ow_product[46:24] : ow_product[45:23];')
        self.instruction('')

    def generate_rounding_bits(self):
        """Generate round and sticky bits for round-to-nearest-even."""
        self.comment('Rounding support (Round-to-Nearest-Even)')
        self.comment('')
        self.comment('For RNE, we need:')
        self.comment('  - Guard bit (G): first bit after mantissa')
        self.comment('  - Round bit (R): second bit after mantissa')
        self.comment('  - Sticky bit (S): OR of all remaining bits')
        self.comment('')
        self.comment('If needs_norm (product >= 2):')
        self.comment('  mantissa = [46:24], G = [23], R = [22], S = |[21:0]')
        self.comment('If not needs_norm (product < 2):')
        self.comment('  mantissa = [45:23], G = [22], R = [21], S = |[20:0]')
        self.instruction('')
        self.instruction('wire w_guard_norm    = ow_product[23];')
        self.instruction('wire w_guard_nonorm  = ow_product[22];')
        self.instruction('')
        self.instruction('wire w_round_norm    = ow_product[22];')
        self.instruction('wire w_round_nonorm  = ow_product[21];')
        self.instruction('')
        self.instruction('wire w_sticky_norm   = |ow_product[21:0];')
        self.instruction('wire w_sticky_nonorm = |ow_product[20:0];')
        self.instruction('')
        self.instruction('assign ow_round_bit  = ow_needs_norm ? w_round_norm  : w_round_nonorm;')
        self.instruction('assign ow_sticky_bit = ow_needs_norm ? ')
        self.instruction('    (w_guard_norm | w_sticky_norm) : (w_guard_nonorm | w_sticky_nonorm);')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 mantissa multiplier."""
        self.generate_mantissa_extension()
        self.generate_multiplier_instantiation()
        self.generate_normalization_detection()
        self.generate_mantissa_extraction()
        self.generate_rounding_bits()

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 mantissa multiplier (24x24 with normalization and rounding)',
            generator_script='fp32_mantissa_mult.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_mantissa_mult(output_path):
    """
    Generate FP32 mantissa multiplier.

    Args:
        output_path: Directory to write the generated file
    """
    mult = FP32MantissaMult()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_mantissa_mult(output_path)
    print(f'Generated: {module_name}.sv')
