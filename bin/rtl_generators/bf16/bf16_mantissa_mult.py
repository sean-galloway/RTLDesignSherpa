# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BF16MantissaMult
# Purpose: BF16 Mantissa Multiplier Generator
#
# BF16 has a 7-bit explicit mantissa with an implied leading 1 for normalized
# numbers. This creates an 8x8 unsigned multiply:
#   {1, mantissa_a[6:0]} * {1, mantissa_b[6:0]} = 16-bit product
#
# The product is in format 1x.xxxxxx_xxxxxxxx or 01.xxxxxx_xxxxxxxx
# If MSB is 1, the result needs normalization (right shift + exponent increment)
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class BF16MantissaMult(Module):
    """
    Generates BF16 mantissa multiplier.

    Features:
    - 8x8 unsigned multiply (7-bit explicit + 1 implied bit)
    - Uses Dadda 4:2 compressor tree
    - Outputs 16-bit product with normalization indicator
    - Optional rounding support (round-to-nearest-even)
    """

    module_str = 'math_bf16_mantissa_mult'
    port_str = '''
    input  logic [6:0]  i_mant_a,      // 7-bit explicit mantissa A
    input  logic [6:0]  i_mant_b,      // 7-bit explicit mantissa B
    input  logic        i_a_is_normal, // A has implied leading 1
    input  logic        i_b_is_normal, // B has implied leading 1
    output logic [15:0] ow_product,    // 16-bit raw product
    output logic        ow_needs_norm, // 1 if product >= 2.0 (MSB set)
    output logic [6:0]  ow_mant_out,   // 7-bit result mantissa (post-norm)
    output logic        ow_round_bit,  // Round bit for RNE
    output logic        ow_sticky_bit  // Sticky bit for RNE
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_mantissa_extension(self):
        """Extend 7-bit mantissa to 8-bit with implied leading bit."""
        self.comment('Extend mantissa with implied leading 1 for normalized numbers')
        self.instruction('wire [7:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};')
        self.instruction('wire [7:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};')
        self.instruction('')

    def generate_multiplier_instantiation(self):
        """Instantiate the 8x8 Dadda multiplier."""
        self.comment('8x8 unsigned multiply using Dadda tree with 4:2 compressors')
        self.instruction('math_multiplier_dadda_4to2_008 u_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(ow_product)')
        self.instruction(');')
        self.instruction('')

    def generate_normalization_detection(self):
        """Detect if product needs normalization."""
        self.comment('Normalization detection')
        self.comment('Product is in range [0, 4) before normalization')
        self.comment('If MSB (bit 15) is set: product >= 2.0, needs right shift')
        self.instruction('assign ow_needs_norm = ow_product[15];')
        self.instruction('')

    def generate_mantissa_extraction(self):
        """Extract 7-bit result mantissa based on normalization."""
        self.comment('Extract result mantissa')
        self.comment('If needs_norm: take bits [14:8] (after implied 1)')
        self.comment('If not: take bits [13:7] (no shift needed)')
        self.instruction('')
        self.comment('Normalized case: 1x.xxxxxx_xxxxxxxx -> take [14:8]')
        self.comment('Non-normalized: 01.xxxxxx_xxxxxxxx -> take [13:7]')
        self.instruction('assign ow_mant_out = ow_needs_norm ? ow_product[14:8] : ow_product[13:7];')
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
        self.comment('  mantissa = [14:8], G = [7], R = [6], S = |[5:0]')
        self.comment('If not needs_norm (product < 2):')
        self.comment('  mantissa = [13:7], G = [6], R = [5], S = |[4:0]')
        self.instruction('')
        self.instruction('wire w_guard_norm    = ow_product[7];')
        self.instruction('wire w_guard_nonorm  = ow_product[6];')
        self.instruction('')
        self.instruction('wire w_round_norm    = ow_product[6];')
        self.instruction('wire w_round_nonorm  = ow_product[5];')
        self.instruction('')
        self.instruction('wire w_sticky_norm   = |ow_product[5:0];')
        self.instruction('wire w_sticky_nonorm = |ow_product[4:0];')
        self.instruction('')
        self.instruction('assign ow_round_bit  = ow_needs_norm ? w_round_norm  : w_round_nonorm;')
        self.instruction('assign ow_sticky_bit = ow_needs_norm ? ')
        self.instruction('    (w_guard_norm | w_sticky_norm) : (w_guard_nonorm | w_sticky_nonorm);')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete BF16 mantissa multiplier."""
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
            purpose='BF16 mantissa multiplier (8x8 with normalization and rounding)',
            generator_script='bf16_mantissa_mult.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_bf16_mantissa_mult(output_path):
    """
    Generate BF16 mantissa multiplier.

    Args:
        output_path: Directory to write the generated file
    """
    mult = BF16MantissaMult()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_bf16_mantissa_mult(output_path)
    print(f'Generated: {module_name}.sv')
