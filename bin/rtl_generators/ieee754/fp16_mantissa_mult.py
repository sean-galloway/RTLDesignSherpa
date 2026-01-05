# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16MantissaMult
# Purpose: IEEE 754-2008 FP16 Mantissa Multiplier Generator
#
# Multiplies two 11-bit mantissas (10-bit stored + 1 implied bit) using
# a Dadda tree with 4:2 compressors, producing a 22-bit product.
#
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP16MantissaMult(Module):
    """
    Generates FP16 mantissa multiplier wrapper.

    Takes two 10-bit mantissas, adds implied 1 for normal numbers,
    and multiplies using an 11x11 Dadda tree.

    Outputs:
    - 22-bit raw product
    - Normalization flag (product >= 2.0)
    - Extracted 10-bit mantissa
    - Round and sticky bits for RNE rounding
    """

    module_str = 'math_ieee754_2008_fp16_mantissa_mult'
    port_str = '''
    input  logic [9:0]  i_mant_a,       // FP16 mantissa A (10 bits)
    input  logic [9:0]  i_mant_b,       // FP16 mantissa B (10 bits)
    input  logic        i_a_is_normal,  // A has implied leading 1
    input  logic        i_b_is_normal,  // B has implied leading 1
    output logic [21:0] ow_product,     // Raw 22-bit product
    output logic        ow_needs_norm,  // Product >= 2.0, needs right shift
    output logic [9:0]  ow_mant_out,    // Normalized 10-bit mantissa
    output logic        ow_round_bit,   // Round bit for RNE
    output logic        ow_sticky_bit   // Sticky bit (OR of remaining bits)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP16 mantissa multiplier."""

        self.comment('Extended mantissas with implied leading 1')
        self.comment('For normal numbers: 1.mantissa (11 bits total)')
        self.comment('For zero/subnormal: 0.mantissa (FTZ mode)')
        self.instruction('')
        self.instruction("wire [10:0] w_mant_a_ext = i_a_is_normal ? {1'b1, i_mant_a} : 11'h0;")
        self.instruction("wire [10:0] w_mant_b_ext = i_b_is_normal ? {1'b1, i_mant_b} : 11'h0;")
        self.instruction('')

        self.comment('11x11 Dadda tree multiplication')
        self.comment('Product range: 1.0 * 1.0 = 1.0 to 1.999... * 1.999... = 3.999...')
        self.comment('Format: xx.xxxx_xxxx_xxxx_xxxx_xxxx (2 integer + 20 fraction bits)')
        self.instruction('math_multiplier_dadda_4to2_011 u_dadda_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(ow_product)')
        self.instruction(');')
        self.instruction('')

        self.comment('Normalization detection')
        self.comment('If bit[21] = 1, product >= 2.0, need to shift right by 1')
        self.instruction('assign ow_needs_norm = ow_product[21];')
        self.instruction('')

        self.comment('Extract 10-bit mantissa based on normalization')
        self.comment('If needs_norm: take bits [20:11] (shift right)')
        self.comment('If not: take bits [19:10] (no shift)')
        self.instruction('assign ow_mant_out = ow_needs_norm ? ow_product[20:11] : ow_product[19:10];')
        self.instruction('')

        self.comment('Round bit (first bit after mantissa)')
        self.instruction('assign ow_round_bit = ow_needs_norm ? ow_product[10] : ow_product[9];')
        self.instruction('')

        self.comment('Sticky bit (OR of all bits after round bit)')
        self.instruction('assign ow_sticky_bit = ow_needs_norm ? |ow_product[9:0] : |ow_product[8:0];')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP16 mantissa multiplier using 11x11 Dadda tree',
            generator_script='fp16_mantissa_mult.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp16_mantissa_mult(output_path):
    """Generate FP16 mantissa multiplier."""
    mult = FP16MantissaMult()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_mantissa_mult(output_path)
    print(f'Generated: {module_name}.sv')
