# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E4M3MantissaMult
# Purpose: FP8 E4M3 Mantissa Multiplier Generator
#
# Implements 4x4 mantissa multiplication for FP8 E4M3 format.
# FP8 E4M3: [7]=sign, [6:3]=exp (bias=7), [2:0]=mantissa
#
# Extended mantissa: 4 bits (3 stored + 1 implied)
# Product: 8 bits (4x4)
#
# For such small widths, direct multiplication is more efficient
# than Dadda tree.
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP8E4M3MantissaMult(Module):
    """
    Generates FP8 E4M3 mantissa multiplier.

    Architecture:
    1. Extend mantissas with implied 1 (3-bit -> 4-bit)
    2. Direct 4x4 multiplication -> 8-bit product
    3. Normalization detection (bit 7 set)
    4. Extract result mantissa with round/sticky bits
    """

    module_str = 'math_fp8_e4m3_mantissa_mult'
    port_str = '''
    input  logic [2:0] i_mant_a,       // 3-bit mantissa A
    input  logic [2:0] i_mant_b,       // 3-bit mantissa B
    input  logic       i_a_is_normal,  // A has implied 1
    input  logic       i_b_is_normal,  // B has implied 1
    output logic [7:0] ow_product,     // Full 8-bit product
    output logic       ow_needs_norm,  // Product bit 7 set (needs right shift)
    output logic [2:0] ow_mant_out,    // Normalized 3-bit mantissa
    output logic       ow_round_bit,   // Round bit for RNE
    output logic       ow_sticky_bit   // Sticky bit (OR of remaining bits)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP8 E4M3 mantissa multiplier."""

        self.comment('Extend mantissas with implied 1 for normal numbers')
        self.comment('Format: 1.mmm (4 bits total)')
        self.instruction('')
        self.instruction("wire [3:0] w_mant_a_ext = i_a_is_normal ? {1'b1, i_mant_a} : 4'h0;")
        self.instruction("wire [3:0] w_mant_b_ext = i_b_is_normal ? {1'b1, i_mant_b} : 4'h0;")
        self.instruction('')

        self.comment('Direct 4x4 multiplication -> 8-bit product')
        self.comment('Product format: xx.xxxxxx (2 integer bits, 6 fraction bits)')
        self.instruction('wire [7:0] w_product = w_mant_a_ext * w_mant_b_ext;')
        self.instruction('')

        self.comment('Normalization detection')
        self.comment('If bit 7 is set, product is in range [2.0, 4.0)')
        self.comment('Need to shift right by 1 and increment exponent')
        self.instruction('wire w_needs_norm = w_product[7];')
        self.instruction('')

        self.comment('Extract normalized mantissa')
        self.comment('If needs_norm: use bits [6:4] (shift right by 1)')
        self.comment('Else: use bits [5:3]')
        self.instruction('wire [2:0] w_mant_normalized = w_needs_norm ? w_product[6:4] : w_product[5:3];')
        self.instruction('')

        self.comment('Round bit (next bit after mantissa)')
        self.instruction('wire w_round = w_needs_norm ? w_product[3] : w_product[2];')
        self.instruction('')

        self.comment('Sticky bit (OR of remaining bits)')
        self.instruction("wire w_sticky = w_needs_norm ? |w_product[2:0] : |w_product[1:0];")
        self.instruction('')

        self.comment('Output assignments')
        self.instruction('assign ow_product = w_product;')
        self.instruction('assign ow_needs_norm = w_needs_norm;')
        self.instruction('assign ow_mant_out = w_mant_normalized;')
        self.instruction('assign ow_round_bit = w_round;')
        self.instruction('assign ow_sticky_bit = w_sticky;')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='FP8 E4M3 4x4 mantissa multiplier with normalization',
            generator_script='fp8_e4m3_mantissa_mult.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e4m3_mantissa_mult(output_path):
    """Generate FP8 E4M3 mantissa multiplier."""
    mult = FP8E4M3MantissaMult()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e4m3_mantissa_mult(output_path)
    print(f'Generated: {module_name}.sv')
