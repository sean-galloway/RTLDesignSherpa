# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E5M2MantissaMult
# Purpose: FP8 E5M2 Mantissa Multiplier Generator
#
# Implements 3x3 mantissa multiplication for FP8 E5M2 format.
# FP8 E5M2: [7]=sign, [6:2]=exp (bias=15), [1:0]=mantissa
#
# Extended mantissa: 3 bits (2 stored + 1 implied)
# Product: 6 bits (3x3)
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP8E5M2MantissaMult(Module):
    """
    Generates FP8 E5M2 mantissa multiplier.

    Architecture:
    1. Extend mantissas with implied 1 (2-bit -> 3-bit)
    2. Direct 3x3 multiplication -> 6-bit product
    3. Normalization detection (bit 5 set)
    4. Extract result mantissa with round/sticky bits
    """

    module_str = 'math_fp8_e5m2_mantissa_mult'
    port_str = '''
    input  logic [1:0] i_mant_a,       // 2-bit mantissa A
    input  logic [1:0] i_mant_b,       // 2-bit mantissa B
    input  logic       i_a_is_normal,  // A has implied 1
    input  logic       i_b_is_normal,  // B has implied 1
    output logic [5:0] ow_product,     // Full 6-bit product
    output logic       ow_needs_norm,  // Product bit 5 set (needs right shift)
    output logic [1:0] ow_mant_out,    // Normalized 2-bit mantissa
    output logic       ow_round_bit,   // Round bit for RNE
    output logic       ow_sticky_bit   // Sticky bit (OR of remaining bits)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP8 E5M2 mantissa multiplier."""

        self.comment('Extend mantissas with implied 1 for normal numbers')
        self.comment('Format: 1.mm (3 bits total)')
        self.instruction('')
        self.instruction("wire [2:0] w_mant_a_ext = i_a_is_normal ? {1'b1, i_mant_a} : 3'h0;")
        self.instruction("wire [2:0] w_mant_b_ext = i_b_is_normal ? {1'b1, i_mant_b} : 3'h0;")
        self.instruction('')

        self.comment('Direct 3x3 multiplication -> 6-bit product')
        self.comment('Product format: xx.xxxx (2 integer bits, 4 fraction bits)')
        self.instruction('wire [5:0] w_product = w_mant_a_ext * w_mant_b_ext;')
        self.instruction('')

        self.comment('Normalization detection')
        self.comment('If bit 5 is set, product is in range [2.0, 4.0)')
        self.comment('Need to shift right by 1 and increment exponent')
        self.instruction('wire w_needs_norm = w_product[5];')
        self.instruction('')

        self.comment('Extract normalized mantissa')
        self.comment('If needs_norm: use bits [4:3] (shift right by 1)')
        self.comment('Else: use bits [3:2]')
        self.instruction('wire [1:0] w_mant_normalized = w_needs_norm ? w_product[4:3] : w_product[3:2];')
        self.instruction('')

        self.comment('Round bit (next bit after mantissa)')
        self.instruction('wire w_round = w_needs_norm ? w_product[2] : w_product[1];')
        self.instruction('')

        self.comment('Sticky bit (OR of remaining bits)')
        self.instruction("wire w_sticky = w_needs_norm ? |w_product[1:0] : w_product[0];")
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
            purpose='FP8 E5M2 3x3 mantissa multiplier with normalization',
            generator_script='fp8_e5m2_mantissa_mult.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e5m2_mantissa_mult(output_path):
    """Generate FP8 E5M2 mantissa multiplier."""
    mult = FP8E5M2MantissaMult()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e5m2_mantissa_mult(output_path)
    print(f'Generated: {module_name}.sv')
