# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E5M2ExponentAdder
# Purpose: FP8 E5M2 Exponent Adder Generator
#
# Implements exponent addition for FP8 E5M2 multiplication.
# FP8 E5M2: [7]=sign, [6:2]=exp (bias=15), [1:0]=mantissa
#
# For multiplication: exp_result = exp_a + exp_b - bias + norm_adjust
# Bias = 15 for E5M2 format
#
# Note: E5M2 HAS infinity! exp=31, mant=0 is infinity
# NaN: exp=31, mant!=0
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP8E5M2ExponentAdder(Module):
    """
    Generates FP8 E5M2 exponent adder for multiplication.

    Architecture:
    1. Add exponents (5-bit each)
    2. Subtract bias (15)
    3. Add normalization adjustment (+1 if product needs shift)
    4. Detect overflow (exp > 30) and underflow (exp < 1)
    """

    module_str = 'math_fp8_e5m2_exponent_adder'
    port_str = '''
    input  logic [4:0] i_exp_a,        // 5-bit exponent A
    input  logic [4:0] i_exp_b,        // 5-bit exponent B
    input  logic       i_norm_adjust,  // +1 if mantissa product needs normalization
    output logic [4:0] ow_exp_out,     // Result exponent (clamped)
    output logic       ow_overflow,    // Exponent overflow (saturate to inf)
    output logic       ow_underflow,   // Exponent underflow (flush to zero)
    output logic       ow_a_is_zero,   // Input A exponent is zero
    output logic       ow_b_is_zero,   // Input B exponent is zero
    output logic       ow_a_is_inf,    // Input A is infinity (exp=31)
    output logic       ow_b_is_inf     // Input B is infinity (exp=31)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP8 E5M2 exponent adder."""

        self.comment('FP8 E5M2 exponent parameters')
        self.comment('Bias = 15, valid exponent range: 1-30')
        self.comment('exp=31 is infinity (mant=0) or NaN (mant!=0)')
        self.instruction('')

        self.comment('Special case detection')
        self.instruction("wire w_a_is_zero = (i_exp_a == 5'h00);")
        self.instruction("wire w_b_is_zero = (i_exp_b == 5'h00);")
        self.instruction('')
        self.comment('Infinity detection: exp=31')
        self.instruction("wire w_a_is_inf = (i_exp_a == 5'h1F);")
        self.instruction("wire w_b_is_inf = (i_exp_b == 5'h1F);")
        self.instruction('')

        self.comment('Exponent sum: exp_a + exp_b')
        self.comment('Extended to 7 bits to catch overflow')
        self.instruction("wire [6:0] w_exp_sum = {2'b0, i_exp_a} + {2'b0, i_exp_b};")
        self.instruction('')

        self.comment('Subtract bias (15) and add normalization adjustment')
        self.comment('Result = exp_sum - 15 + norm_adjust')
        self.instruction("wire signed [7:0] w_exp_biased = $signed({1'b0, w_exp_sum}) - 8'sd15 + {7'b0, i_norm_adjust};")
        self.instruction('')

        self.comment('Overflow detection: result > 30 (31 reserved for inf/NaN)')
        self.instruction('wire w_overflow = ~w_exp_biased[7] & (w_exp_biased > 8\'sd30);')
        self.instruction('')

        self.comment('Underflow detection: result < 1')
        self.instruction("wire w_underflow = w_exp_biased[7] | (w_exp_biased < 8'sd1);")
        self.instruction('')

        self.comment('Clamp exponent to valid range')
        self.instruction('wire [4:0] w_exp_clamped;')
        self.instruction('assign w_exp_clamped = w_overflow ? 5\'h1F :')
        self.instruction("                       w_underflow ? 5'h00 :")
        self.instruction('                       w_exp_biased[4:0];')
        self.instruction('')

        self.comment('Output assignments')
        self.instruction('assign ow_exp_out = w_exp_clamped;')
        self.instruction('assign ow_overflow = w_overflow;')
        self.instruction('assign ow_underflow = w_underflow;')
        self.instruction('assign ow_a_is_zero = w_a_is_zero;')
        self.instruction('assign ow_b_is_zero = w_b_is_zero;')
        self.instruction('assign ow_a_is_inf = w_a_is_inf;')
        self.instruction('assign ow_b_is_inf = w_b_is_inf;')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='FP8 E5M2 exponent adder for multiplication with bias handling',
            generator_script='fp8_e5m2_exponent_adder.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e5m2_exponent_adder(output_path):
    """Generate FP8 E5M2 exponent adder."""
    adder = FP8E5M2ExponentAdder()
    adder.verilog(output_path)
    return adder.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e5m2_exponent_adder(output_path)
    print(f'Generated: {module_name}.sv')
