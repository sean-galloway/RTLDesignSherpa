# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E4M3ExponentAdder
# Purpose: FP8 E4M3 Exponent Adder Generator
#
# Implements exponent addition for FP8 E4M3 multiplication.
# FP8 E4M3: [7]=sign, [6:3]=exp (bias=7), [2:0]=mantissa
#
# For multiplication: exp_result = exp_a + exp_b - bias + norm_adjust
# Bias = 7 for E4M3 format
#
# Note: E4M3 has NO infinity! exp=15 with non-zero mantissa is NaN,
# exp=15 with zero mantissa is the maximum normal value.
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP8E4M3ExponentAdder(Module):
    """
    Generates FP8 E4M3 exponent adder for multiplication.

    Architecture:
    1. Add exponents (4-bit each)
    2. Subtract bias (7)
    3. Add normalization adjustment (+1 if product needs shift)
    4. Detect overflow (exp > 15) and underflow (exp < 1)
    """

    module_str = 'math_fp8_e4m3_exponent_adder'
    port_str = '''
    input  logic [3:0] i_exp_a,        // 4-bit exponent A
    input  logic [3:0] i_exp_b,        // 4-bit exponent B
    input  logic       i_norm_adjust,  // +1 if mantissa product needs normalization
    output logic [3:0] ow_exp_out,     // Result exponent (clamped)
    output logic       ow_overflow,    // Exponent overflow (saturate to max)
    output logic       ow_underflow,   // Exponent underflow (flush to zero)
    output logic       ow_a_is_zero,   // Input A exponent is zero
    output logic       ow_b_is_zero,   // Input B exponent is zero
    output logic       ow_a_is_nan,    // Input A is NaN (exp=15, mant=111)
    output logic       ow_b_is_nan     // Input B is NaN (exp=15, mant=111)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP8 E4M3 exponent adder."""

        self.comment('FP8 E4M3 exponent parameters')
        self.comment('Bias = 7, valid exponent range: 1-15')
        self.comment('Note: E4M3 has no infinity! exp=15 is valid for max normal value')
        self.instruction('')

        self.comment('Special case detection')
        self.instruction("wire w_a_is_zero = (i_exp_a == 4'h0);")
        self.instruction("wire w_b_is_zero = (i_exp_b == 4'h0);")
        self.instruction('')
        self.comment('NaN detection: exp=15, mantissa=111 (checked externally)')
        self.comment('Here we just detect exp=15 for special handling')
        self.instruction("wire w_a_exp_max = (i_exp_a == 4'hF);")
        self.instruction("wire w_b_exp_max = (i_exp_b == 4'hF);")
        self.instruction('')

        self.comment('Exponent sum: exp_a + exp_b')
        self.comment('Extended to 6 bits to catch overflow')
        self.instruction("wire [5:0] w_exp_sum = {2'b0, i_exp_a} + {2'b0, i_exp_b};")
        self.instruction('')

        self.comment('Subtract bias (7) and add normalization adjustment')
        self.comment('Result = exp_sum - 7 + norm_adjust')
        self.instruction("wire signed [6:0] w_exp_biased = $signed({1'b0, w_exp_sum}) - 7'sd7 + {6'b0, i_norm_adjust};")
        self.instruction('')

        self.comment('Overflow detection: result > 15 (max valid exponent)')
        self.instruction('wire w_overflow = ~w_exp_biased[6] & (w_exp_biased > 7\'sd15);')
        self.instruction('')

        self.comment('Underflow detection: result < 1')
        self.instruction("wire w_underflow = w_exp_biased[6] | (w_exp_biased < 7'sd1);")
        self.instruction('')

        self.comment('Clamp exponent to valid range')
        self.instruction('wire [3:0] w_exp_clamped;')
        self.instruction('assign w_exp_clamped = w_overflow ? 4\'hF :')
        self.instruction("                       w_underflow ? 4'h0 :")
        self.instruction('                       w_exp_biased[3:0];')
        self.instruction('')

        self.comment('Output assignments')
        self.instruction('assign ow_exp_out = w_exp_clamped;')
        self.instruction('assign ow_overflow = w_overflow;')
        self.instruction('assign ow_underflow = w_underflow;')
        self.instruction('assign ow_a_is_zero = w_a_is_zero;')
        self.instruction('assign ow_b_is_zero = w_b_is_zero;')
        self.instruction('assign ow_a_is_nan = w_a_exp_max;  // Partial NaN check (mant check done externally)')
        self.instruction('assign ow_b_is_nan = w_b_exp_max;  // Partial NaN check (mant check done externally)')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='FP8 E4M3 exponent adder for multiplication with bias handling',
            generator_script='fp8_e4m3_exponent_adder.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e4m3_exponent_adder(output_path):
    """Generate FP8 E4M3 exponent adder."""
    adder = FP8E4M3ExponentAdder()
    adder.verilog(output_path)
    return adder.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e4m3_exponent_adder(output_path)
    print(f'Generated: {module_name}.sv')
