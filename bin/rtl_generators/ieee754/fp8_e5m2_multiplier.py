# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E5M2Multiplier
# Purpose: FP8 E5M2 Complete Multiplier Generator
#
# Complete FP8 E5M2 multiplier combining:
# - Mantissa multiplication (3x3 direct multiply)
# - Exponent addition with bias handling
# - Special case handling (zero, inf, NaN, subnormal)
# - RNE (Round-to-Nearest-Even) rounding
#
# FP8 E5M2 format: [7]=sign, [6:2]=exp (bias=15), [1:0]=mantissa
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


class FP8E5M2Multiplier(Module):
    """
    Generates complete FP8 E5M2 multiplier.

    Architecture (combinational):
    1. Field extraction + special case detection
    2. Sign = sign_a XOR sign_b
    3. 3x3 direct multiply -> 6-bit product
    4. Exponent = exp_a + exp_b - 15 + norm_adjust
    5. Normalization + RNE rounding
    6. Special case priority assembly
    """

    module_str = 'math_fp8_e5m2_multiplier'
    port_str = '''
    input  logic [7:0] i_a,           // FP8 E5M2 operand A
    input  logic [7:0] i_b,           // FP8 E5M2 operand B
    output logic [7:0] ow_result,     // FP8 E5M2 result
    output logic       ow_overflow,   // Overflow to infinity
    output logic       ow_underflow,  // Underflow to zero
    output logic       ow_invalid     // Invalid operation (0 * inf)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the complete FP8 E5M2 multiplier."""

        self.comment('FP8 E5M2 field extraction')
        self.comment('Format: [7]=sign, [6:2]=exponent, [1:0]=mantissa')
        self.instruction('')
        self.instruction('wire       w_sign_a = i_a[7];')
        self.instruction('wire [4:0] w_exp_a  = i_a[6:2];')
        self.instruction('wire [1:0] w_mant_a = i_a[1:0];')
        self.instruction('')
        self.instruction('wire       w_sign_b = i_b[7];')
        self.instruction('wire [4:0] w_exp_b  = i_b[6:2];')
        self.instruction('wire [1:0] w_mant_b = i_b[1:0];')
        self.instruction('')

        self.comment('Special value detection')
        self.instruction('')
        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 2'h0);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 2'h0);")
        self.instruction('')
        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 2'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 2'h0);")
        self.instruction('')
        self.comment('Infinity: exp=31, mant=0')
        self.instruction("wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 2'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 2'h0);")
        self.instruction('')
        self.comment('NaN: exp=31, mant!=0')
        self.instruction("wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);")
        self.instruction('')
        self.comment('Effective zero (includes subnormals in FTZ mode)')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('')
        self.comment('Normal number (has implied leading 1)')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        self.comment('Result sign: XOR of input signs')
        self.instruction('wire w_sign_result = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Mantissa multiplication (3x3 direct multiply)')
        self.instruction('wire [5:0] w_mant_product;')
        self.instruction('wire       w_needs_norm;')
        self.instruction('wire [1:0] w_mant_mult_out;')
        self.instruction('wire       w_round_bit;')
        self.instruction('wire       w_sticky_bit;')
        self.instruction('')
        self.instruction('math_fp8_e5m2_mantissa_mult u_mant_mult (')
        self.instruction('    .i_mant_a(w_mant_a),')
        self.instruction('    .i_mant_b(w_mant_b),')
        self.instruction('    .i_a_is_normal(w_a_is_normal),')
        self.instruction('    .i_b_is_normal(w_b_is_normal),')
        self.instruction('    .ow_product(w_mant_product),')
        self.instruction('    .ow_needs_norm(w_needs_norm),')
        self.instruction('    .ow_mant_out(w_mant_mult_out),')
        self.instruction('    .ow_round_bit(w_round_bit),')
        self.instruction('    .ow_sticky_bit(w_sticky_bit)')
        self.instruction(');')
        self.instruction('')

        self.comment('Exponent addition')
        self.instruction('wire [4:0] w_exp_sum;')
        self.instruction('wire       w_exp_overflow;')
        self.instruction('wire       w_exp_underflow;')
        self.instruction('wire       w_exp_a_zero, w_exp_b_zero;')
        self.instruction('wire       w_exp_a_inf, w_exp_b_inf;')
        self.instruction('')
        self.instruction('math_fp8_e5m2_exponent_adder u_exp_add (')
        self.instruction('    .i_exp_a(w_exp_a),')
        self.instruction('    .i_exp_b(w_exp_b),')
        self.instruction('    .i_norm_adjust(w_needs_norm),')
        self.instruction('    .ow_exp_out(w_exp_sum),')
        self.instruction('    .ow_overflow(w_exp_overflow),')
        self.instruction('    .ow_underflow(w_exp_underflow),')
        self.instruction('    .ow_a_is_zero(w_exp_a_zero),')
        self.instruction('    .ow_b_is_zero(w_exp_b_zero),')
        self.instruction('    .ow_a_is_inf(w_exp_a_inf),')
        self.instruction('    .ow_b_is_inf(w_exp_b_inf)')
        self.instruction(');')
        self.instruction('')

        self.comment('Round-to-Nearest-Even (RNE) rounding')
        self.comment('Round up if:')
        self.comment('  - round_bit=1 AND (sticky_bit=1 OR LSB=1)')
        self.instruction('')
        self.instruction('wire w_lsb = w_mant_mult_out[0];')
        self.instruction('wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);')
        self.instruction('')

        self.comment('Apply rounding to mantissa')
        self.instruction("wire [2:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {2'b0, w_round_up};")
        self.instruction('')

        self.comment('Check for mantissa overflow from rounding')
        self.instruction('wire w_mant_round_overflow = w_mant_rounded[2];')
        self.instruction('')

        self.comment('Final mantissa (2 bits)')
        self.instruction('wire [1:0] w_mant_final = w_mant_round_overflow ?')
        self.instruction("    2'h0 : w_mant_rounded[1:0];  // Overflow means 1.0 -> needs exp adjust")
        self.instruction('')

        self.comment('Exponent adjustment for rounding overflow')
        self.instruction("wire [4:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 5'd1) : w_exp_sum;")
        self.instruction('')

        self.comment('Check for exponent overflow after rounding adjustment')
        self.instruction("wire w_final_overflow = w_exp_overflow | (w_exp_final == 5'h1F);")
        self.instruction('')

        self.comment('Special case result handling')
        self.instruction('')
        self.comment('NaN propagation: any NaN input produces NaN output')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan;')
        self.instruction('')
        self.comment('Invalid operation: 0 * inf = NaN')
        self.instruction('wire w_invalid_op = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('')
        self.comment('Zero result: either input is (effective) zero')
        self.instruction('wire w_result_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('')
        self.comment('Infinity result: either input is infinity (and not invalid)')
        self.instruction('wire w_result_inf = (w_a_is_inf | w_b_is_inf) & ~w_invalid_op;')
        self.instruction('')

        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    // Default: normal multiplication result')
        self.instruction('    ow_result = {w_sign_result, w_exp_final, w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    // Special case priority (highest to lowest)')
        self.instruction('    if (w_any_nan | w_invalid_op) begin')
        self.instruction("        // NaN result: canonical qNaN")
        self.instruction("        ow_result = {w_sign_result, 5'h1F, 2'h1};  // qNaN")
        self.instruction('        ow_invalid = w_invalid_op;')
        self.instruction('    end else if (w_result_inf | w_final_overflow) begin')
        self.instruction('        // Infinity result')
        self.instruction("        ow_result = {w_sign_result, 5'h1F, 2'h0};")
        self.instruction('        ow_overflow = w_final_overflow & ~w_result_inf;')
        self.instruction('    end else if (w_result_zero | w_exp_underflow) begin')
        self.instruction('        // Zero result')
        self.instruction("        ow_result = {w_sign_result, 5'h00, 2'h0};")
        self.instruction('        ow_underflow = w_exp_underflow & ~w_result_zero;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='Complete FP8 E5M2 multiplier with special case handling and RNE rounding',
            generator_script='fp8_e5m2_multiplier.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e5m2_multiplier(output_path):
    """Generate complete FP8 E5M2 multiplier."""
    mult = FP8E5M2Multiplier()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e5m2_multiplier(output_path)
    print(f'Generated: {module_name}.sv')
