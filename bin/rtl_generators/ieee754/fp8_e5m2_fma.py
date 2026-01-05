# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E5M2FMA
# Purpose: FP8 E5M2 Fused Multiply-Add Generator
#
# Implements FMA: result = (a * b) + c for FP8 E5M2 format.
# FP8 E5M2: [7]=sign, [6:2]=exp (bias=15), [1:0]=mantissa
#
# Extended precision: 12-bit accumulator for intermediate results
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


class FP8E5M2FMA(Module):
    """
    Generates FP8 E5M2 Fused Multiply-Add unit.

    Architecture:
    1. Multiply a * b (3x3 -> 6-bit product)
    2. Align c with product exponent
    3. Add/subtract aligned mantissas (12-bit accumulator)
    4. Normalize and round result
    5. Handle special cases
    """

    module_str = 'math_fp8_e5m2_fma'
    port_str = '''
    input  logic [7:0] i_a,           // FP8 E5M2 multiplicand
    input  logic [7:0] i_b,           // FP8 E5M2 multiplier
    input  logic [7:0] i_c,           // FP8 E5M2 addend
    output logic [7:0] ow_result,     // FP8 E5M2 result
    output logic       ow_overflow,   // Overflow flag
    output logic       ow_underflow,  // Underflow flag
    output logic       ow_invalid     // Invalid operation flag
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP8 E5M2 FMA."""

        self.generate_field_extraction()
        self.generate_special_cases()
        self.generate_multiplication()
        self.generate_alignment()
        self.generate_addition()
        self.generate_normalization()
        self.generate_rounding_and_packing()
        self.generate_result_assembly()

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='FP8 E5M2 Fused Multiply-Add with 12-bit internal precision',
            generator_script='fp8_e5m2_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')

    def generate_field_extraction(self):
        """Generate field extraction for all three operands."""
        self.comment('FP8 E5M2 field extraction')
        self.comment('Format: [7]=sign, [6:2]=exp, [1:0]=mant')
        self.instruction('')
        self.comment('Operand A')
        self.instruction('wire       w_sign_a = i_a[7];')
        self.instruction('wire [4:0] w_exp_a  = i_a[6:2];')
        self.instruction('wire [1:0] w_mant_a = i_a[1:0];')
        self.instruction('')
        self.comment('Operand B')
        self.instruction('wire       w_sign_b = i_b[7];')
        self.instruction('wire [4:0] w_exp_b  = i_b[6:2];')
        self.instruction('wire [1:0] w_mant_b = i_b[1:0];')
        self.instruction('')
        self.comment('Operand C (addend)')
        self.instruction('wire       w_sign_c = i_c[7];')
        self.instruction('wire [4:0] w_exp_c  = i_c[6:2];')
        self.instruction('wire [1:0] w_mant_c = i_c[1:0];')
        self.instruction('')

    def generate_special_cases(self):
        """Generate special case detection."""
        self.comment('Special case detection')
        self.instruction('')
        self.comment('Zero detection')
        self.instruction("wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 2'h0);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 2'h0);")
        self.instruction("wire w_c_is_zero = (w_exp_c == 5'h00) & (w_mant_c == 2'h0);")
        self.instruction('')
        self.comment('Subnormal detection (FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 2'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 2'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 5'h00) & (w_mant_c != 2'h0);")
        self.instruction('')
        self.comment('Infinity detection (E5M2: exp=31, mant=0)')
        self.instruction("wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 2'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 2'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 5'h1F) & (w_mant_c == 2'h0);")
        self.instruction('')
        self.comment('NaN detection (E5M2: exp=31, mant!=0)')
        self.instruction("wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 5'h1F) & (w_mant_c != 2'h0);")
        self.instruction('')
        self.comment('Effective zero (includes subnormals)')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;')
        self.instruction('')
        self.comment('Normal number check')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;')
        self.instruction('')

    def generate_multiplication(self):
        """Generate the mantissa multiplication stage."""
        self.comment('Mantissa multiplication (a * b)')
        self.instruction('')
        self.comment('Extended mantissas with implied 1 (3-bit)')
        self.instruction("wire [2:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 3'h0;")
        self.instruction("wire [2:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 3'h0;")
        self.instruction('')
        self.comment('3x3 multiplication -> 6-bit product')
        self.instruction('wire [5:0] w_prod_mant = w_mant_a_ext * w_mant_b_ext;')
        self.instruction('')
        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')
        self.comment('Product exponent (before normalization)')
        self.comment('exp_prod = exp_a + exp_b - bias(15)')
        self.instruction("wire [6:0] w_prod_exp_sum = {2'b0, w_exp_a} + {2'b0, w_exp_b};")
        self.instruction("wire signed [7:0] w_prod_exp_raw = $signed({1'b0, w_prod_exp_sum}) - 8'sd15;")
        self.instruction('')
        self.comment('Normalize product (check if bit 5 is set)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant[5];')
        self.instruction('wire [5:0] w_prod_mant_norm = w_prod_needs_norm ? w_prod_mant : {w_prod_mant[4:0], 1\'b0};')
        self.instruction("wire signed [7:0] w_prod_exp = w_prod_exp_raw + {7'b0, w_prod_needs_norm};")
        self.instruction('')

    def generate_alignment(self):
        """Generate addend alignment logic."""
        self.comment('Addend alignment')
        self.instruction('')
        self.comment('Extended addend mantissa with implied 1 (3-bit)')
        self.instruction("wire [2:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 3'h0;")
        self.instruction('')
        self.comment('Exponent difference for alignment')
        self.instruction("wire [6:0] w_exp_c_ext = {2'b0, w_exp_c};")
        self.instruction("wire signed [7:0] w_exp_diff = w_prod_exp - $signed({1'b0, w_exp_c_ext});")
        self.instruction('')
        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [5:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff[5:0] : (~w_exp_diff[5:0] + 6'd1);")
        self.instruction('')
        self.comment('Clamp shift amount (12-bit max)')
        self.instruction("wire [3:0] w_shift_clamped = (w_shift_amt > 6'd11) ? 4'd11 : w_shift_amt[3:0];")
        self.instruction('')
        self.comment('Extended mantissas for addition (12 bits)')
        self.instruction("wire [11:0] w_prod_mant_12 = {w_prod_mant_norm, 6'b0};")
        self.instruction("wire [11:0] w_c_mant_12    = {w_mant_c_ext, 9'b0};")
        self.instruction('')
        self.comment('Aligned mantissas')
        self.instruction('wire [11:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire [5:0]  w_exp_result_pre;')
        self.instruction('')
        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_12 : w_c_mant_12;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_12 >> w_shift_clamped) : (w_prod_mant_12 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction("assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp[5:0] : w_exp_c_ext[5:0];")
        self.instruction('')

    def generate_addition(self):
        """Generate the mantissa addition/subtraction logic."""
        self.comment('Mantissa addition/subtraction (12-bit)')
        self.instruction('')
        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')
        self.instruction('wire [12:0] w_sum_raw = w_effective_sub ?')
        self.instruction("    {1'b0, w_mant_larger} - {1'b0, w_mant_smaller_shifted} :")
        self.instruction("    {1'b0, w_mant_larger} + {1'b0, w_mant_smaller_shifted};")
        self.instruction('')
        self.comment('Handle negative result from subtraction')
        self.instruction('wire w_sum_negative = w_effective_sub & w_sum_raw[12];')
        self.instruction('wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;')
        self.instruction("wire [12:0] w_sum_abs = w_sum_negative ? (~w_sum_raw + 13'd1) : w_sum_raw;")
        self.instruction('')
        self.comment('Check for addition overflow')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_sum_abs[12];')
        self.instruction('')
        self.comment('Adjust for overflow')
        self.instruction("wire [11:0] w_sum_12 = w_add_overflow ? w_sum_abs[12:1] : w_sum_abs[11:0];")
        self.instruction('')

    def generate_normalization(self):
        """Generate the normalization logic."""
        self.comment('Normalization')
        self.instruction('')
        self.comment('Find leading one using priority encoder')
        self.instruction('wire [3:0] w_lz_count;')
        self.instruction('assign w_lz_count = w_sum_12[11] ? 4\'d0 :')
        self.instruction("                    w_sum_12[10] ? 4'd1 :")
        self.instruction("                    w_sum_12[9]  ? 4'd2 :")
        self.instruction("                    w_sum_12[8]  ? 4'd3 :")
        self.instruction("                    w_sum_12[7]  ? 4'd4 :")
        self.instruction("                    w_sum_12[6]  ? 4'd5 :")
        self.instruction("                    w_sum_12[5]  ? 4'd6 :")
        self.instruction("                    w_sum_12[4]  ? 4'd7 :")
        self.instruction("                    w_sum_12[3]  ? 4'd8 :")
        self.instruction("                    w_sum_12[2]  ? 4'd9 :")
        self.instruction("                    w_sum_12[1]  ? 4'd10 : 4'd11;")
        self.instruction('')
        self.comment('Normalized mantissa')
        self.instruction('wire [11:0] w_mant_normalized = w_sum_12 << w_lz_count;')
        self.instruction('')
        self.comment('Adjusted exponent')
        self.instruction("wire signed [7:0] w_exp_adjusted = $signed({2'b0, w_exp_result_pre}) -")
        self.instruction("    $signed({4'b0, w_lz_count}) + {7'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP8 packing."""
        self.comment('Round-to-Nearest-Even and FP8 packing')
        self.instruction('')
        self.comment('Extract mantissa bits [11:10], guard [9], round [8], sticky [7:0]')
        self.instruction('wire [1:0] w_mant_pre = w_mant_normalized[10:9];')
        self.instruction('wire w_guard = w_mant_normalized[8];')
        self.instruction('wire w_round = w_mant_normalized[7];')
        self.instruction('wire w_sticky = |w_mant_normalized[6:0];')
        self.instruction('')
        self.comment('RNE rounding')
        self.instruction('wire w_round_up = w_guard & (w_round | w_sticky | w_mant_pre[0]);')
        self.instruction('')
        self.comment('Apply rounding')
        self.instruction("wire [2:0] w_mant_rounded = {1'b0, w_mant_pre} + {2'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[2];')
        self.instruction('')
        self.comment('Final mantissa and exponent')
        self.instruction("wire [1:0] w_mant_final = w_round_overflow ? 2'h0 : w_mant_rounded[1:0];")
        self.instruction("wire signed [7:0] w_exp_final = w_exp_adjusted + {7'b0, w_round_overflow};")
        self.instruction('')

    def generate_result_assembly(self):
        """Generate final result assembly with special cases."""
        self.comment('Special case handling')
        self.instruction('')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;')
        self.instruction('wire w_prod_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('wire w_prod_inf = (w_a_is_inf | w_b_is_inf) & ~w_prod_zero;')
        self.instruction('')
        self.comment('Invalid: 0 * inf or inf - inf')
        self.instruction('wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('wire w_invalid_add = w_prod_inf & w_c_is_inf & (w_prod_sign != w_sign_c);')
        self.instruction('wire w_invalid = w_invalid_mul | w_invalid_add;')
        self.instruction('')
        self.comment('Overflow: exp > 30')
        self.instruction('wire w_overflow = ~w_exp_final[7] & (w_exp_final > 8\'sd30);')
        self.instruction('')
        self.comment('Underflow: exp < 1')
        self.instruction("wire w_underflow = w_exp_final[7] | (w_exp_final < 8'sd1);")
        self.instruction('')
        self.comment('Sum is zero')
        self.instruction("wire w_sum_is_zero = (w_sum_12 == 12'h0);")
        self.instruction('')
        self.comment('Infinity sign selection')
        self.instruction('wire w_inf_sign = w_prod_inf ? w_prod_sign : w_c_is_inf ? w_sign_c : w_result_sign;')
        self.instruction('')
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 5'h1F, 2'h1};  // Canonical qNaN")
        self.instruction("        ow_invalid = w_invalid;")
        self.instruction('    end else if (w_prod_inf | w_c_is_inf | w_overflow) begin')
        self.instruction("        ow_result = {w_inf_sign, 5'h1F, 2'h0};  // Infinity")
        self.instruction("        ow_overflow = w_overflow & ~w_prod_inf & ~w_c_is_inf;")
        self.instruction('    end else if (w_underflow | w_sum_is_zero) begin')
        self.instruction("        ow_result = {w_result_sign, 5'h00, 2'h0};")
        self.instruction("        ow_underflow = w_underflow & ~w_sum_is_zero;")
        self.instruction('    end else if (w_prod_zero) begin')
        self.instruction('        ow_result = i_c;  // 0 * b + c = c')
        self.instruction('    end else if (w_c_eff_zero) begin')
        self.instruction('        // a * b + 0 = a * b')
        self.instruction("        ow_result = {w_prod_sign, w_prod_exp[4:0], w_prod_mant_norm[4:3]};")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')


def generate_fp8_e5m2_fma(output_path):
    """Generate FP8 E5M2 FMA."""
    fma = FP8E5M2FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e5m2_fma(output_path)
    print(f'Generated: {module_name}.sv')
