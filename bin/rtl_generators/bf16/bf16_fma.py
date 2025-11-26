# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BF16FMA
# Purpose: BF16 Fused Multiply-Add with FP32 Accumulator Generator
#
# Implements FMA: result = (a * b) + c
# Where a and b are BF16, and c/result are FP32.
#
# This follows industry standard practice for AI training:
# - BF16 inputs for reduced memory bandwidth
# - FP32 accumulation for numerical stability
# - Single rounding (fused operation)
#
# Key insight: BF16 is simply the top 16 bits of FP32:
#   BF16 sign/exp = FP32 sign/exp (identical)
#   BF16 mantissa = FP32 mantissa[22:16] (truncated)
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class BF16FMA(Module):
    """
    Generates BF16 FMA with FP32 accumulator.

    Architecture:
    1. BF16 multiplication (8x8 mantissa, reuse existing multiplier logic)
    2. Extend BF16 product to FP32 precision
    3. Align addend (FP32 c) with product
    4. Add aligned values
    5. Normalize and round to FP32

    This provides the accuracy benefits of FP32 accumulation while
    reducing memory traffic with BF16 operands.
    """

    module_str = 'math_bf16_fma'
    port_str = '''
    input  logic [15:0] i_a,           // BF16 operand A
    input  logic [15:0] i_b,           // BF16 operand B
    input  logic [31:0] i_c,           // FP32 addend/accumulator
    output logic [31:0] ow_result,     // FP32 result = (a * b) + c
    output logic        ow_overflow,   // Overflow
    output logic        ow_underflow,  // Underflow
    output logic        ow_invalid     // Invalid operation (NaN)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_bf16_field_extraction(self):
        """Extract fields from BF16 operands."""
        self.comment('BF16 field extraction')
        self.comment('BF16: [15]=sign, [14:7]=exp, [6:0]=mant')
        self.instruction('')
        self.instruction('wire       w_sign_a = i_a[15];')
        self.instruction('wire [7:0] w_exp_a  = i_a[14:7];')
        self.instruction('wire [6:0] w_mant_a = i_a[6:0];')
        self.instruction('')
        self.instruction('wire       w_sign_b = i_b[15];')
        self.instruction('wire [7:0] w_exp_b  = i_b[14:7];')
        self.instruction('wire [6:0] w_mant_b = i_b[6:0];')
        self.instruction('')

    def generate_fp32_field_extraction(self):
        """Extract fields from FP32 addend."""
        self.comment('FP32 field extraction')
        self.comment('FP32: [31]=sign, [30:23]=exp, [22:0]=mant')
        self.instruction('')
        self.instruction('wire        w_sign_c  = i_c[31];')
        self.instruction('wire [7:0]  w_exp_c   = i_c[30:23];')
        self.instruction('wire [22:0] w_mant_c  = i_c[22:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special cases for all operands."""
        self.comment('Special case detection - BF16 operands')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);")
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);")
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);")
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);")
        self.instruction('')

        self.comment('Effective zero (FTZ for subnormals)')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        self.comment('Special case detection - FP32 addend')
        self.instruction("wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);")
        self.instruction('wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;')
        self.instruction('wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;')
        self.instruction('')

    def generate_product_computation(self):
        """Generate BF16 product computation."""
        self.comment('BF16 multiplication: a * b')
        self.instruction('')

        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Mantissa multiplication (8x8 with implied 1)')
        self.instruction('wire [7:0] w_mant_a_ext = {w_a_is_normal, w_mant_a};')
        self.instruction('wire [7:0] w_mant_b_ext = {w_b_is_normal, w_mant_b};')
        self.instruction('')
        self.instruction('wire [15:0] w_prod_mant_raw;')
        self.instruction('math_multiplier_dadda_4to2_008 u_mant_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(w_prod_mant_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Product exponent: exp_a + exp_b - bias')
        self.instruction("wire [9:0] w_prod_exp_raw = {2'b0, w_exp_a} + {2'b0, w_exp_b} - 10'd127;")
        self.instruction('')

        self.comment('Normalization detection (product >= 2.0)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant_raw[15];')
        self.instruction('')

        self.comment('Normalized product exponent')
        self.instruction("wire [9:0] w_prod_exp = w_prod_exp_raw + {9'b0, w_prod_needs_norm};")
        self.instruction('')

        self.comment('Extended product mantissa to FP32 precision (23 bits)')
        self.comment('Product is either 1x.xxxxxxx_xxxxxxxx or 01.xxxxxx_xxxxxxxxx')
        self.instruction('wire [23:0] w_prod_mant_ext;  // With implied 1')
        self.instruction('assign w_prod_mant_ext = w_prod_needs_norm ?')
        self.instruction("    {1'b1, w_prod_mant_raw[14:0], 8'b0} :  // Shift right, add zeros")
        self.instruction("    {1'b1, w_prod_mant_raw[13:0], 9'b0};   // No shift")
        self.instruction('')

    def generate_addend_alignment(self):
        """Generate addend alignment logic."""
        self.comment('Addend (c) alignment')
        self.comment('Need to align c with product based on exponent difference')
        self.instruction('')

        self.comment('Extended addend mantissa with implied 1')
        self.instruction("wire [23:0] w_c_mant_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;")
        self.instruction('')

        self.comment('Exponent difference for alignment')
        self.instruction("wire [9:0] w_exp_c_ext = {2'b0, w_exp_c};")
        self.instruction('wire signed [10:0] w_exp_diff = $signed({1\'b0, w_prod_exp}) - $signed({1\'b0, w_exp_c_ext});')
        self.instruction('')

        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [9:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff[9:0] : (~w_exp_diff[9:0] + 10'd1);")
        self.instruction('')

        self.comment('Clamp shift amount to prevent over-shifting')
        self.instruction("wire [5:0] w_shift_clamped = (w_shift_amt > 10'd48) ? 6'd48 : w_shift_amt[5:0];")
        self.instruction('')

        self.comment('Extended mantissas for addition (48 bits to capture all precision)')
        self.instruction("wire [47:0] w_prod_mant_48 = {w_prod_mant_ext, 24'b0};")
        self.instruction("wire [47:0] w_c_mant_48    = {w_c_mant_ext, 24'b0};")
        self.instruction('')

        self.comment('Aligned mantissas')
        self.instruction('wire [47:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire [9:0]  w_exp_result_pre;')
        self.instruction('')
        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_48 : w_c_mant_48;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_48 >> w_shift_clamped) : (w_prod_mant_48 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction('assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp : w_exp_c_ext;')
        self.instruction('')

    def generate_addition(self):
        """Generate the addition of product and addend using structural adder."""
        self.comment('Addition of aligned mantissas using Han-Carlson structural adder')
        self.instruction('')

        self.comment('Effective operation: add or subtract based on signs')
        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')

        self.comment('For subtraction, invert smaller operand (two\'s complement: ~B + 1)')
        self.comment('The +1 is handled via carry-in to the adder')
        self.instruction('wire [47:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;')
        self.instruction('')

        self.comment('48-bit Han-Carlson structural adder')
        self.instruction('wire [47:0] w_adder_sum;')
        self.instruction('wire        w_adder_cout;')
        self.instruction('math_adder_han_carlson_048 u_wide_adder (')
        self.instruction('    .i_a(w_mant_larger),')
        self.instruction('    .i_b(w_adder_b),')
        self.instruction('    .i_cin(w_effective_sub),  // +1 for two\'s complement subtraction')
        self.instruction('    .ow_sum(w_adder_sum),')
        self.instruction('    .ow_cout(w_adder_cout)')
        self.instruction(');')
        self.instruction('')

        self.comment('Result sign determination')
        self.comment('For subtraction: if no carry out, result is negative (A < B)')
        self.comment('For addition: carry out means magnitude overflow (need right shift)')
        self.instruction('wire w_sum_negative = w_effective_sub & ~w_adder_cout;')
        self.instruction('wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;')
        self.instruction('')

        self.comment('Absolute value of result')
        self.comment('If negative (subtraction with A < B), need to negate the result')
        self.instruction('wire [47:0] w_negated_sum;')
        self.instruction('wire        w_neg_cout;')
        self.instruction('math_adder_han_carlson_048 u_negate_adder (')
        self.instruction('    .i_a(~w_adder_sum),')
        self.instruction("    .i_b(48'h0),")
        self.instruction("    .i_cin(1'b1),  // ~sum + 1 = -sum")
        self.instruction('    .ow_sum(w_negated_sum),')
        self.instruction('    .ow_cout(w_neg_cout)')
        self.instruction(');')
        self.instruction('')

        self.comment('Handle addition overflow (carry out for same-sign addition)')
        self.comment('When addition overflows, prepend carry bit and shift right')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_adder_cout;')
        self.instruction('wire [47:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[47:1]};  // Right shift, prepend carry')
        self.instruction('')

        self.comment('Select appropriate absolute value')
        self.instruction('wire [47:0] w_sum_abs = w_sum_negative ? w_negated_sum :')
        self.instruction('                        w_add_overflow ? w_sum_with_carry : w_adder_sum;')
        self.instruction('')

    def generate_normalization(self):
        """Generate normalization logic."""
        self.comment('Normalization')
        self.instruction('')

        self.comment('Count leading zeros for normalization')
        self.comment('NOTE: count_leading_zeros module counts from bit[0] (trailing zeros)')
        self.comment('To get actual leading zeros from MSB, we bit-reverse the input')
        self.comment('For WIDTH=48, clz output is $clog2(48)+1 = 7 bits (0-48 range)')
        self.instruction('')
        self.comment('Bit-reverse function for 48-bit value')
        self.instruction('wire [47:0] w_sum_abs_reversed;')
        self.instruction('genvar i;')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < 48; i = i + 1) begin : gen_bit_reverse')
        self.instruction('        assign w_sum_abs_reversed[i] = w_sum_abs[47 - i];')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')
        self.instruction('wire [6:0] w_lz_count_raw;')
        self.instruction('count_leading_zeros #(.WIDTH(48)) u_clz (')
        self.instruction('    .data(w_sum_abs_reversed),')
        self.instruction('    .clz(w_lz_count_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Clamp LZ count to 6 bits for shift (max useful shift is 47)')
        self.instruction("wire [5:0] w_lz_count = (w_lz_count_raw > 7'd47) ? 6'd47 : w_lz_count_raw[5:0];")
        self.instruction('')

        self.comment('Normalized mantissa (shift left by LZ count)')
        self.instruction('wire [47:0] w_mant_normalized = w_sum_abs << w_lz_count;')
        self.instruction('')

        self.comment('Adjusted exponent')
        self.comment('exp_result_pre - lz_count + add_overflow (subtract leading zeros, add 1 for carry overflow)')
        self.instruction("wire signed [10:0] w_exp_adjusted = $signed({1'b0, w_exp_result_pre}) - $signed({4'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP32 packing."""
        self.comment('Round-to-Nearest-Even and FP32 packing')
        self.instruction('')

        self.comment('Extract 23-bit mantissa with guard, round, sticky')
        self.comment('Bit 47 is the implied 1 (not stored), bits [46:24] are the 23-bit mantissa')
        self.instruction('wire [22:0] w_mant_23 = w_mant_normalized[46:24];')
        self.instruction('wire w_guard  = w_mant_normalized[23];')
        self.instruction('wire w_round  = w_mant_normalized[22];')
        self.instruction('wire w_sticky = |w_mant_normalized[21:0];')
        self.instruction('')

        self.comment('RNE rounding decision')
        self.instruction('wire w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0]);')
        self.instruction('')

        self.comment('Apply rounding')
        self.instruction("wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[23];')
        self.instruction('')

        self.comment('Final mantissa (23 bits)')
        self.instruction('wire [22:0] w_mant_final = w_round_overflow ? w_mant_rounded[23:1] : w_mant_rounded[22:0];')
        self.instruction('')

        self.comment('Final exponent with rounding adjustment')
        self.instruction("wire signed [10:0] w_exp_final = w_exp_adjusted + {10'b0, w_round_overflow};")
        self.instruction('')

    def generate_special_case_handling(self):
        """Generate special case result selection."""
        self.comment('Special case handling')
        self.instruction('')

        self.comment('Any NaN input')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;')
        self.instruction('')

        self.comment('Invalid: 0 * inf or inf - inf')
        self.instruction('wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;')
        self.instruction('wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);')
        self.instruction('wire w_invalid = w_invalid_mul | w_invalid_add;')
        self.instruction('')

        self.comment('Overflow and underflow detection')
        self.comment('Use signed comparison - negative exponent is underflow, not overflow')
        self.instruction("wire w_overflow_cond = ~w_exp_final[10] & (w_exp_final > 11'sd254);")
        self.instruction("wire w_underflow_cond = w_exp_final[10] | (w_exp_final < 11'sd1);")
        self.instruction('')

    def generate_result_assembly(self):
        """Generate final result assembly."""
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    // Default: normal result')
        self.instruction('    ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    // Special cases')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN")
        self.instruction('        ow_invalid = w_invalid;')
        self.instruction('    end else if (w_prod_is_inf & ~w_c_is_inf) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity")
        self.instruction('    end else if (w_c_is_inf) begin')
        self.instruction("        ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity")
        self.instruction('    end else if (w_overflow_cond) begin')
        self.instruction("        ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_underflow_cond | (w_sum_abs == 48\'h0)) begin')
        self.instruction("        ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero")
        self.instruction("        ow_underflow = w_underflow_cond & (w_sum_abs != 48'h0);")
        self.instruction('    end else if (w_prod_is_zero & w_c_eff_zero) begin')
        self.instruction("        ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};  // Zero")
        self.instruction('    end else if (w_prod_is_zero) begin')
        self.instruction('        ow_result = i_c;  // 0 + c = c')
        self.instruction('    end else if (w_c_eff_zero) begin')
        self.instruction('        // Product only, extend to FP32')
        self.instruction("        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]};")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete BF16 FMA."""
        self.generate_bf16_field_extraction()
        self.generate_fp32_field_extraction()
        self.generate_special_case_detection()
        self.generate_product_computation()
        self.generate_addend_alignment()
        self.generate_addition()
        self.generate_normalization()
        self.generate_rounding_and_packing()
        self.generate_special_case_handling()
        self.generate_result_assembly()

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='BF16 Fused Multiply-Add with FP32 accumulator for AI training',
            generator_script='bf16_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_bf16_fma(output_path):
    """
    Generate BF16 FMA with FP32 accumulator.

    Args:
        output_path: Directory to write the generated file
    """
    fma = BF16FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_bf16_fma(output_path)
    print(f'Generated: {module_name}.sv')
