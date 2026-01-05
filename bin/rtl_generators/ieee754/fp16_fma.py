# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16FMA
# Purpose: IEEE 754-2008 FP16 Fused Multiply-Add Generator
#
# Implements FMA: result = (a * b) + c
# Where a, b, c, and result are all FP16.
#
# Key characteristics:
#   - Single rounding at the end (fused operation)
#   - 11x11 mantissa multiplication (22-bit product)
#   - 44-bit wide accumulator for full precision
#   - FTZ (Flush-To-Zero) mode for subnormals
#   - RNE (Round-to-Nearest-Even) rounding
#
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Architecture:
#   Stage 1: Field extraction from a, b, c
#   Stage 2: 11x11 Dadda multiply -> 22-bit product
#   Stage 3: Alignment (44-bit operands)
#   Stage 4: 44-bit addition
#   Stage 5: Normalization (44-bit CLZ + shift)
#   Stage 6: RNE rounding to FP16
#   Stage 7: Special case handling
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP16FMA(Module):
    """
    Generates IEEE 754-2008 FP16 Fused Multiply-Add.

    Uses 44-bit accumulator for full precision:
    - 22-bit product mantissa
    - Plus guard bits for alignment
    - Single rounding at end (true fused operation)
    """

    module_str = 'math_ieee754_2008_fp16_fma'
    port_str = '''
    input  logic [15:0] i_a,           // FP16 operand A
    input  logic [15:0] i_b,           // FP16 operand B
    input  logic [15:0] i_c,           // FP16 addend
    output logic [15:0] ow_result,     // FP16 result = (a * b) + c
    output logic        ow_overflow,   // Overflow
    output logic        ow_underflow,  // Underflow
    output logic        ow_invalid     // Invalid operation (NaN)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_field_extraction(self):
        """Extract fields from all FP16 operands."""
        self.comment('FP16 field extraction')
        self.comment('FP16: [15]=sign, [14:10]=exp, [9:0]=mant')
        self.instruction('')

        self.instruction('wire       w_sign_a = i_a[15];')
        self.instruction('wire [4:0] w_exp_a  = i_a[14:10];')
        self.instruction('wire [9:0] w_mant_a = i_a[9:0];')
        self.instruction('')

        self.instruction('wire       w_sign_b = i_b[15];')
        self.instruction('wire [4:0] w_exp_b  = i_b[14:10];')
        self.instruction('wire [9:0] w_mant_b = i_b[9:0];')
        self.instruction('')

        self.instruction('wire       w_sign_c = i_c[15];')
        self.instruction('wire [4:0] w_exp_c  = i_c[14:10];')
        self.instruction('wire [9:0] w_mant_c = i_c[9:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special cases for all operands."""
        self.comment('Special case detection')
        self.instruction('')

        self.comment('Operand A')
        self.instruction("wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 10'h0);")
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 10'h0);")
        self.instruction("wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 10'h0);")
        self.instruction("wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 10'h0);")
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('')

        self.comment('Operand B')
        self.instruction("wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 10'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 10'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 10'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 10'h0);")
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        self.comment('Operand C (addend)')
        self.instruction("wire w_c_is_zero = (w_exp_c == 5'h00) & (w_mant_c == 10'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 5'h00) & (w_mant_c != 10'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 5'h1F) & (w_mant_c == 10'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 5'h1F) & (w_mant_c != 10'h0);")
        self.instruction('wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;')
        self.instruction('wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;')
        self.instruction('')

    def generate_product_computation(self):
        """Generate FP16 product computation."""
        self.comment('FP16 multiplication: a * b')
        self.instruction('')

        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Extended mantissas with implied 1 (11-bit)')
        self.instruction("wire [10:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 11'h0;")
        self.instruction("wire [10:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 11'h0;")
        self.instruction('')

        self.comment('11x11 mantissa multiplication using Dadda tree (22-bit product)')
        self.instruction('wire [21:0] w_prod_mant_raw;')
        self.instruction('math_multiplier_dadda_4to2_011 u_mant_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(w_prod_mant_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Product exponent: exp_a + exp_b - bias (15)')
        self.comment('Use signed arithmetic to correctly handle underflow')
        self.instruction("wire signed [6:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 7'sd15;")
        self.instruction('')

        self.comment('Normalization detection (product >= 2.0)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant_raw[21];')
        self.instruction('')

        self.comment('Normalized product exponent')
        self.instruction("wire signed [6:0] w_prod_exp = w_prod_exp_raw + {6'b0, w_prod_needs_norm};")
        self.instruction('')

        self.comment('Normalized 22-bit product mantissa')
        self.instruction('wire [21:0] w_prod_mant_norm = w_prod_needs_norm ?')
        self.instruction('    w_prod_mant_raw : {w_prod_mant_raw[20:0], 1\'b0};')
        self.instruction('')

    def generate_addend_alignment(self):
        """Generate addend alignment logic for 44-bit accumulator."""
        self.comment('Addend (c) alignment')
        self.comment('Extend both product and addend to 44 bits for full precision')
        self.instruction('')

        self.comment('Extended addend mantissa with implied 1 (11-bit)')
        self.instruction("wire [10:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 11'h0;")
        self.instruction('')

        self.comment('Exponent difference for alignment')
        self.comment('w_prod_exp is signed, w_exp_c is unsigned; sign-extend product exp for comparison')
        self.instruction("wire signed [7:0] w_prod_exp_ext = {{1{w_prod_exp[6]}}, w_prod_exp};  // Sign-extend")
        self.instruction("wire signed [7:0] w_exp_c_ext = {3'b0, w_exp_c};  // Zero-extend (always positive)")
        self.instruction('wire signed [7:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;')
        self.instruction('')

        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [7:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 8'd1);")
        self.instruction('')

        self.comment('Clamp shift amount (44-bit max)')
        self.instruction("wire [5:0] w_shift_clamped = (w_shift_amt > 8'd44) ? 6'd44 : w_shift_amt[5:0];")
        self.instruction('')

        self.comment('Extended mantissas for addition (44 bits)')
        self.instruction("wire [43:0] w_prod_mant_44 = {w_prod_mant_norm, 22'b0};")
        self.instruction("wire [43:0] w_c_mant_44    = {w_mant_c_ext, 33'b0};")
        self.instruction('')

        self.comment('Aligned mantissas')
        self.instruction('wire [43:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire signed [7:0] w_exp_result_pre;')
        self.instruction('')

        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_44 : w_c_mant_44;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_44 >> w_shift_clamped) : (w_prod_mant_44 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction('assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;')
        self.instruction('')

    def generate_addition(self):
        """Generate the 44-bit addition."""
        self.comment('44-bit Addition')
        self.instruction('')

        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')

        self.comment('For subtraction, compute two\'s complement')
        self.instruction('wire [44:0] w_mant_larger_45 = {1\'b0, w_mant_larger};')
        self.instruction('wire [44:0] w_mant_smaller_45 = {1\'b0, w_mant_smaller_shifted};')
        self.instruction('')

        self.instruction('wire [44:0] w_adder_sum = w_effective_sub ?')
        self.instruction('    (w_mant_larger_45 - w_mant_smaller_45) :')
        self.instruction('    (w_mant_larger_45 + w_mant_smaller_45);')
        self.instruction('')

        self.comment('Result sign determination')
        self.instruction('wire w_sum_negative = w_effective_sub & w_adder_sum[44];')
        self.instruction('wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;')
        self.instruction('')

        self.comment('Absolute value of result')
        self.instruction("wire [44:0] w_sum_abs = w_sum_negative ? (~w_adder_sum + 45'd1) : w_adder_sum;")
        self.instruction('')

        self.comment('Handle addition overflow')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_sum_abs[44];')
        self.instruction('wire [44:0] w_sum_adjusted = w_add_overflow ? {1\'b0, w_sum_abs[44:1]} : w_sum_abs;')
        self.instruction('')

    def generate_normalization(self):
        """Generate normalization logic."""
        self.comment('Normalization')
        self.instruction('')

        self.comment('Count leading zeros (bit-reverse for CLZ module)')
        self.instruction('wire [43:0] w_sum_44 = w_sum_adjusted[43:0];')
        self.instruction('wire [43:0] w_sum_reversed;')
        self.instruction('genvar i;')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < 44; i = i + 1) begin : gen_bit_reverse')
        self.instruction('        assign w_sum_reversed[i] = w_sum_44[43 - i];')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

        self.instruction('wire [6:0] w_lz_count_raw;')
        self.instruction('count_leading_zeros #(.WIDTH(44)) u_clz (')
        self.instruction('    .data(w_sum_reversed),')
        self.instruction('    .clz(w_lz_count_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Clamp LZ count')
        self.instruction("wire [5:0] w_lz_count = (w_lz_count_raw > 7'd43) ? 6'd43 : w_lz_count_raw[5:0];")
        self.instruction('')

        self.comment('Normalized mantissa')
        self.instruction('wire [43:0] w_mant_normalized = w_sum_44 << w_lz_count;')
        self.instruction('')

        self.comment('Adjusted exponent')
        self.comment('exp_result_pre is already signed 8-bit')
        self.instruction("wire signed [7:0] w_exp_adjusted = w_exp_result_pre -")
        self.instruction("    $signed({1'b0, w_lz_count_raw}) + {7'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP16 packing."""
        self.comment('Round-to-Nearest-Even and FP16 packing')
        self.instruction('')

        self.comment('Extract 10-bit mantissa with guard, round, sticky')
        self.comment('Bit 43 is implied 1, bits [42:33] are the 10-bit mantissa')
        self.instruction('wire [9:0] w_mant_10 = w_mant_normalized[42:33];')
        self.instruction('wire w_guard  = w_mant_normalized[32];')
        self.instruction('wire w_round  = w_mant_normalized[31];')
        self.instruction('wire w_sticky = |w_mant_normalized[30:0];')
        self.instruction('')

        self.comment('RNE rounding decision')
        self.instruction('wire w_round_up = w_guard & (w_round | w_sticky | w_mant_10[0]);')
        self.instruction('')

        self.comment('Apply rounding')
        self.instruction("wire [10:0] w_mant_rounded = {1'b0, w_mant_10} + {10'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[10];')
        self.instruction('')

        self.comment('Final mantissa')
        self.comment('When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)')
        self.instruction("wire [9:0] w_mant_final = w_round_overflow ? 10'h000 : w_mant_rounded[9:0];")
        self.instruction('')

        self.comment('Final exponent')
        self.instruction("wire signed [7:0] w_exp_final = w_exp_adjusted + {7'b0, w_round_overflow};")
        self.instruction('')

    def generate_special_case_handling(self):
        """Generate special case result selection."""
        self.comment('Special case handling')
        self.instruction('')

        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;')
        self.instruction('wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;')
        self.instruction('wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);')
        self.instruction('wire w_invalid = w_invalid_mul | w_invalid_add;')
        self.instruction('')

        self.instruction("wire w_overflow_cond = ~w_exp_final[7] & (w_exp_final > 8'sd30);")
        self.instruction("wire w_underflow_cond = w_exp_final[7] | (w_exp_final < 8'sd1);")
        self.instruction('')
        self.comment('Product-only overflow/underflow (for c=0 shortcut path)')
        self.comment('w_prod_exp is now signed; use signed comparison')
        self.instruction("wire w_prod_overflow = (w_prod_exp > 7'sd30);")
        self.instruction("wire w_prod_underflow = (w_prod_exp < 7'sd1);")
        self.instruction('')

    def generate_result_assembly(self):
        """Generate final result assembly."""
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 5'h1F, 10'h200};  // qNaN")
        self.instruction('        ow_invalid = w_invalid;')
        self.instruction('    end else if (w_prod_is_inf & ~w_c_is_inf) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h1F, 10'h0};")
        self.instruction('    end else if (w_c_is_inf) begin')
        self.instruction("        ow_result = {w_sign_c, 5'h1F, 10'h0};")
        self.instruction('    end else if (w_prod_is_zero & w_c_eff_zero) begin')
        self.instruction("        ow_result = {w_prod_sign & w_sign_c, 5'h00, 10'h0};  // 0*b+0 = 0")
        self.instruction('    end else if (w_prod_is_zero) begin')
        self.instruction('        ow_result = i_c;  // 0*b+c = c')
        self.instruction('    end else if (w_c_eff_zero & w_prod_overflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h1F, 10'h0};  // Product overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_c_eff_zero & w_prod_underflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h00, 10'h0};  // Product underflow to zero")
        self.instruction("        ow_underflow = 1'b1;")
        self.instruction('    end else if (w_c_eff_zero) begin')
        self.instruction('        ow_result = {w_prod_sign, w_prod_exp[4:0], w_prod_mant_norm[20:11]};  // a*b+0 (normal)')
        self.instruction('    end else if (w_overflow_cond) begin')
        self.instruction("        ow_result = {w_result_sign, 5'h1F, 10'h0};")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction("    end else if (w_underflow_cond | (w_sum_44 == 44'h0)) begin")
        self.instruction("        ow_result = {w_result_sign, 5'h00, 10'h0};")
        self.instruction("        ow_underflow = w_underflow_cond & (w_sum_44 != 44'h0);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP16 FMA."""
        self.generate_field_extraction()
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

        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP16 Fused Multiply-Add with full precision accumulation',
            generator_script='fp16_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp16_fma(output_path):
    """Generate FP16 FMA."""
    fma = FP16FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_fma(output_path)
    print(f'Generated: {module_name}.sv')
