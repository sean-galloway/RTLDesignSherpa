# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32FMA
# Purpose: IEEE 754-2008 FP32 Fused Multiply-Add Generator
#
# Implements FMA: result = (a * b) + c
# Where a, b, c, and result are all FP32.
#
# Key characteristics:
#   - Single rounding at the end (fused operation)
#   - 24x24 mantissa multiplication (48-bit product)
#   - 72-bit wide accumulator for full precision
#   - FTZ (Flush-To-Zero) mode for subnormals
#   - RNE (Round-to-Nearest-Even) rounding
#
# FP32 format: [31]=sign, [30:23]=exp (bias=127), [22:0]=mantissa
#
# Architecture:
#   Stage 1: Field extraction from a, b, c
#   Stage 2: 24x24 Dadda multiply -> 48-bit product
#   Stage 3: Alignment (72-bit operands, barrel shifter)
#   Stage 4: 72-bit Han-Carlson addition
#   Stage 5: Normalization (72-bit CLZ + shift)
#   Stage 6: RNE rounding to FP32
#   Stage 7: Special case handling
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP32FMA(Module):
    """
    Generates IEEE 754-2008 FP32 Fused Multiply-Add.

    Architecture:
    1. FP32 multiplication (24x24 mantissa using Dadda tree)
    2. Align addend with product using exponent difference
    3. 72-bit addition using Han-Carlson structural adder
    4. Normalize result (CLZ + left shift)
    5. Round to FP32 precision (RNE)
    6. Handle special cases (NaN, Inf, Zero, overflow, underflow)

    The 72-bit accumulator provides full precision:
    - 48-bit product mantissa
    - Plus guard bits for alignment
    - Single rounding at end (true fused operation)
    """

    module_str = 'math_ieee754_2008_fp32_fma'
    port_str = '''
    input  logic [31:0] i_a,           // FP32 operand A
    input  logic [31:0] i_b,           // FP32 operand B
    input  logic [31:0] i_c,           // FP32 addend
    output logic [31:0] ow_result,     // FP32 result = (a * b) + c
    output logic        ow_overflow,   // Overflow
    output logic        ow_underflow,  // Underflow
    output logic        ow_invalid     // Invalid operation (NaN)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_field_extraction(self):
        """Extract fields from all FP32 operands."""
        self.comment('FP32 field extraction')
        self.comment('FP32: [31]=sign, [30:23]=exp, [22:0]=mant')
        self.instruction('')

        # Operand A
        self.instruction('wire        w_sign_a = i_a[31];')
        self.instruction('wire [7:0]  w_exp_a  = i_a[30:23];')
        self.instruction('wire [22:0] w_mant_a = i_a[22:0];')
        self.instruction('')

        # Operand B
        self.instruction('wire        w_sign_b = i_b[31];')
        self.instruction('wire [7:0]  w_exp_b  = i_b[30:23];')
        self.instruction('wire [22:0] w_mant_b = i_b[22:0];')
        self.instruction('')

        # Operand C (addend)
        self.instruction('wire        w_sign_c = i_c[31];')
        self.instruction('wire [7:0]  w_exp_c  = i_c[30:23];')
        self.instruction('wire [22:0] w_mant_c = i_c[22:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special cases for all operands."""
        self.comment('Special case detection')
        self.instruction('')

        # Operand A
        self.comment('Operand A special cases')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h0);")
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h0);")
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h0);")
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h0);")
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('')

        # Operand B
        self.comment('Operand B special cases')
        self.instruction("wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h0);")
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        # Operand C
        self.comment('Operand C (addend) special cases')
        self.instruction("wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);")
        self.instruction('wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;')
        self.instruction('wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;')
        self.instruction('')

    def generate_product_computation(self):
        """Generate FP32 product computation (24x24 mantissa multiply)."""
        self.comment('FP32 multiplication: a * b')
        self.instruction('')

        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Extended mantissas with implied 1 (24-bit)')
        self.instruction("wire [23:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 24'h0;")
        self.instruction("wire [23:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 24'h0;")
        self.instruction('')

        self.comment('24x24 mantissa multiplication using Dadda tree (48-bit product)')
        self.instruction('wire [47:0] w_prod_mant_raw;')
        self.instruction('math_multiplier_dadda_4to2_024 u_mant_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(w_prod_mant_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Product exponent: exp_a + exp_b - bias (127)')
        self.comment('Use signed arithmetic to correctly handle underflow')
        self.instruction("wire signed [9:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 10'sd127;")
        self.instruction('')

        self.comment('Normalization detection (product >= 2.0)')
        self.comment('With 24x24 multiply: 1.xxx * 1.yyy = 01.xxx or 1x.xxx')
        self.comment('Check bit[47] for overflow (result >= 2.0)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant_raw[47];')
        self.instruction('')

        self.comment('Normalized product exponent (add 1 if needs normalization)')
        self.instruction("wire signed [9:0] w_prod_exp = w_prod_exp_raw + {9'b0, w_prod_needs_norm};")
        self.instruction('')

        self.comment('Normalized 48-bit product mantissa')
        self.comment('Shift right by 1 if overflow, keeping bit[47] as implied 1')
        self.instruction('wire [47:0] w_prod_mant_norm = w_prod_needs_norm ?')
        self.instruction('    w_prod_mant_raw : {w_prod_mant_raw[46:0], 1\'b0};')
        self.instruction('')

    def generate_addend_alignment(self):
        """Generate addend alignment logic for 72-bit accumulator."""
        self.comment('Addend (c) alignment')
        self.comment('Extend both product and addend to 72 bits for full precision')
        self.instruction('')

        self.comment('Extended addend mantissa with implied 1 (24-bit)')
        self.instruction("wire [23:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;")
        self.instruction('')

        self.comment('Exponent difference for alignment')
        self.comment('w_prod_exp is signed, w_exp_c is unsigned; sign-extend product exp for comparison')
        self.instruction("wire signed [10:0] w_prod_exp_ext = {{1{w_prod_exp[9]}}, w_prod_exp};  // Sign-extend")
        self.instruction("wire signed [10:0] w_exp_c_ext = {3'b0, w_exp_c};  // Zero-extend (always positive)")
        self.instruction('wire signed [10:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;')
        self.instruction('')

        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [10:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 11'd1);")
        self.instruction('')

        self.comment('Clamp shift amount to prevent over-shifting (72-bit max)')
        self.instruction("wire [6:0] w_shift_clamped = (w_shift_amt > 11'd72) ? 7'd72 : w_shift_amt[6:0];")
        self.instruction('')

        self.comment('Extended mantissas for addition (72 bits)')
        self.comment('Product: 48-bit mantissa extended to 72 bits')
        self.comment('Addend: 24-bit mantissa extended to 72 bits')
        self.instruction("wire [71:0] w_prod_mant_72 = {w_prod_mant_norm, 24'b0};")
        self.instruction("wire [71:0] w_c_mant_72    = {w_mant_c_ext, 48'b0};")
        self.instruction('')

        self.comment('Aligned mantissas')
        self.instruction('wire [71:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire signed [10:0] w_exp_result_pre;')
        self.instruction('')

        self.comment('Select aligned operands based on exponent comparison')
        self.comment('Smaller exponent operand gets right-shifted for alignment')
        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_72 : w_c_mant_72;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_72 >> w_shift_clamped) : (w_prod_mant_72 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction('assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;')
        self.instruction('')

    def generate_addition(self):
        """Generate the 72-bit addition using Han-Carlson structural adder."""
        self.comment('72-bit Addition using Han-Carlson structural adder')
        self.instruction('')

        self.comment('Effective operation: add or subtract based on signs')
        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')

        self.comment('For subtraction, invert smaller operand (two\'s complement: ~B + 1)')
        self.comment('The +1 is handled via carry-in to the adder')
        self.instruction('wire [71:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;')
        self.instruction('')

        self.comment('72-bit Han-Carlson structural adder')
        self.instruction('wire [71:0] w_adder_sum;')
        self.instruction('wire        w_adder_cout;')
        self.instruction('math_adder_han_carlson_072 u_wide_adder (')
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
        self.instruction('wire [71:0] w_negated_sum;')
        self.instruction('wire        w_neg_cout;')
        self.instruction('math_adder_han_carlson_072 u_negate_adder (')
        self.instruction('    .i_a(~w_adder_sum),')
        self.instruction("    .i_b(72'h0),")
        self.instruction("    .i_cin(1'b1),  // ~sum + 1 = -sum")
        self.instruction('    .ow_sum(w_negated_sum),')
        self.instruction('    .ow_cout(w_neg_cout)')
        self.instruction(');')
        self.instruction('')

        self.comment('Handle addition overflow (carry out for same-sign addition)')
        self.comment('When addition overflows, prepend carry bit and shift right')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_adder_cout;')
        self.instruction('wire [71:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[71:1]};  // Right shift, prepend carry')
        self.instruction('')

        self.comment('Select appropriate absolute value')
        self.instruction('wire [71:0] w_sum_abs = w_sum_negative ? w_negated_sum :')
        self.instruction('                        w_add_overflow ? w_sum_with_carry : w_adder_sum;')
        self.instruction('')

    def generate_normalization(self):
        """Generate normalization logic with 72-bit CLZ."""
        self.comment('Normalization')
        self.instruction('')

        self.comment('Count leading zeros for normalization')
        self.comment('NOTE: count_leading_zeros module counts from bit[0] (trailing zeros)')
        self.comment('To get actual leading zeros from MSB, we bit-reverse the input')
        self.comment('For WIDTH=72, clz output is $clog2(72)+1 = 8 bits (0-72 range)')
        self.instruction('')

        self.comment('Bit-reverse function for 72-bit value')
        self.instruction('wire [71:0] w_sum_abs_reversed;')
        self.instruction('genvar i;')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < 72; i = i + 1) begin : gen_bit_reverse')
        self.instruction('        assign w_sum_abs_reversed[i] = w_sum_abs[71 - i];')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')

        self.instruction('wire [7:0] w_lz_count_raw;')
        self.instruction('count_leading_zeros #(.WIDTH(72)) u_clz (')
        self.instruction('    .data(w_sum_abs_reversed),')
        self.instruction('    .clz(w_lz_count_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Clamp LZ count to 7 bits for shift (max useful shift is 71)')
        self.instruction("wire [6:0] w_lz_count = (w_lz_count_raw > 8'd71) ? 7'd71 : w_lz_count_raw[6:0];")
        self.instruction('')

        self.comment('Normalized mantissa (shift left by LZ count)')
        self.instruction('wire [71:0] w_mant_normalized = w_sum_abs << w_lz_count;')
        self.instruction('')

        self.comment('Adjusted exponent')
        self.comment('exp_result_pre is already signed 11-bit')
        self.instruction("wire signed [10:0] w_exp_adjusted = w_exp_result_pre - $signed({3'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP32 packing."""
        self.comment('Round-to-Nearest-Even and FP32 packing')
        self.instruction('')

        self.comment('Extract 23-bit mantissa with guard, round, sticky')
        self.comment('Bit 71 is the implied 1 (not stored), bits [70:48] are the 23-bit mantissa')
        self.instruction('wire [22:0] w_mant_23 = w_mant_normalized[70:48];')
        self.instruction('wire w_guard  = w_mant_normalized[47];')
        self.instruction('wire w_round  = w_mant_normalized[46];')
        self.instruction('wire w_sticky = |w_mant_normalized[45:0];')
        self.instruction('')

        self.comment('RNE rounding decision')
        self.instruction('wire w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0]);')
        self.instruction('')

        self.comment('Apply rounding')
        self.instruction("wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[23];')
        self.instruction('')

        self.comment('Final mantissa (23 bits)')
        self.comment('When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)')
        self.instruction("wire [22:0] w_mant_final = w_round_overflow ? 23'h000000 : w_mant_rounded[22:0];")
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

        self.comment('Invalid operations: 0 * inf or inf - inf')
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
        self.comment('Product-only overflow/underflow (for c=0 shortcut path)')
        self.comment('w_prod_exp is now signed; use signed comparison')
        self.instruction("wire w_prod_overflow = (w_prod_exp > 10'sd254);")
        self.instruction("wire w_prod_underflow = (w_prod_exp < 10'sd1);")
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
        self.instruction('    // Special case priority (highest to lowest)')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN")
        self.instruction('        ow_invalid = w_invalid;')
        self.instruction('    end else if (w_prod_is_inf & ~w_c_is_inf) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity")
        self.instruction('    end else if (w_c_is_inf) begin')
        self.instruction("        ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity")
        self.instruction('    end else if (w_prod_is_zero & w_c_eff_zero) begin')
        self.instruction("        ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};  // 0*b+0 = 0")
        self.instruction('    end else if (w_prod_is_zero) begin')
        self.instruction('        ow_result = i_c;  // 0 * b + c = c')
        self.instruction('    end else if (w_c_eff_zero & w_prod_overflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_c_eff_zero & w_prod_underflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'h00, 23'h0};  // Product underflow to zero")
        self.instruction("        ow_underflow = 1'b1;")
        self.instruction('    end else if (w_c_eff_zero) begin')
        self.instruction('        // Product only: a * b + 0 (normal case)')
        self.instruction('        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_norm[46:24]};')
        self.instruction('    end else if (w_overflow_cond) begin')
        self.instruction("        ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_underflow_cond | (w_sum_abs == 72\'h0)) begin')
        self.instruction("        ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero")
        self.instruction("        ow_underflow = w_underflow_cond & (w_sum_abs != 72'h0);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 FMA."""
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

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 Fused Multiply-Add with full precision accumulation',
            generator_script='fp32_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_fma(output_path):
    """
    Generate IEEE 754-2008 FP32 FMA.

    Args:
        output_path: Directory to write the generated file

    Returns:
        Module name string
    """
    fma = FP32FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_fma(output_path)
    print(f'Generated: {module_name}.sv')
