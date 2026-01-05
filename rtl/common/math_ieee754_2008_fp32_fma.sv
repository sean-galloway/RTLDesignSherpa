// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_fma
// Purpose: IEEE 754-2008 FP32 Fused Multiply-Add with full precision accumulation
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_fma.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp32_fma(
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    input  logic [31:0] i_c,
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);

// FP32 field extraction
// FP32: [31]=sign, [30:23]=exp, [22:0]=mant

wire        w_sign_a = i_a[31];
wire [7:0]  w_exp_a  = i_a[30:23];
wire [22:0] w_mant_a = i_a[22:0];

wire        w_sign_b = i_b[31];
wire [7:0]  w_exp_b  = i_b[30:23];
wire [22:0] w_mant_b = i_b[22:0];

wire        w_sign_c = i_c[31];
wire [7:0]  w_exp_c  = i_c[30:23];
wire [22:0] w_mant_c = i_c[22:0];

// Special case detection

// Operand A special cases
wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h0);
wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h0);
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h0);
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h0);
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;

// Operand B special cases
wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h0);
wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h0);
wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h0);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h0);
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Operand C (addend) special cases
wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);
wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);
wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);
wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);
wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;
wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;

// FP32 multiplication: a * b

// Product sign
wire w_prod_sign = w_sign_a ^ w_sign_b;

// Extended mantissas with implied 1 (24-bit)
wire [23:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 24'h0;
wire [23:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 24'h0;

// 24x24 mantissa multiplication using Dadda tree (48-bit product)
wire [47:0] w_prod_mant_raw;
math_multiplier_dadda_4to2_024 u_mant_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(w_prod_mant_raw)
);

// Product exponent: exp_a + exp_b - bias (127)
// Use signed arithmetic to correctly handle underflow
wire signed [9:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 10'sd127;

// Normalization detection (product >= 2.0)
// With 24x24 multiply: 1.xxx * 1.yyy = 01.xxx or 1x.xxx
// Check bit[47] for overflow (result >= 2.0)
wire w_prod_needs_norm = w_prod_mant_raw[47];

// Normalized product exponent (add 1 if needs normalization)
wire signed [9:0] w_prod_exp = w_prod_exp_raw + {9'b0, w_prod_needs_norm};

// Normalized 48-bit product mantissa
// Shift right by 1 if overflow, keeping bit[47] as implied 1
wire [47:0] w_prod_mant_norm = w_prod_needs_norm ?
    w_prod_mant_raw : {w_prod_mant_raw[46:0], 1'b0};

// Addend (c) alignment
// Extend both product and addend to 72 bits for full precision

// Extended addend mantissa with implied 1 (24-bit)
wire [23:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;

// Exponent difference for alignment
// w_prod_exp is signed, w_exp_c is unsigned; sign-extend product exp for comparison
wire signed [10:0] w_prod_exp_ext = {{1{w_prod_exp[9]}}, w_prod_exp};  // Sign-extend
wire signed [10:0] w_exp_c_ext = {3'b0, w_exp_c};  // Zero-extend (always positive)
wire signed [10:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;

// Determine which operand has larger exponent
wire w_prod_exp_larger = w_exp_diff >= 0;
wire [10:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 11'd1);

// Clamp shift amount to prevent over-shifting (72-bit max)
wire [6:0] w_shift_clamped = (w_shift_amt > 11'd72) ? 7'd72 : w_shift_amt[6:0];

// Extended mantissas for addition (72 bits)
// Product: 48-bit mantissa extended to 72 bits
// Addend: 24-bit mantissa extended to 72 bits
wire [71:0] w_prod_mant_72 = {w_prod_mant_norm, 24'b0};
wire [71:0] w_c_mant_72    = {w_mant_c_ext, 48'b0};

// Aligned mantissas
wire [71:0] w_mant_larger, w_mant_smaller_shifted;
wire        w_sign_larger, w_sign_smaller;
wire signed [10:0] w_exp_result_pre;

// Select aligned operands based on exponent comparison
// Smaller exponent operand gets right-shifted for alignment
assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_72 : w_c_mant_72;
assign w_mant_smaller_shifted = w_prod_exp_larger ?
    (w_c_mant_72 >> w_shift_clamped) : (w_prod_mant_72 >> w_shift_clamped);
assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;
assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;
assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;

// 72-bit Addition using Han-Carlson structural adder

// Effective operation: add or subtract based on signs
wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// For subtraction, invert smaller operand (two's complement: ~B + 1)
// The +1 is handled via carry-in to the adder
wire [71:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;

// 72-bit Han-Carlson structural adder
wire [71:0] w_adder_sum;
wire        w_adder_cout;
math_adder_han_carlson_072 u_wide_adder (
    .i_a(w_mant_larger),
    .i_b(w_adder_b),
    .i_cin(w_effective_sub),  // +1 for two's complement subtraction
    .ow_sum(w_adder_sum),
    .ow_cout(w_adder_cout)
);

// Result sign determination
// For subtraction: if no carry out, result is negative (A < B)
// For addition: carry out means magnitude overflow (need right shift)
wire w_sum_negative = w_effective_sub & ~w_adder_cout;
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;

// Absolute value of result
// If negative (subtraction with A < B), need to negate the result
wire [71:0] w_negated_sum;
wire        w_neg_cout;
math_adder_han_carlson_072 u_negate_adder (
    .i_a(~w_adder_sum),
    .i_b(72'h0),
    .i_cin(1'b1),  // ~sum + 1 = -sum
    .ow_sum(w_negated_sum),
    .ow_cout(w_neg_cout)
);

// Handle addition overflow (carry out for same-sign addition)
// When addition overflows, prepend carry bit and shift right
wire w_add_overflow = ~w_effective_sub & w_adder_cout;
wire [71:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[71:1]};  // Right shift, prepend carry

// Select appropriate absolute value
wire [71:0] w_sum_abs = w_sum_negative ? w_negated_sum :
                        w_add_overflow ? w_sum_with_carry : w_adder_sum;

// Normalization

// Count leading zeros for normalization
// NOTE: count_leading_zeros module counts from bit[0] (trailing zeros)
// To get actual leading zeros from MSB, we bit-reverse the input
// For WIDTH=72, clz output is $clog2(72)+1 = 8 bits (0-72 range)

// Bit-reverse function for 72-bit value
wire [71:0] w_sum_abs_reversed;
genvar i;
generate
    for (i = 0; i < 72; i = i + 1) begin : gen_bit_reverse
        assign w_sum_abs_reversed[i] = w_sum_abs[71 - i];
    end
endgenerate

wire [7:0] w_lz_count_raw;
count_leading_zeros #(.WIDTH(72)) u_clz (
    .data(w_sum_abs_reversed),
    .clz(w_lz_count_raw)
);

// Clamp LZ count to 7 bits for shift (max useful shift is 71)
wire [6:0] w_lz_count = (w_lz_count_raw > 8'd71) ? 7'd71 : w_lz_count_raw[6:0];

// Normalized mantissa (shift left by LZ count)
wire [71:0] w_mant_normalized = w_sum_abs << w_lz_count;

// Adjusted exponent
// exp_result_pre is already signed 11-bit
wire signed [10:0] w_exp_adjusted = w_exp_result_pre - $signed({3'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};

// Round-to-Nearest-Even and FP32 packing

// Extract 23-bit mantissa with guard, round, sticky
// Bit 71 is the implied 1 (not stored), bits [70:48] are the 23-bit mantissa
wire [22:0] w_mant_23 = w_mant_normalized[70:48];
wire w_guard  = w_mant_normalized[47];
wire w_round  = w_mant_normalized[46];
wire w_sticky = |w_mant_normalized[45:0];

// RNE rounding decision
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0]);

// Apply rounding
wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[23];

// Final mantissa (23 bits)
// When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)
wire [22:0] w_mant_final = w_round_overflow ? 23'h000000 : w_mant_rounded[22:0];

// Final exponent with rounding adjustment
wire signed [10:0] w_exp_final = w_exp_adjusted + {10'b0, w_round_overflow};

// Special case handling

// Any NaN input
wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;

// Invalid operations: 0 * inf or inf - inf
wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;
wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;
wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
wire w_invalid = w_invalid_mul | w_invalid_add;

// Overflow and underflow detection
// Use signed comparison - negative exponent is underflow, not overflow
wire w_overflow_cond = ~w_exp_final[10] & (w_exp_final > 11'sd254);
wire w_underflow_cond = w_exp_final[10] | (w_exp_final < 11'sd1);

// Product-only overflow/underflow (for c=0 shortcut path)
// w_prod_exp is now signed; use signed comparison
wire w_prod_overflow = (w_prod_exp > 10'sd254);
wire w_prod_underflow = (w_prod_exp < 10'sd1);

// Final result assembly

always_comb begin
    // Default: normal result
    ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    // Special case priority (highest to lowest)
    if (w_any_nan | w_invalid) begin
        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN
        ow_invalid = w_invalid;
    end else if (w_prod_is_inf & ~w_c_is_inf) begin
        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity
    end else if (w_c_is_inf) begin
        ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity
    end else if (w_prod_is_zero & w_c_eff_zero) begin
        ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};  // 0*b+0 = 0
    end else if (w_prod_is_zero) begin
        ow_result = i_c;  // 0 * b + c = c
    end else if (w_c_eff_zero & w_prod_overflow) begin
        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product overflow to inf
        ow_overflow = 1'b1;
    end else if (w_c_eff_zero & w_prod_underflow) begin
        ow_result = {w_prod_sign, 8'h00, 23'h0};  // Product underflow to zero
        ow_underflow = 1'b1;
    end else if (w_c_eff_zero) begin
        // Product only: a * b + 0 (normal case)
        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_norm[46:24]};
    end else if (w_overflow_cond) begin
        ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf
        ow_overflow = 1'b1;
    end else if (w_underflow_cond | (w_sum_abs == 72'h0)) begin
        ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero
        ow_underflow = w_underflow_cond & (w_sum_abs != 72'h0);
    end
end

endmodule
