// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_fma
// Purpose: BF16 Fused Multiply-Add with FP32 accumulator for AI training
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-11-25
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/bf16/bf16_fma.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_bf16_fma(
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    input  logic [31:0] i_c,
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);

// BF16 field extraction
// BF16: [15]=sign, [14:7]=exp, [6:0]=mant

wire       w_sign_a = i_a[15];
wire [7:0] w_exp_a  = i_a[14:7];
wire [6:0] w_mant_a = i_a[6:0];

wire       w_sign_b = i_b[15];
wire [7:0] w_exp_b  = i_b[14:7];
wire [6:0] w_mant_b = i_b[6:0];

// FP32 field extraction
// FP32: [31]=sign, [30:23]=exp, [22:0]=mant

wire        w_sign_c  = i_c[31];
wire [7:0]  w_exp_c   = i_c[30:23];
wire [22:0] w_mant_c  = i_c[22:0];

// Special case detection - BF16 operands
wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);
wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);
wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);
wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);
wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);

// Effective zero (FTZ for subnormals)
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Special case detection - FP32 addend
wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);
wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);
wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);
wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);
wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;
wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;

// BF16 multiplication: a * b

// Product sign
wire w_prod_sign = w_sign_a ^ w_sign_b;

// Mantissa multiplication (8x8 with implied 1)
wire [7:0] w_mant_a_ext = {w_a_is_normal, w_mant_a};
wire [7:0] w_mant_b_ext = {w_b_is_normal, w_mant_b};

wire [15:0] w_prod_mant_raw;
math_multiplier_dadda_4to2_008 u_mant_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(w_prod_mant_raw)
);

// Product exponent: exp_a + exp_b - bias (SIGNED to detect underflow!)
wire signed [10:0] w_prod_exp_raw = $signed({3'b0, w_exp_a}) + $signed({3'b0, w_exp_b}) - 11'sd127;

// Normalization detection (product >= 2.0)
wire w_prod_needs_norm = w_prod_mant_raw[15];

// Normalized product exponent
wire signed [10:0] w_prod_exp_adj = w_prod_exp_raw + {10'b0, w_prod_needs_norm};

// Detect product underflow: when product exponent is too small to represent
// Product is effectively zero if exp < 1 (or exp goes negative)
wire w_prod_underflow = w_prod_exp_adj[10] | (w_prod_exp_adj < 11'sd1);

// Clamp product exponent for downstream use (will be overridden by special cases)
wire [9:0] w_prod_exp = w_prod_underflow ? 10'd0 : w_prod_exp_adj[9:0];

// Extended product mantissa to FP32 precision (23 bits)
// Product is either 1x.xxxxxxx_xxxxxxxx or 01.xxxxxx_xxxxxxxxx
wire [23:0] w_prod_mant_ext;  // With implied 1
assign w_prod_mant_ext = w_prod_needs_norm ?
    {1'b1, w_prod_mant_raw[14:0], 8'b0} :  // Shift right, add zeros
    {1'b1, w_prod_mant_raw[13:0], 9'b0};   // No shift

// Addend (c) alignment
// Need to align c with product based on exponent difference

// Extended addend mantissa with implied 1
wire [23:0] w_c_mant_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;

// Exponent difference for alignment
wire [9:0] w_exp_c_ext = {2'b0, w_exp_c};
wire signed [10:0] w_exp_diff = $signed({1'b0, w_prod_exp}) - $signed({1'b0, w_exp_c_ext});

// Determine which operand has larger exponent
wire w_prod_exp_larger = w_exp_diff >= 0;
wire [9:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff[9:0] : (~w_exp_diff[9:0] + 10'd1);

// Clamp shift amount to prevent over-shifting
wire [5:0] w_shift_clamped = (w_shift_amt > 10'd48) ? 6'd48 : w_shift_amt[5:0];

// Extended mantissas for addition (48 bits to capture all precision)
wire [47:0] w_prod_mant_48 = {w_prod_mant_ext, 24'b0};
wire [47:0] w_c_mant_48    = {w_c_mant_ext, 24'b0};

// Aligned mantissas
wire [47:0] w_mant_larger, w_mant_smaller_shifted;
wire        w_sign_larger, w_sign_smaller;
wire [9:0]  w_exp_result_pre;

assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_48 : w_c_mant_48;
assign w_mant_smaller_shifted = w_prod_exp_larger ?
    (w_c_mant_48 >> w_shift_clamped) : (w_prod_mant_48 >> w_shift_clamped);
assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;
assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;
assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp : w_exp_c_ext;

// Addition of aligned mantissas using Han-Carlson structural adder

// Effective operation: add or subtract based on signs
wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// For subtraction, invert smaller operand (two's complement: ~B + 1)
// The +1 is handled via carry-in to the adder
wire [47:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;

// 48-bit Han-Carlson structural adder
wire [47:0] w_adder_sum;
wire        w_adder_cout;
math_adder_han_carlson_048 u_wide_adder (
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
wire [47:0] w_negated_sum;
wire        w_neg_cout;
math_adder_han_carlson_048 u_negate_adder (
    .i_a(~w_adder_sum),
    .i_b(48'h0),
    .i_cin(1'b1),  // ~sum + 1 = -sum
    .ow_sum(w_negated_sum),
    .ow_cout(w_neg_cout)
);

// Handle addition overflow (carry out for same-sign addition)
// When addition overflows, prepend carry bit and shift right
wire w_add_overflow = ~w_effective_sub & w_adder_cout;
wire [47:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[47:1]};  // Right shift, prepend carry

// Select appropriate absolute value
wire [47:0] w_sum_abs = w_sum_negative ? w_negated_sum :
                        w_add_overflow ? w_sum_with_carry : w_adder_sum;

// Normalization

// Count leading zeros for normalization
// NOTE: count_leading_zeros module counts from bit[0] (trailing zeros)
// To get actual leading zeros from MSB, we bit-reverse the input
// For WIDTH=48, clz output is $clog2(48)+1 = 7 bits (0-48 range)

// Bit-reverse function for 48-bit value
wire [47:0] w_sum_abs_reversed;
genvar i;
generate
    for (i = 0; i < 48; i = i + 1) begin : gen_bit_reverse
        assign w_sum_abs_reversed[i] = w_sum_abs[47 - i];
    end
endgenerate

wire [6:0] w_lz_count_raw;
count_leading_zeros #(.WIDTH(48)) u_clz (
    .data(w_sum_abs_reversed),
    .clz(w_lz_count_raw)
);

// Clamp LZ count to 6 bits for shift (max useful shift is 47)
wire [5:0] w_lz_count = (w_lz_count_raw > 7'd47) ? 6'd47 : w_lz_count_raw[5:0];

// Normalized mantissa (shift left by LZ count)
wire [47:0] w_mant_normalized = w_sum_abs << w_lz_count;

// Adjusted exponent
// exp_result_pre - lz_count + add_overflow (subtract leading zeros, add 1 for carry overflow)
wire signed [10:0] w_exp_adjusted = $signed({1'b0, w_exp_result_pre}) - $signed({4'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};

// Round-to-Nearest-Even and FP32 packing

// Extract 23-bit mantissa with guard, round, sticky
// Bit 47 is the implied 1 (not stored), bits [46:24] are the 23-bit mantissa
wire [22:0] w_mant_23 = w_mant_normalized[46:24];
wire w_guard  = w_mant_normalized[23];
wire w_round  = w_mant_normalized[22];
wire w_sticky = |w_mant_normalized[21:0];

// RNE rounding decision
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0]);

// Apply rounding
wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[23];

// Final mantissa (23 bits)
// When rounding overflows (mantissa goes from 0x7FFFFF to 0x800000), the value
// becomes exactly 2.0, which normalizes to 1.0 * 2^1. The mantissa for 1.0 is 0.
wire [22:0] w_mant_final = w_round_overflow ? 23'h0 : w_mant_rounded[22:0];

// Final exponent with rounding adjustment
wire signed [10:0] w_exp_final = w_exp_adjusted + {10'b0, w_round_overflow};

// Special case handling

// Any NaN input
wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;

// Invalid: 0 * inf or inf - inf
wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;
// Product is zero if either operand is zero/subnormal, OR if the product underflows
wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero | w_prod_underflow;
wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
wire w_invalid = w_invalid_mul | w_invalid_add;

// Overflow and underflow detection
// Use signed comparison - negative exponent is underflow, not overflow
wire w_overflow_cond = ~w_exp_final[10] & (w_exp_final > 11'sd254);
wire w_underflow_cond = w_exp_final[10] | (w_exp_final < 11'sd1);

// Final result assembly

always_comb begin
    // Default: normal result
    ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    // Special cases - PRIORITY ORDER MATTERS!
    // 1. NaN/Invalid first (highest priority)
    // 2. Infinity cases
    // 3. Zero operand pass-through (BEFORE overflow/underflow check!)
    // 4. Overflow/underflow
    // 5. Normal result (default)

    if (w_any_nan | w_invalid) begin
        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN
        ow_invalid = w_invalid;
    end else if (w_prod_is_inf & ~w_c_is_inf) begin
        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity
    end else if (w_c_is_inf) begin
        ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity
    end else if (w_prod_is_zero & w_c_eff_zero) begin
        // 0 * 0 + 0 = 0 (sign from IEEE rules)
        ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};
    end else if (w_prod_is_zero) begin
        // 0 * X + C = C (pass-through addend when product is zero)
        ow_result = i_c;
    end else if (w_c_eff_zero) begin
        // A * B + 0 = A * B (product only, extend to FP32)
        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]};
    end else if (w_sum_abs == 48'h0) begin
        // Exact zero result: IEEE 754 round-to-nearest gives +0
        // (Exception: both operands negative gives -0, but that's handled by
        // the zero product cases above)
        ow_result = 32'h0;  // Positive zero
    end else if (w_overflow_cond) begin
        ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf
        ow_overflow = 1'b1;
    end else if (w_underflow_cond) begin
        ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero
        ow_underflow = 1'b1;
    end
end

endmodule
