// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp16_fma
// Purpose: IEEE 754-2008 FP16 Fused Multiply-Add with full precision accumulation
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp16_fma.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp16_fma(
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    input  logic [15:0] i_c,
    output logic [15:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);

// FP16 field extraction
// FP16: [15]=sign, [14:10]=exp, [9:0]=mant

wire       w_sign_a = i_a[15];
wire [4:0] w_exp_a  = i_a[14:10];
wire [9:0] w_mant_a = i_a[9:0];

wire       w_sign_b = i_b[15];
wire [4:0] w_exp_b  = i_b[14:10];
wire [9:0] w_mant_b = i_b[9:0];

wire       w_sign_c = i_c[15];
wire [4:0] w_exp_c  = i_c[14:10];
wire [9:0] w_mant_c = i_c[9:0];

// Special case detection

// Operand A
wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 10'h0);
wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 10'h0);
wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 10'h0);
wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 10'h0);
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;

// Operand B
wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 10'h0);
wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 10'h0);
wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 10'h0);
wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 10'h0);
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Operand C (addend)
wire w_c_is_zero = (w_exp_c == 5'h00) & (w_mant_c == 10'h0);
wire w_c_is_subnormal = (w_exp_c == 5'h00) & (w_mant_c != 10'h0);
wire w_c_is_inf = (w_exp_c == 5'h1F) & (w_mant_c == 10'h0);
wire w_c_is_nan = (w_exp_c == 5'h1F) & (w_mant_c != 10'h0);
wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;
wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;

// FP16 multiplication: a * b

// Product sign
wire w_prod_sign = w_sign_a ^ w_sign_b;

// Extended mantissas with implied 1 (11-bit)
wire [10:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 11'h0;
wire [10:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 11'h0;

// 11x11 mantissa multiplication using Dadda tree (22-bit product)
wire [21:0] w_prod_mant_raw;
math_multiplier_dadda_4to2_011 u_mant_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(w_prod_mant_raw)
);

// Product exponent: exp_a + exp_b - bias (15)
// Use signed arithmetic to correctly handle underflow
wire signed [6:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 7'sd15;

// Normalization detection (product >= 2.0)
wire w_prod_needs_norm = w_prod_mant_raw[21];

// Normalized product exponent
wire signed [6:0] w_prod_exp = w_prod_exp_raw + {6'b0, w_prod_needs_norm};

// Normalized 22-bit product mantissa
wire [21:0] w_prod_mant_norm = w_prod_needs_norm ?
    w_prod_mant_raw : {w_prod_mant_raw[20:0], 1'b0};

// Addend (c) alignment
// Extend both product and addend to 44 bits for full precision

// Extended addend mantissa with implied 1 (11-bit)
wire [10:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 11'h0;

// Exponent difference for alignment
// w_prod_exp is signed, w_exp_c is unsigned; sign-extend product exp for comparison
wire signed [7:0] w_prod_exp_ext = {{1{w_prod_exp[6]}}, w_prod_exp};  // Sign-extend
wire signed [7:0] w_exp_c_ext = {3'b0, w_exp_c};  // Zero-extend (always positive)
wire signed [7:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;

// Determine which operand has larger exponent
wire w_prod_exp_larger = w_exp_diff >= 0;
wire [7:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 8'd1);

// Clamp shift amount (44-bit max)
wire [5:0] w_shift_clamped = (w_shift_amt > 8'd44) ? 6'd44 : w_shift_amt[5:0];

// Extended mantissas for addition (44 bits)
wire [43:0] w_prod_mant_44 = {w_prod_mant_norm, 22'b0};
wire [43:0] w_c_mant_44    = {w_mant_c_ext, 33'b0};

// Aligned mantissas
wire [43:0] w_mant_larger, w_mant_smaller_shifted;
wire        w_sign_larger, w_sign_smaller;
wire signed [7:0] w_exp_result_pre;

assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_44 : w_c_mant_44;
assign w_mant_smaller_shifted = w_prod_exp_larger ?
    (w_c_mant_44 >> w_shift_clamped) : (w_prod_mant_44 >> w_shift_clamped);
assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;
assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;
assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;

// 44-bit Addition

wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// For subtraction, compute two's complement
wire [44:0] w_mant_larger_45 = {1'b0, w_mant_larger};
wire [44:0] w_mant_smaller_45 = {1'b0, w_mant_smaller_shifted};

wire [44:0] w_adder_sum = w_effective_sub ?
    (w_mant_larger_45 - w_mant_smaller_45) :
    (w_mant_larger_45 + w_mant_smaller_45);

// Result sign determination
wire w_sum_negative = w_effective_sub & w_adder_sum[44];
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;

// Absolute value of result
wire [44:0] w_sum_abs = w_sum_negative ? (~w_adder_sum + 45'd1) : w_adder_sum;

// Handle addition overflow
wire w_add_overflow = ~w_effective_sub & w_sum_abs[44];
wire [44:0] w_sum_adjusted = w_add_overflow ? {1'b0, w_sum_abs[44:1]} : w_sum_abs;

// Normalization

// Count leading zeros (bit-reverse for CLZ module)
wire [43:0] w_sum_44 = w_sum_adjusted[43:0];
wire [43:0] w_sum_reversed;
genvar i;
generate
    for (i = 0; i < 44; i = i + 1) begin : gen_bit_reverse
        assign w_sum_reversed[i] = w_sum_44[43 - i];
    end
endgenerate

wire [6:0] w_lz_count_raw;
count_leading_zeros #(.WIDTH(44)) u_clz (
    .data(w_sum_reversed),
    .clz(w_lz_count_raw)
);

// Clamp LZ count
wire [5:0] w_lz_count = (w_lz_count_raw > 7'd43) ? 6'd43 : w_lz_count_raw[5:0];

// Normalized mantissa
wire [43:0] w_mant_normalized = w_sum_44 << w_lz_count;

// Adjusted exponent
// exp_result_pre is already signed 8-bit
wire signed [7:0] w_exp_adjusted = w_exp_result_pre -
    $signed({1'b0, w_lz_count_raw}) + {7'b0, w_add_overflow};

// Round-to-Nearest-Even and FP16 packing

// Extract 10-bit mantissa with guard, round, sticky
// Bit 43 is implied 1, bits [42:33] are the 10-bit mantissa
wire [9:0] w_mant_10 = w_mant_normalized[42:33];
wire w_guard  = w_mant_normalized[32];
wire w_round  = w_mant_normalized[31];
wire w_sticky = |w_mant_normalized[30:0];

// RNE rounding decision
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_10[0]);

// Apply rounding
wire [10:0] w_mant_rounded = {1'b0, w_mant_10} + {10'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[10];

// Final mantissa
// When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)
wire [9:0] w_mant_final = w_round_overflow ? 10'h000 : w_mant_rounded[9:0];

// Final exponent
wire signed [7:0] w_exp_final = w_exp_adjusted + {7'b0, w_round_overflow};

// Special case handling

wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;
wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;
wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;
wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
wire w_invalid = w_invalid_mul | w_invalid_add;

wire w_overflow_cond = ~w_exp_final[7] & (w_exp_final > 8'sd30);
wire w_underflow_cond = w_exp_final[7] | (w_exp_final < 8'sd1);

// Product-only overflow/underflow (for c=0 shortcut path)
// w_prod_exp is now signed; use signed comparison
wire w_prod_overflow = (w_prod_exp > 7'sd30);
wire w_prod_underflow = (w_prod_exp < 7'sd1);

// Final result assembly

always_comb begin
    ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    if (w_any_nan | w_invalid) begin
        ow_result = {1'b0, 5'h1F, 10'h200};  // qNaN
        ow_invalid = w_invalid;
    end else if (w_prod_is_inf & ~w_c_is_inf) begin
        ow_result = {w_prod_sign, 5'h1F, 10'h0};
    end else if (w_c_is_inf) begin
        ow_result = {w_sign_c, 5'h1F, 10'h0};
    end else if (w_prod_is_zero & w_c_eff_zero) begin
        ow_result = {w_prod_sign & w_sign_c, 5'h00, 10'h0};  // 0*b+0 = 0
    end else if (w_prod_is_zero) begin
        ow_result = i_c;  // 0*b+c = c
    end else if (w_c_eff_zero & w_prod_overflow) begin
        ow_result = {w_prod_sign, 5'h1F, 10'h0};  // Product overflow to inf
        ow_overflow = 1'b1;
    end else if (w_c_eff_zero & w_prod_underflow) begin
        ow_result = {w_prod_sign, 5'h00, 10'h0};  // Product underflow to zero
        ow_underflow = 1'b1;
    end else if (w_c_eff_zero) begin
        ow_result = {w_prod_sign, w_prod_exp[4:0], w_prod_mant_norm[20:11]};  // a*b+0 (normal)
    end else if (w_overflow_cond) begin
        ow_result = {w_result_sign, 5'h1F, 10'h0};
        ow_overflow = 1'b1;
    end else if (w_underflow_cond | (w_sum_44 == 44'h0)) begin
        ow_result = {w_result_sign, 5'h00, 10'h0};
        ow_underflow = w_underflow_cond & (w_sum_44 != 44'h0);
    end
end

endmodule
