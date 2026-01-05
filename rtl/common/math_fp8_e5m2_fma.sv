// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_fma
// Purpose: FP8 E5M2 Fused Multiply-Add with 12-bit internal precision
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e5m2_fma.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e5m2_fma(
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    input  logic [7:0] i_c,
    output logic [7:0] ow_result,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_invalid
);

// FP8 E5M2 field extraction
// Format: [7]=sign, [6:2]=exp, [1:0]=mant

// Operand A
wire       w_sign_a = i_a[7];
wire [4:0] w_exp_a  = i_a[6:2];
wire [1:0] w_mant_a = i_a[1:0];

// Operand B
wire       w_sign_b = i_b[7];
wire [4:0] w_exp_b  = i_b[6:2];
wire [1:0] w_mant_b = i_b[1:0];

// Operand C (addend)
wire       w_sign_c = i_c[7];
wire [4:0] w_exp_c  = i_c[6:2];
wire [1:0] w_mant_c = i_c[1:0];

// Special case detection

// Zero detection
wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 2'h0);
wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 2'h0);
wire w_c_is_zero = (w_exp_c == 5'h00) & (w_mant_c == 2'h0);

// Subnormal detection (FTZ mode)
wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 2'h0);
wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 2'h0);
wire w_c_is_subnormal = (w_exp_c == 5'h00) & (w_mant_c != 2'h0);

// Infinity detection (E5M2: exp=31, mant=0)
wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 2'h0);
wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 2'h0);
wire w_c_is_inf = (w_exp_c == 5'h1F) & (w_mant_c == 2'h0);

// NaN detection (E5M2: exp=31, mant!=0)
wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);
wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);
wire w_c_is_nan = (w_exp_c == 5'h1F) & (w_mant_c != 2'h0);

// Effective zero (includes subnormals)
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;

// Normal number check
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;
wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;

// Mantissa multiplication (a * b)

// Extended mantissas with implied 1 (3-bit)
wire [2:0] w_mant_a_ext = w_a_is_normal ? {1'b1, w_mant_a} : 3'h0;
wire [2:0] w_mant_b_ext = w_b_is_normal ? {1'b1, w_mant_b} : 3'h0;

// 3x3 multiplication -> 6-bit product
wire [5:0] w_prod_mant = w_mant_a_ext * w_mant_b_ext;

// Product sign
wire w_prod_sign = w_sign_a ^ w_sign_b;

// Product exponent (before normalization)
// exp_prod = exp_a + exp_b - bias(15)
wire [6:0] w_prod_exp_sum = {2'b0, w_exp_a} + {2'b0, w_exp_b};
wire signed [7:0] w_prod_exp_raw = $signed({1'b0, w_prod_exp_sum}) - 8'sd15;

// Normalize product (check if bit 5 is set)
wire w_prod_needs_norm = w_prod_mant[5];
wire [5:0] w_prod_mant_norm = w_prod_needs_norm ? w_prod_mant : {w_prod_mant[4:0], 1'b0};
wire signed [7:0] w_prod_exp = w_prod_exp_raw + {7'b0, w_prod_needs_norm};

// Addend alignment

// Extended addend mantissa with implied 1 (3-bit)
wire [2:0] w_mant_c_ext = w_c_is_normal ? {1'b1, w_mant_c} : 3'h0;

// Exponent difference for alignment
wire [6:0] w_exp_c_ext = {2'b0, w_exp_c};
wire signed [7:0] w_exp_diff = w_prod_exp - $signed({1'b0, w_exp_c_ext});

// Determine which operand has larger exponent
wire w_prod_exp_larger = w_exp_diff >= 0;
wire [5:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff[5:0] : (~w_exp_diff[5:0] + 6'd1);

// Clamp shift amount (12-bit max)
wire [3:0] w_shift_clamped = (w_shift_amt > 6'd11) ? 4'd11 : w_shift_amt[3:0];

// Extended mantissas for addition (12 bits)
wire [11:0] w_prod_mant_12 = {w_prod_mant_norm, 6'b0};
wire [11:0] w_c_mant_12    = {w_mant_c_ext, 9'b0};

// Aligned mantissas
wire [11:0] w_mant_larger, w_mant_smaller_shifted;
wire        w_sign_larger, w_sign_smaller;
wire [5:0]  w_exp_result_pre;

assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_12 : w_c_mant_12;
assign w_mant_smaller_shifted = w_prod_exp_larger ?
    (w_c_mant_12 >> w_shift_clamped) : (w_prod_mant_12 >> w_shift_clamped);
assign w_sign_larger = w_prod_exp_larger ? w_prod_sign : w_sign_c;
assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;
assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp[5:0] : w_exp_c_ext[5:0];

// Mantissa addition/subtraction (12-bit)

wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

wire [12:0] w_sum_raw = w_effective_sub ?
    {1'b0, w_mant_larger} - {1'b0, w_mant_smaller_shifted} :
    {1'b0, w_mant_larger} + {1'b0, w_mant_smaller_shifted};

// Handle negative result from subtraction
wire w_sum_negative = w_effective_sub & w_sum_raw[12];
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;
wire [12:0] w_sum_abs = w_sum_negative ? (~w_sum_raw + 13'd1) : w_sum_raw;

// Check for addition overflow
wire w_add_overflow = ~w_effective_sub & w_sum_abs[12];

// Adjust for overflow
wire [11:0] w_sum_12 = w_add_overflow ? w_sum_abs[12:1] : w_sum_abs[11:0];

// Normalization

// Find leading one using priority encoder
wire [3:0] w_lz_count;
assign w_lz_count = w_sum_12[11] ? 4'd0 :
                    w_sum_12[10] ? 4'd1 :
                    w_sum_12[9]  ? 4'd2 :
                    w_sum_12[8]  ? 4'd3 :
                    w_sum_12[7]  ? 4'd4 :
                    w_sum_12[6]  ? 4'd5 :
                    w_sum_12[5]  ? 4'd6 :
                    w_sum_12[4]  ? 4'd7 :
                    w_sum_12[3]  ? 4'd8 :
                    w_sum_12[2]  ? 4'd9 :
                    w_sum_12[1]  ? 4'd10 : 4'd11;

// Normalized mantissa
wire [11:0] w_mant_normalized = w_sum_12 << w_lz_count;

// Adjusted exponent
wire signed [7:0] w_exp_adjusted = $signed({2'b0, w_exp_result_pre}) -
    $signed({4'b0, w_lz_count}) + {7'b0, w_add_overflow};

// Round-to-Nearest-Even and FP8 packing

// Extract mantissa bits [11:10], guard [9], round [8], sticky [7:0]
wire [1:0] w_mant_pre = w_mant_normalized[10:9];
wire w_guard = w_mant_normalized[8];
wire w_round = w_mant_normalized[7];
wire w_sticky = |w_mant_normalized[6:0];

// RNE rounding
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_pre[0]);

// Apply rounding
wire [2:0] w_mant_rounded = {1'b0, w_mant_pre} + {2'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[2];

// Final mantissa and exponent
wire [1:0] w_mant_final = w_round_overflow ? 2'h0 : w_mant_rounded[1:0];
wire signed [7:0] w_exp_final = w_exp_adjusted + {7'b0, w_round_overflow};

// Special case handling

wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;
wire w_prod_zero = w_a_eff_zero | w_b_eff_zero;
wire w_prod_inf = (w_a_is_inf | w_b_is_inf) & ~w_prod_zero;

// Invalid: 0 * inf or inf - inf
wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
wire w_invalid_add = w_prod_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
wire w_invalid = w_invalid_mul | w_invalid_add;

// Overflow: exp > 30
wire w_overflow = ~w_exp_final[7] & (w_exp_final > 8'sd30);

// Underflow: exp < 1
wire w_underflow = w_exp_final[7] | (w_exp_final < 8'sd1);

// Sum is zero
wire w_sum_is_zero = (w_sum_12 == 12'h0);

// Infinity sign selection
wire w_inf_sign = w_prod_inf ? w_prod_sign : w_c_is_inf ? w_sign_c : w_result_sign;

// Final result assembly

always_comb begin
    ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    if (w_any_nan | w_invalid) begin
        ow_result = {1'b0, 5'h1F, 2'h1};  // Canonical qNaN
        ow_invalid = w_invalid;
    end else if (w_prod_inf | w_c_is_inf | w_overflow) begin
        ow_result = {w_inf_sign, 5'h1F, 2'h0};  // Infinity
        ow_overflow = w_overflow & ~w_prod_inf & ~w_c_is_inf;
    end else if (w_underflow | w_sum_is_zero) begin
        ow_result = {w_result_sign, 5'h00, 2'h0};
        ow_underflow = w_underflow & ~w_sum_is_zero;
    end else if (w_prod_zero) begin
        ow_result = i_c;  // 0 * b + c = c
    end else if (w_c_eff_zero) begin
        // a * b + 0 = a * b
        ow_result = {w_prod_sign, w_prod_exp[4:0], w_prod_mant_norm[4:3]};
    end
end

endmodule
