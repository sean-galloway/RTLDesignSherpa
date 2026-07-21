// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_adder
// Purpose: FP8 E4M3 floating-point adder
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e4m3_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e4m3_adder (
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic [7:0] ow_result,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_invalid
);

// FP8 E4M3 field extraction
// Format: [7]=sign, [6:3]=exp, [2:0]=mant

wire       w_sign_a = i_a[7];
wire [3:0] w_exp_a  = i_a[6:3];
wire [2:0] w_mant_a = i_a[2:0];

wire       w_sign_b = i_b[7];
wire [3:0] w_exp_b  = i_b[6:3];
wire [2:0] w_mant_b = i_b[2:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 4'h0) & (w_mant_a == 3'h0);
wire w_b_is_zero = (w_exp_b == 4'h0) & (w_mant_b == 3'h0);
wire w_a_is_subnormal = (w_exp_a == 4'h0) & (w_mant_a != 3'h0);
wire w_b_is_subnormal = (w_exp_b == 4'h0) & (w_mant_b != 3'h0);
wire w_a_is_nan = (w_exp_a == 4'hF) & (w_mant_a == 3'h7);
wire w_b_is_nan = (w_exp_b == 4'hF) & (w_mant_b == 3'h7);

wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_nan;

// Exponent comparison and operand swap
// Always put larger exponent operand first

wire w_a_exp_larger = (w_exp_a >= w_exp_b);

// Swapped operands (larger exponent first)
wire       w_sign_larger  = w_a_exp_larger ? w_sign_a : w_sign_b;
wire [3:0] w_exp_larger   = w_a_exp_larger ? w_exp_a : w_exp_b;
wire [2:0] w_mant_larger  = w_a_exp_larger ? w_mant_a : w_mant_b;
wire       w_larger_normal = w_a_exp_larger ? w_a_is_normal : w_b_is_normal;

wire       w_sign_smaller  = w_a_exp_larger ? w_sign_b : w_sign_a;
wire [3:0] w_exp_smaller   = w_a_exp_larger ? w_exp_b : w_exp_a;
wire [2:0] w_mant_smaller  = w_a_exp_larger ? w_mant_b : w_mant_a;
wire       w_smaller_normal = w_a_exp_larger ? w_b_is_normal : w_a_is_normal;

wire [3:0] w_exp_diff = w_exp_larger - w_exp_smaller;

// Extended mantissas with implied bit
// Format: 1.mmm + 3 GRS bits = 7 bits total

wire [6:0] w_mant_larger_ext = w_larger_normal ? {1'b1, w_mant_larger, 3'b0} : 7'h0;
wire [6:0] w_mant_smaller_ext = w_smaller_normal ? {1'b1, w_mant_smaller, 3'b0} : 7'h0;

// Mantissa alignment (shift smaller mantissa right)

// Clamp shift amount
wire [2:0] w_shift_amt = (w_exp_diff > 4'd7) ? 3'd7 : w_exp_diff[2:0];

// Shift and capture sticky bits
wire [6:0] w_mant_smaller_shifted = w_mant_smaller_ext >> w_shift_amt;

// Sticky bit from shifted-out bits
wire [6:0] w_shift_mask = (7'h7F >> (7 - w_shift_amt));
wire w_sticky_from_shift = |(w_mant_smaller_ext & w_shift_mask);

// Mantissa addition/subtraction

wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// 8-bit addition to handle overflow
wire [7:0] w_mant_sum_raw;
wire [7:0] w_mant_larger_8 = {1'b0, w_mant_larger_ext};
wire [7:0] w_mant_smaller_8 = {1'b0, w_mant_smaller_shifted};

assign w_mant_sum_raw = w_effective_sub ?
    (w_mant_larger_8 - w_mant_smaller_8) :
    (w_mant_larger_8 + w_mant_smaller_8);

// Result sign (subtraction may invert if |B| > |A|)
wire w_sum_negative = w_effective_sub & w_mant_sum_raw[7];
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;

// Absolute value of sum
wire [7:0] w_mant_sum_abs = w_sum_negative ? (~w_mant_sum_raw + 8'd1) : w_mant_sum_raw;

// Normalization using priority encoder (simple for 8 bits)

// Find leading one position
wire [2:0] w_lz_count;
assign w_lz_count = w_mant_sum_abs[7] ? 3'd0 :
                    w_mant_sum_abs[6] ? 3'd1 :
                    w_mant_sum_abs[5] ? 3'd2 :
                    w_mant_sum_abs[4] ? 3'd3 :
                    w_mant_sum_abs[3] ? 3'd4 :
                    w_mant_sum_abs[2] ? 3'd5 :
                    w_mant_sum_abs[1] ? 3'd6 : 3'd7;

// Handle addition overflow (bit 7 set)
wire w_add_overflow = ~w_effective_sub & w_mant_sum_abs[7];

// Normalized mantissa
// For normal case (bit 6 = 1), lz_count = 1, but no shift needed since implied 1 is at correct position
// For cancellation (bit 5 = 1), lz_count = 2, need shift by 1 to move implied 1 to bit 6
wire [2:0] w_norm_shift = w_add_overflow ? 3'd0 :
    (w_lz_count <= 3'd1) ? 3'd0 : (w_lz_count - 3'd1);
wire [7:0] w_mant_norm = w_add_overflow ?
    {1'b0, w_mant_sum_abs[7:1]} : (w_mant_sum_abs << w_norm_shift);

// Capture sticky bit lost during overflow right-shift
wire w_overflow_lost_sticky = w_add_overflow & w_mant_sum_abs[0];

// Adjusted exponent
wire signed [5:0] w_exp_adjusted = $signed({2'b0, w_exp_larger}) +
    {5'b0, w_add_overflow} - $signed({3'b0, w_norm_shift});

// Round-to-Nearest-Even rounding

// Extract mantissa, guard, round, sticky
// After normalization, implied 1 is at bit 6, mantissa at [5:3], GRS at [2:0]
wire [2:0] w_mant_pre = w_mant_norm[5:3];
wire w_guard = w_mant_norm[2];
wire w_round = w_mant_norm[1];
wire w_sticky = w_mant_norm[0] | w_sticky_from_shift | w_overflow_lost_sticky;

// RNE: round up if G=1 and (R=1 or S=1 or LSB=1)
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_pre[0]);

// Apply rounding
wire [3:0] w_mant_rounded = {1'b0, w_mant_pre} + {3'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[3];

// Final mantissa
wire [2:0] w_mant_final = w_round_overflow ? 3'h0 : w_mant_rounded[2:0];

// Final exponent
wire signed [5:0] w_exp_final = w_exp_adjusted + {5'b0, w_round_overflow};

// Special case handling

wire w_any_nan = w_a_is_nan | w_b_is_nan;

// Overflow: exp > 15 or result is NaN pattern
wire w_overflow = ~w_exp_final[5] & (w_exp_final > 6'sd15);

// Check if result would be NaN pattern
wire w_result_is_nan_pattern = (w_exp_final == 6'sd15) & (w_mant_final == 3'h7);

// Underflow: exp < 1
wire w_underflow = w_exp_final[5] | (w_exp_final < 6'sd1);

// Result assembly

logic [7:0] r_result;
logic       r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_result_sign, w_exp_final[3:0], w_mant_final};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_any_nan) begin
        r_result = {1'b0, 4'hF, 3'h7};  // qNaN
        r_invalid = 1'b1;
    end else if (w_overflow | w_result_is_nan_pattern) begin
        r_result = {w_result_sign, 4'hF, 3'h6};  // Max normal (no infinity in E4M3)
        r_overflow = 1'b1;
    end else if (w_underflow | (w_mant_sum_abs == 8'h0)) begin
        r_result = {w_result_sign, 4'h0, 3'h0};
        r_underflow = w_underflow & (w_mant_sum_abs != 8'h0);
    end else if (w_a_eff_zero) begin
        r_result = i_b;
    end else if (w_b_eff_zero) begin
        r_result = i_a;
    end
end

// Output assignment
assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule

