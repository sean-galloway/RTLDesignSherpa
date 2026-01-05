// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp16_to_fp8_e4m3
// Purpose: Convert FP16 to FP8_E4M3 (downconvert with RNE rounding)
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp_conversions.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp16_to_fp8_e4m3 (
    input  logic [15:0] i_a,
    output logic [7:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// FP16 field extraction
wire       w_sign = i_a[15];
wire [4:0] w_exp  = i_a[14:10];
wire [9:0] w_mant = i_a[9:0];

// Special case detection
wire w_is_zero = (w_exp == 5'h0) & (w_mant == 10'h0);
wire w_is_subnormal = (w_exp == 5'h0) & (w_mant != 10'h0);
wire w_is_inf = (w_exp == 5'h1F) & (w_mant == 10'h0);
wire w_is_nan = (w_exp == 5'h1F) & (w_mant != 10'h0);

// Exponent conversion with overflow/underflow detection
wire signed [6:0] w_exp_adjusted = $signed({2'b0, w_exp}) - 7'sd8;

wire w_exp_overflow = ~w_exp_adjusted[6] & (w_exp_adjusted > 7'sd15);
wire w_exp_underflow = w_exp_adjusted[6] | (w_exp_adjusted < 7'sd1);

// Mantissa truncation with rounding
wire [2:0] w_mant_truncated = w_mant[9:7];
wire w_guard = w_mant[6];
wire w_round = w_mant[5];
wire w_sticky = |w_mant[4:0];

// RNE rounding
wire w_lsb = w_mant_truncated[0];
wire w_round_up = w_guard & (w_round | w_sticky | w_lsb);

wire [3:0] w_mant_rounded = {1'b0, w_mant_truncated} + {3'b0, w_round_up};
wire w_mant_overflow = w_mant_rounded[3];

// Final exponent with rounding adjustment
wire [3:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[3:0] + 4'd1) : w_exp_adjusted[3:0];
wire [2:0] w_mant_final = w_mant_overflow ? 3'h0 : w_mant_rounded[2:0];

// Check for overflow after rounding (but not if underflow - negative exp has garbage low bits)

// FP8_E4M3 has no infinity - only overflow if result would be NaN pattern
wire w_result_is_nan_pattern = (w_exp_final == 4'hF) & (w_mant_final >= 3'h7);
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | w_result_is_nan_pattern);

// Result assembly
logic [7:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_sign, w_exp_final, w_mant_final};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
        // Propagate as quiet NaN
        r_result = {w_sign, 4'hF, 3'h7};
        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
        // FP8_E4M3 has no infinity - saturate to max normal
        r_result = {w_sign, 4'hF, 3'h6};
        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        // Underflow to zero
        r_result = {w_sign, 4'h0, 3'h0};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule

