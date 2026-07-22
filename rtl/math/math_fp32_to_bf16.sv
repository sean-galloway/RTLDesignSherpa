// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp32_to_bf16
// Purpose: Convert FP32 to BF16 (downconvert with RNE rounding)
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

module math_fp32_to_bf16 (
    input  logic [31:0] i_a,
    output logic [15:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// FP32 field extraction
wire       w_sign = i_a[31];
wire [7:0] w_exp  = i_a[30:23];
wire [22:0] w_mant = i_a[22:0];

// Special case detection
wire w_is_zero = (w_exp == 8'h0) & (w_mant == 23'h0);
wire w_is_subnormal = (w_exp == 8'h0) & (w_mant != 23'h0);
wire w_is_inf = (w_exp == 8'hFF) & (w_mant == 23'h0);
wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 23'h0);

// Exponent conversion with overflow/underflow detection
wire signed [9:0] w_exp_adjusted = $signed({2'b0, w_exp}) - 10'sd0;

wire w_exp_overflow = ~w_exp_adjusted[9] & (w_exp_adjusted > 10'sd254);
wire w_exp_underflow = w_exp_adjusted[9] | (w_exp_adjusted < 10'sd1);

// Mantissa truncation with rounding
wire [6:0] w_mant_truncated = w_mant[22:16];
wire w_guard = w_mant[15];
wire w_round = w_mant[14];
wire w_sticky = |w_mant[13:0];

// RNE rounding
wire w_lsb = w_mant_truncated[0];
wire w_round_up = w_guard & (w_round | w_sticky | w_lsb);

wire [7:0] w_mant_rounded = {1'b0, w_mant_truncated} + {7'b0, w_round_up};
wire w_mant_overflow = w_mant_rounded[7];

// Final exponent with rounding adjustment
wire [7:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[7:0] + 8'd1) : w_exp_adjusted[7:0];
wire [6:0] w_mant_final = w_mant_overflow ? 7'h0 : w_mant_rounded[6:0];

// Check for overflow after rounding (but not if underflow - negative exp has garbage low bits)
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | (w_exp_final >= 8'hFF));

// Result assembly
logic [15:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_sign, w_exp_final, w_mant_final};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
        // Propagate as quiet NaN
        r_result = {w_sign, 8'hFF, 7'h40};
        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
        // Overflow to infinity
        r_result = {w_sign, 8'hFF, 7'h0};
        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        // Underflow to zero
        r_result = {w_sign, 8'h0, 7'h0};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule

