// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_to_fp8_e4m3
// Purpose: Convert FP8_E5M2 to FP8_E4M3
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

module math_fp8_e5m2_to_fp8_e4m3 (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// FP8_E5M2 field extraction
wire       w_sign = i_a[7];
wire [4:0] w_exp  = i_a[6:2];
wire [1:0] w_mant = i_a[1:0];

// Special case detection
wire w_is_zero = (w_exp == 5'h0) & (w_mant == 2'h0);
wire w_is_subnormal = (w_exp == 5'h0) & (w_mant != 2'h0);
wire w_is_inf = (w_exp == 5'h1F) & (w_mant == 2'h0);
wire w_is_nan = (w_exp == 5'h1F) & (w_mant != 2'h0);

// Exponent conversion
wire signed [6:0] w_exp_adjusted = $signed({2'b0, w_exp}) - 7'sd8;

wire w_exp_overflow = ~w_exp_adjusted[6] & (w_exp_adjusted > 7'sd15);
wire w_exp_underflow = w_exp_adjusted[6] | (w_exp_adjusted < 7'sd1);

// Mantissa extension
wire [2:0] w_mant_converted = {w_mant, 1'b0};
wire w_mant_overflow = 1'b0;

// Final exponent
wire [3:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[3:0] + 4'd1) : w_exp_adjusted[3:0];

// Check for final overflow (but not if underflow - negative exp has garbage low bits)

// FP8_E4M3 has no infinity - only overflow if result would be NaN pattern
wire w_result_is_nan_pattern = (w_exp_final == 4'hF) & (w_mant_converted >= 3'h7);
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | w_result_is_nan_pattern);

// Result assembly
logic [7:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_sign, w_exp_final, w_mant_converted};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
        r_result = {w_sign, 4'hF, 3'h7};
        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
        r_result = {w_sign, 4'hF, 3'h6};
        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        r_result = {w_sign, 4'h0, 3'h0};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule

