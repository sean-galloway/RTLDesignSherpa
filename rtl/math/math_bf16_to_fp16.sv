// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_to_fp16
// Purpose: Convert BF16 to FP16
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

module math_bf16_to_fp16 (
    input  logic [15:0] i_a,
    output logic [15:0] ow_result,
    output logic                  ow_overflow,
    output logic                  ow_underflow,
    output logic                  ow_invalid
);

// BF16 field extraction
wire       w_sign = i_a[15];
wire [7:0] w_exp  = i_a[14:7];
wire [6:0] w_mant = i_a[6:0];

// Special case detection
wire w_is_zero = (w_exp == 8'h0) & (w_mant == 7'h0);
wire w_is_subnormal = (w_exp == 8'h0) & (w_mant != 7'h0);
wire w_is_inf = (w_exp == 8'hFF) & (w_mant == 7'h0);
wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 7'h0);

// Exponent conversion
wire signed [9:0] w_exp_adjusted = $signed({2'b0, w_exp}) - 10'sd112;

wire w_exp_overflow = ~w_exp_adjusted[9] & (w_exp_adjusted > 10'sd30);
wire w_exp_underflow = w_exp_adjusted[9] | (w_exp_adjusted < 10'sd1);

// Mantissa extension
wire [9:0] w_mant_converted = {w_mant, 3'b0};
wire w_mant_overflow = 1'b0;

// Final exponent
wire [4:0] w_exp_final = w_mant_overflow ?
    (w_exp_adjusted[4:0] + 5'd1) : w_exp_adjusted[4:0];

// Check for final overflow (but not if underflow - negative exp has garbage low bits)
wire w_final_overflow = ~w_exp_underflow & (w_exp_overflow | (w_exp_final >= 5'h1F));

// Result assembly
logic [15:0] r_result;
logic r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_sign, w_exp_final, w_mant_converted};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_is_nan) begin
        r_result = {w_sign, 5'h1F, 10'h200};
        r_invalid = 1'b1;
    end else if (w_is_inf | w_final_overflow) begin
        r_result = {w_sign, 5'h1F, 10'h0};
        r_overflow = ~w_is_inf;
    end else if (w_is_zero | w_is_subnormal | w_exp_underflow) begin
        r_result = {w_sign, 5'h0, 10'h0};
        r_underflow = w_exp_underflow & ~w_is_zero & ~w_is_subnormal;
    end
end

assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule

