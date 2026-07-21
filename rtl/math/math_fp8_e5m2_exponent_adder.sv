// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_exponent_adder
// Purpose: FP8 E5M2 exponent adder for multiplication with bias handling
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e5m2_exponent_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e5m2_exponent_adder(
    input  logic [4:0] i_exp_a,
    input  logic [4:0] i_exp_b,
    input  logic       i_norm_adjust,
    output logic [4:0] ow_exp_out,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_a_is_zero,
    output logic       ow_b_is_zero,
    output logic       ow_a_is_inf,
    output logic       ow_b_is_inf
);

// FP8 E5M2 exponent parameters
// Bias = 15, valid exponent range: 1-30
// exp=31 is infinity (mant=0) or NaN (mant!=0)

// Special case detection
wire w_a_is_zero = (i_exp_a == 5'h00);
wire w_b_is_zero = (i_exp_b == 5'h00);

// Infinity detection: exp=31
wire w_a_is_inf = (i_exp_a == 5'h1F);
wire w_b_is_inf = (i_exp_b == 5'h1F);

// Exponent sum: exp_a + exp_b
// Extended to 7 bits to catch overflow
wire [6:0] w_exp_sum = {2'b0, i_exp_a} + {2'b0, i_exp_b};

// Subtract bias (15) and add normalization adjustment
// Result = exp_sum - 15 + norm_adjust
wire signed [7:0] w_exp_biased = $signed({1'b0, w_exp_sum}) - 8'sd15 + {7'b0, i_norm_adjust};

// Overflow detection: result > 30 (31 reserved for inf/NaN)
wire w_overflow = ~w_exp_biased[7] & (w_exp_biased > 8'sd30);

// Underflow detection: result < 1
wire w_underflow = w_exp_biased[7] | (w_exp_biased < 8'sd1);

// Clamp exponent to valid range
wire [4:0] w_exp_clamped;
assign w_exp_clamped = w_overflow ? 5'h1F :
                       w_underflow ? 5'h00 :
                       w_exp_biased[4:0];

// Output assignments
assign ow_exp_out = w_exp_clamped;
assign ow_overflow = w_overflow;
assign ow_underflow = w_underflow;
assign ow_a_is_zero = w_a_is_zero;
assign ow_b_is_zero = w_b_is_zero;
assign ow_a_is_inf = w_a_is_inf;
assign ow_b_is_inf = w_b_is_inf;

endmodule
