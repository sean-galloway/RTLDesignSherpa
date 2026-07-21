// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_exponent_adder
// Purpose: FP8 E4M3 exponent adder for multiplication with bias handling
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e4m3_exponent_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e4m3_exponent_adder(
    input  logic [3:0] i_exp_a,
    input  logic [3:0] i_exp_b,
    input  logic       i_norm_adjust,
    output logic [3:0] ow_exp_out,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_a_is_zero,
    output logic       ow_b_is_zero,
    output logic       ow_a_is_nan,
    output logic       ow_b_is_nan
);

// FP8 E4M3 exponent parameters
// Bias = 7, valid exponent range: 1-15
// Note: E4M3 has no infinity! exp=15 is valid for max normal value

// Special case detection
wire w_a_is_zero = (i_exp_a == 4'h0);
wire w_b_is_zero = (i_exp_b == 4'h0);

// NaN detection: exp=15, mantissa=111 (checked externally)
// Here we just detect exp=15 for special handling
wire w_a_exp_max = (i_exp_a == 4'hF);
wire w_b_exp_max = (i_exp_b == 4'hF);

// Exponent sum: exp_a + exp_b
// Extended to 6 bits to catch overflow
wire [5:0] w_exp_sum = {2'b0, i_exp_a} + {2'b0, i_exp_b};

// Subtract bias (7) and add normalization adjustment
// Result = exp_sum - 7 + norm_adjust
wire signed [6:0] w_exp_biased = $signed({1'b0, w_exp_sum}) - 7'sd7 + {6'b0, i_norm_adjust};

// Overflow detection: result > 15 (max valid exponent)
wire w_overflow = ~w_exp_biased[6] & (w_exp_biased > 7'sd15);

// Underflow detection: result < 1
wire w_underflow = w_exp_biased[6] | (w_exp_biased < 7'sd1);

// Clamp exponent to valid range
wire [3:0] w_exp_clamped;
assign w_exp_clamped = w_overflow ? 4'hF :
                       w_underflow ? 4'h0 :
                       w_exp_biased[3:0];

// Output assignments
assign ow_exp_out = w_exp_clamped;
assign ow_overflow = w_overflow;
assign ow_underflow = w_underflow;
assign ow_a_is_zero = w_a_is_zero;
assign ow_b_is_zero = w_b_is_zero;
assign ow_a_is_nan = w_a_exp_max;  // Partial NaN check (mant check done externally)
assign ow_b_is_nan = w_b_exp_max;  // Partial NaN check (mant check done externally)

endmodule
