// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_comparator
// Purpose: FP8_E5M2 comparator with EQ/LT/GT/LE/GE/NE/UNORD flags
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp_comparisons.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e5m2_comparator (
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic              ow_eq,    // a == b
    output logic              ow_lt,    // a < b
    output logic              ow_gt,    // a > b
    output logic              ow_le,    // a <= b
    output logic              ow_ge,    // a >= b
    output logic              ow_ne,    // a != b
    output logic              ow_unord  // Unordered (either is NaN)
);

// FP8_E5M2 Comparator
// IEEE 754 comparison semantics:
// - NaN compares unordered with everything (including itself)
// - +0 == -0
// - Infinity compares as expected

// Field extraction - A
wire w_sign_a = i_a[7];
wire [4:0] w_exp_a = i_a[6:2];
wire [1:0] w_mant_a = i_a[1:0];

// Field extraction - B
wire w_sign_b = i_b[7];
wire [4:0] w_exp_b = i_b[6:2];
wire [1:0] w_mant_b = i_b[1:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 5'h0) & (w_mant_a == 2'h0);
wire w_b_is_zero = (w_exp_b == 5'h0) & (w_mant_b == 2'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;

wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);
wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);

wire w_either_nan = w_a_is_nan | w_b_is_nan;

// Magnitude comparison (treating as unsigned integers, ignoring sign)
// For positive numbers: larger exp/mant means larger value
// For negative numbers: larger exp/mant means smaller value (more negative)
wire [6:0] w_mag_a = i_a[6:0];  // exp + mant
wire [6:0] w_mag_b = i_b[6:0];

wire w_mag_a_gt_b = w_mag_a > w_mag_b;
wire w_mag_a_lt_b = w_mag_a < w_mag_b;
wire w_mag_eq = (w_mag_a == w_mag_b);

// Determine ordering
logic w_a_less_than_b;
logic w_a_equal_b;

always_comb begin
    // Default: compare magnitudes
    w_a_equal_b = 1'b0;
    w_a_less_than_b = 1'b0;

    if (w_both_zero) begin
        // +0 == -0
        w_a_equal_b = 1'b1;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: negative is less
        w_a_less_than_b = w_sign_a;  // a is negative, so a < b
    end else if (w_sign_a == 1'b0) begin
        // Both positive: larger magnitude is greater
        w_a_less_than_b = w_mag_a_lt_b;
        w_a_equal_b = w_mag_eq;
    end else begin
        // Both negative: larger magnitude is less (more negative)
        w_a_less_than_b = w_mag_a_gt_b;
        w_a_equal_b = w_mag_eq;
    end
end

// Output assignments
assign ow_unord = w_either_nan;
assign ow_eq = ~w_either_nan & w_a_equal_b;
assign ow_lt = ~w_either_nan & w_a_less_than_b;
assign ow_gt = ~w_either_nan & ~w_a_less_than_b & ~w_a_equal_b;
assign ow_le = ~w_either_nan & (w_a_less_than_b | w_a_equal_b);
assign ow_ge = ~w_either_nan & (~w_a_less_than_b | w_a_equal_b);
assign ow_ne = ~w_either_nan & ~w_a_equal_b;

endmodule

