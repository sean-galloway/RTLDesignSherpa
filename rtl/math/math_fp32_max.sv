// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp32_max
// Purpose: FP32 maximum of two values
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

module math_fp32_max (
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    output logic [31:0] ow_result
);

// FP32 Max: returns maximum of two values
// IEEE 754 semantics:
// - If either is NaN, return the non-NaN (or NaN if both)
// - max(+0, -0) = +0

// Field extraction - A
wire w_sign_a = i_a[31];
wire [7:0] w_exp_a = i_a[30:23];
wire [22:0] w_mant_a = i_a[22:0];

// Field extraction - B
wire w_sign_b = i_b[31];
wire [7:0] w_exp_b = i_b[30:23];
wire [22:0] w_mant_b = i_b[22:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 8'h0) & (w_mant_a == 23'h0);
wire w_b_is_zero = (w_exp_b == 8'h0) & (w_mant_b == 23'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;

wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h0);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h0);

// Magnitude comparison
wire [30:0] w_mag_a = i_a[30:0];
wire [30:0] w_mag_b = i_b[30:0];

// Determine which is greater
logic w_a_greater;

always_comb begin
    if (w_both_zero) begin
        // max(+0, -0) = +0: prefer non-negative
        w_a_greater = ~w_sign_a;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: positive is greater
        w_a_greater = ~w_sign_a;
    end else if (w_sign_a == 1'b0) begin
        // Both positive: larger magnitude is greater
        w_a_greater = (w_mag_a >= w_mag_b);
    end else begin
        // Both negative: smaller magnitude is greater (less negative)
        w_a_greater = (w_mag_a <= w_mag_b);
    end
end

// Result selection
assign ow_result = w_a_is_nan ? i_b :      // a is NaN, return b
                   w_b_is_nan ? i_a :      // b is NaN, return a
                   w_a_greater ? i_a : i_b;

endmodule

