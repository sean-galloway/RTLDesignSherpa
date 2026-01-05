// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_min
// Purpose: BF16 minimum of two values
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

module math_bf16_min (
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    output logic [15:0] ow_result
);

// BF16 Min: returns minimum of two values
// IEEE 754 semantics:
// - If either is NaN, return the non-NaN (or NaN if both)
// - min(+0, -0) = -0

// Field extraction - A
wire w_sign_a = i_a[15];
wire [7:0] w_exp_a = i_a[14:7];
wire [6:0] w_mant_a = i_a[6:0];

// Field extraction - B
wire w_sign_b = i_b[15];
wire [7:0] w_exp_b = i_b[14:7];
wire [6:0] w_mant_b = i_b[6:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 8'h0) & (w_mant_a == 7'h0);
wire w_b_is_zero = (w_exp_b == 8'h0) & (w_mant_b == 7'h0);
wire w_both_zero = w_a_is_zero & w_b_is_zero;

wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h0);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h0);

// Magnitude comparison
wire [14:0] w_mag_a = i_a[14:0];
wire [14:0] w_mag_b = i_b[14:0];

// Determine which is less
logic w_a_less;

always_comb begin
    if (w_both_zero) begin
        // min(+0, -0) = -0: prefer negative
        w_a_less = w_sign_a;
    end else if (w_sign_a != w_sign_b) begin
        // Different signs: negative is less
        w_a_less = w_sign_a;
    end else if (w_sign_a == 1'b0) begin
        // Both positive: smaller magnitude is less
        w_a_less = (w_mag_a <= w_mag_b);
    end else begin
        // Both negative: larger magnitude is less (more negative)
        w_a_less = (w_mag_a >= w_mag_b);
    end
end

// Result selection
assign ow_result = w_a_is_nan ? i_b :    // a is NaN, return b
                   w_b_is_nan ? i_a :    // b is NaN, return a
                   w_a_less ? i_a : i_b;

endmodule

