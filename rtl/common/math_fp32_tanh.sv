// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp32_tanh
// Purpose: FP32 Tanh activation function
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp_activations.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp32_tanh (
    input  logic [31:0] i_a,
    output logic [31:0] ow_result
);

// FP32 Tanh: (exp(x)-exp(-x))/(exp(x)+exp(-x))
// Piecewise linear approximation
//
// tanh characteristics:
//   tanh(0) = 0
//   tanh(-inf) = -1, tanh(+inf) = +1
//   tanh(-x) = -tanh(x) (odd function)
//   Nearly linear around 0 with slope 1, saturates at ±1

wire w_sign = i_a[31];
wire [7:0] w_exp = i_a[30:23];
wire [22:0] w_mant = i_a[22:0];

// Special case detection
wire w_is_zero = (w_exp == 8'h0) & (w_mant == 23'h0);
wire w_is_subnormal = (w_exp == 8'h0) & (w_mant != 23'h0);
wire w_is_inf = (w_exp == 8'hFF) & (w_mant == 23'h0);
wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 23'h0);

// Constants
localparam [31:0] ZERO = 32'h0;
localparam [31:0] POS_ONE = {1'b0, 8'd127, 23'h0};   // +1.0
localparam [31:0] NEG_ONE = {1'b1, 8'd127, 23'h0};   // -1.0

// Determine magnitude category
// |x| >= 2 means exp >= bias+1 (saturates to ±1)
wire w_saturated = (w_exp >= 8'd128);

// |x| < 0.5 means exp < bias-1 (nearly linear region)
wire w_near_zero = (w_exp < 8'd126) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [31:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf | w_saturated) begin
        // Large magnitude: saturate to ±1
        r_result = w_sign ? NEG_ONE : POS_ONE;
    end else if (w_near_zero) begin
        // Small magnitude: tanh(x) ≈ x (slope ~1)
        r_result = i_a;
    end else begin
        // Medium range: interpolate
        // Approximate as ±0.75 for moderate values
        r_result = {w_sign, 8'd126, 23'd4194304};  // ±0.75
    end
end

assign ow_result = r_result;

endmodule

