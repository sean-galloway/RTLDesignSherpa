// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_tanh
// Purpose: FP8_E4M3 Tanh activation function
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

module math_fp8_e4m3_tanh (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result
);

// FP8_E4M3 Tanh: (exp(x)-exp(-x))/(exp(x)+exp(-x))
// Piecewise linear approximation
//
// tanh characteristics:
//   tanh(0) = 0
//   tanh(-inf) = -1, tanh(+inf) = +1
//   tanh(-x) = -tanh(x) (odd function)
//   Nearly linear around 0 with slope 1, saturates at ±1

wire w_sign = i_a[7];
wire [3:0] w_exp = i_a[6:3];
wire [2:0] w_mant = i_a[2:0];

// Special case detection
wire w_is_zero = (w_exp == 4'h0) & (w_mant == 3'h0);
wire w_is_subnormal = (w_exp == 4'h0) & (w_mant != 3'h0);
wire w_is_inf = 1'b0;
wire w_is_nan = (w_exp == 4'hF) & (w_mant == 3'h7);

// Constants
localparam [7:0] ZERO = 8'h0;
localparam [7:0] POS_ONE = {1'b0, 4'd7, 3'h0};   // +1.0
localparam [7:0] NEG_ONE = {1'b1, 4'd7, 3'h0};   // -1.0

// Determine magnitude category
// |x| >= 2 means exp >= bias+1 (saturates to ±1)
wire w_saturated = (w_exp >= 4'd8);

// |x| < 0.5 means exp < bias-1 (nearly linear region)
wire w_near_zero = (w_exp < 4'd6) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [7:0] r_result;

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
        r_result = {w_sign, 4'd6, 3'd4};  // ±0.75
    end
end

assign ow_result = r_result;

endmodule

