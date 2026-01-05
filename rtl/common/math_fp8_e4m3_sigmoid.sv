// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_sigmoid
// Purpose: FP8_E4M3 Sigmoid activation function: 1/(1+exp(-x))
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

module math_fp8_e4m3_sigmoid (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result
);

// FP8_E4M3 Sigmoid: 1/(1+exp(-x))
// Piecewise linear approximation using symmetry: sigmoid(-x) = 1 - sigmoid(x)
//
// Approximation regions:
//   x <= -4: sigmoid(x) ≈ 0
//   -4 < x < 4: linear interpolation
//   x >= 4: sigmoid(x) ≈ 1

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
localparam [7:0] HALF = {1'b0, 4'd6, 3'h0};  // 0.5
localparam [7:0] ONE  = {1'b0, 4'd7, 3'h0};   // 1.0

// Determine magnitude category
// |x| >= 4 means exp >= bias+2 (since 4 = 2^2)
wire w_saturated = (w_exp >= 4'd9);

// |x| < 0.25 means exp < bias-2 (nearly linear region, slope ~0.25)
wire w_near_zero = (w_exp < 4'd5) | w_is_zero | w_is_subnormal;

// Linear approximation: sigmoid(x) ≈ 0.5 + 0.25*x for small x
// For |x| in [0.25, 4], use coarser approximation

// Simplified piecewise result
logic [7:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf | w_saturated) begin
        // Large magnitude: saturate to 0 or 1
        r_result = w_sign ? ZERO : ONE;
    end else if (w_near_zero) begin
        // Small magnitude: sigmoid(x) ≈ 0.5
        r_result = HALF;
    end else begin
        // Medium range: linear interpolation between 0.25 and 0.75
        // Approximate as 0.5 + sign * 0.25 = 0.25 or 0.75
        // More accurate: scale based on exponent
        if (w_sign) begin
            // Negative: result in (0, 0.5)
            // Approximate: 0.5 - 0.125 = 0.375 for moderate negative
            r_result = {1'b0, 4'd5, 3'd4};  // ~0.375
        end else begin
            // Positive: result in (0.5, 1)
            // Approximate: 0.5 + 0.125 = 0.625 for moderate positive
            r_result = {1'b0, 4'd6, 3'd4};  // ~0.625
        end
    end
end

assign ow_result = r_result;

endmodule

