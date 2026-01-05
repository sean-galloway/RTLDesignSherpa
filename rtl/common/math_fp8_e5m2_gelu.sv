// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_gelu
// Purpose: FP8_E5M2 GELU activation function: x * sigmoid(1.702*x)
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

module math_fp8_e5m2_gelu (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result
);

// FP8_E5M2 GELU: Gaussian Error Linear Unit
// Approximation: x * sigmoid(1.702 * x)
//
// GELU characteristics:
//   GELU(0) = 0
//   GELU(x) ≈ x for large positive x
//   GELU(x) ≈ 0 for large negative x
//   Smooth, non-monotonic near x ≈ -0.5

wire w_sign = i_a[7];
wire [4:0] w_exp = i_a[6:2];
wire [1:0] w_mant = i_a[1:0];

// Special case detection
wire w_is_zero = (w_exp == 5'h0) & (w_mant == 2'h0);
wire w_is_subnormal = (w_exp == 5'h0) & (w_mant != 2'h0);
wire w_is_inf = (w_exp == 5'h1F) & (w_mant == 2'h0);
wire w_is_nan = (w_exp == 5'h1F) & (w_mant != 2'h0);

// Constants
localparam [7:0] ZERO = 8'h0;

// Determine magnitude category
// Large positive: GELU(x) ≈ x
// Large negative: GELU(x) ≈ 0
wire w_large_pos = ~w_sign & (w_exp >= 5'd17);
wire w_large_neg = w_sign & (w_exp >= 5'd17);

// Near zero: GELU(x) ≈ 0.5 * x
wire w_near_zero = (w_exp < 5'd13) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [7:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf) begin
        r_result = w_sign ? ZERO : i_a;  // +inf -> +inf, -inf -> 0
    end else if (w_large_neg) begin
        // Large negative: GELU ≈ 0
        r_result = ZERO;
    end else if (w_large_pos) begin
        // Large positive: GELU ≈ x
        r_result = i_a;
    end else if (w_near_zero) begin
        // Small x: GELU(x) ≈ 0.5 * x
        // Halving: decrement exponent by 1
        if (w_exp > 5'd1) begin
            r_result = {w_sign, w_exp - 5'd1, w_mant};
        end else begin
            r_result = ZERO;  // Underflow to zero
        end
    end else begin
        // Medium range: approximate
        if (w_sign) begin
            // Negative medium: small negative output
            // GELU(-1) ≈ -0.159, approximate as -0.125 = -2^-3
            r_result = {1'b1, 5'd12, 2'h0};
        end else begin
            // Positive medium: slightly less than x
            // GELU(1) ≈ 0.841, approximate as 0.75
            r_result = {1'b0, 5'd14, 2'd2};
        end
    end
end

assign ow_result = r_result;

endmodule

