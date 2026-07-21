// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp16_silu
// Purpose: FP16 SiLU/Swish activation function: x * sigmoid(x)
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

module math_fp16_silu (
    input  logic [15:0] i_a,
    output logic [15:0] ow_result
);

// FP16 SiLU/Swish: x * sigmoid(x)
//
// SiLU characteristics:
//   SiLU(0) = 0
//   SiLU(x) ≈ x for large positive x (sigmoid ≈ 1)
//   SiLU(x) ≈ 0 for large negative x (sigmoid ≈ 0)
//   Has a small negative dip around x ≈ -1.28

wire w_sign = i_a[15];
wire [4:0] w_exp = i_a[14:10];
wire [9:0] w_mant = i_a[9:0];

// Special case detection
wire w_is_zero = (w_exp == 5'h0) & (w_mant == 10'h0);
wire w_is_subnormal = (w_exp == 5'h0) & (w_mant != 10'h0);
wire w_is_inf = (w_exp == 5'h1F) & (w_mant == 10'h0);
wire w_is_nan = (w_exp == 5'h1F) & (w_mant != 10'h0);

// Constants
localparam [15:0] ZERO = 16'h0;

// Determine magnitude category
wire w_large_pos = ~w_sign & (w_exp >= 5'd17);
wire w_large_neg = w_sign & (w_exp >= 5'd17);
wire w_near_zero = (w_exp < 5'd13) | w_is_zero | w_is_subnormal;

// Simplified piecewise result
logic [15:0] r_result;

always_comb begin
    if (w_is_nan) begin
        r_result = i_a;  // Propagate NaN
    end else if (w_is_inf) begin
        r_result = w_sign ? ZERO : i_a;  // +inf -> +inf, -inf -> 0
    end else if (w_large_neg) begin
        // Large negative: SiLU ≈ 0
        r_result = ZERO;
    end else if (w_large_pos) begin
        // Large positive: SiLU ≈ x (sigmoid ≈ 1)
        r_result = i_a;
    end else if (w_near_zero) begin
        // Small x: SiLU(x) ≈ 0.5 * x (sigmoid(0) = 0.5)
        if (w_exp > 5'd1) begin
            r_result = {w_sign, w_exp - 5'd1, w_mant};
        end else begin
            r_result = ZERO;
        end
    end else begin
        // Medium range
        if (w_sign) begin
            // Negative medium: small negative (dip region)
            // SiLU(-1) ≈ -0.269, approximate as -0.25
            r_result = {1'b1, 5'd13, 10'h0};
        end else begin
            // Positive medium: somewhat less than x
            // SiLU(1) ≈ 0.731, approximate as 0.75
            r_result = {1'b0, 5'd14, 10'd512};
        end
    end
end

assign ow_result = r_result;

endmodule

