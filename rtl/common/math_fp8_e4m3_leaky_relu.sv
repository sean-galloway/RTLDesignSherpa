// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_leaky_relu
// Purpose: FP8_E4M3 Leaky ReLU activation: max(alpha*x, x)
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

module math_fp8_e4m3_leaky_relu #(
    parameter int ALPHA_SHIFT = 4  // alpha = 2^-ALPHA_SHIFT (default 0.0625)
) (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result
);

// FP8_E4M3 Leaky ReLU: max(alpha*x, x)
// alpha = 2^-ALPHA_SHIFT (implemented as exponent decrement)
// For negative x: output = alpha * x (small negative slope)
// For positive x: output = x

wire w_sign = i_a[7];
wire [3:0] w_exp = i_a[6:3];
wire [2:0] w_mant = i_a[2:0];

// Special case detection
wire w_is_zero = (w_exp == 4'h0) & (w_mant == 3'h0);
wire w_is_nan = (w_exp == 4'hF) & (w_mant == 3'h7);

// Leaky ReLU: multiply by alpha for negative values
// alpha * x = x * 2^-ALPHA_SHIFT = decrement exponent
wire [3:0] w_scaled_exp = (w_exp > ALPHA_SHIFT[3:0]) ?
                                     (w_exp - ALPHA_SHIFT[3:0]) : 4'h0;

assign ow_result = w_is_nan   ? i_a :                           // Propagate NaN
                   w_is_zero  ? 8'h0 :                     // Zero -> Zero
                   ~w_sign    ? i_a :                           // Positive -> pass through
                   {w_sign, w_scaled_exp, w_mant};            // Negative -> scale by alpha

endmodule

