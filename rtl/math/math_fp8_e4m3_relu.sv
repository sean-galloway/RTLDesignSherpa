// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_relu
// Purpose: FP8_E4M3 ReLU activation function: max(0, x)
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

module math_fp8_e4m3_relu (
    input  logic [7:0] i_a,
    output logic [7:0] ow_result
);

// FP8_E4M3 ReLU: max(0, x)
// Simply return 0 if negative, else pass through

wire w_sign = i_a[7];
wire [3:0] w_exp = i_a[6:3];
wire [2:0] w_mant = i_a[2:0];

// Special case detection
wire w_is_zero = (w_exp == 4'h0) & (w_mant == 3'h0);
wire w_is_nan = (w_exp == 4'hF) & (w_mant == 3'h7);

// ReLU logic: if negative (and not NaN), output zero
// NaN propagates as NaN
assign ow_result = w_is_nan ? i_a :          // Propagate NaN
                   w_sign   ? 8'h0 :    // Negative -> 0
                              i_a;           // Positive -> pass through

endmodule

