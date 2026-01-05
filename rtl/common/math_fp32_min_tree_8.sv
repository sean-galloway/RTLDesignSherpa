// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp32_min_tree_8
// Purpose: FP32 minimum tree reduction for 8 values
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

module math_fp32_min_tree_8 (
    input  logic [31:0] i_data [8],
    output logic [31:0] ow_min,
    output logic [7:0] ow_min_idx  // One-hot index of minimum
);

// FP32 Min Tree: finds minimum of 8 values
// Uses binary reduction tree for O(log N) depth

// Min function for two values
function automatic logic [31:0] fp_min(
    input logic [31:0] a,
    input logic [31:0] b
);
    logic a_sign, b_sign;
    logic [30:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;
    logic a_less;

    a_sign = a[31];
    b_sign = b[31];
    a_mag = a[30:0];
    b_mag = b[30:0];
    a_is_nan = (a[30:23] == 8'hFF) & (a[22:0] != 23'h0);
    b_is_nan = (b[30:23] == 8'hFF) & (b[22:0] != 23'h0);

    // Handle NaN
    if (a_is_nan) return b;
    if (b_is_nan) return a;

    // Compare
    if (a_sign != b_sign) begin
        a_less = a_sign;  // Negative < positive
    end else if (a_sign == 1'b0) begin
        a_less = (a_mag <= b_mag);
    end else begin
        a_less = (a_mag >= b_mag);
    end

    return a_less ? a : b;
endfunction

// Binary reduction tree

// Level 0: 8 -> 4
logic [31:0] w_level0 [4];
assign w_level0[0] = fp_min(i_data[0], i_data[1]);
assign w_level0[1] = fp_min(i_data[2], i_data[3]);
assign w_level0[2] = fp_min(i_data[4], i_data[5]);
assign w_level0[3] = fp_min(i_data[6], i_data[7]);

// Level 1: 4 -> 2
logic [31:0] w_level1 [2];
assign w_level1[0] = fp_min(w_level0[0], w_level0[1]);
assign w_level1[1] = fp_min(w_level0[2], w_level0[3]);

// Level 2: 2 -> 1
logic [31:0] w_level2 [1];
assign w_level2[0] = fp_min(w_level1[0], w_level1[1]);

// Final output
assign ow_min = w_level2[0];

// Generate one-hot index of minimum
genvar gi;
generate
    for (gi = 0; gi < 8; gi = gi + 1) begin : gen_idx
        assign ow_min_idx[gi] = (i_data[gi] == ow_min);
    end
endgenerate

endmodule

