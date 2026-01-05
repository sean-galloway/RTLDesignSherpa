// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_max_tree_8
// Purpose: BF16 maximum tree reduction for 8 values
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

module math_bf16_max_tree_8 (
    input  logic [15:0] i_data [8],
    output logic [15:0] ow_max,
    output logic [7:0] ow_max_idx  // One-hot index of maximum
);

// BF16 Max Tree: finds maximum of 8 values
// Uses binary reduction tree for O(log N) depth

// Max function for two values
function automatic logic [15:0] fp_max(
    input logic [15:0] a,
    input logic [15:0] b
);
    logic a_sign, b_sign;
    logic [14:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;
    logic a_greater;

    a_sign = a[15];
    b_sign = b[15];
    a_mag = a[14:0];
    b_mag = b[14:0];
    a_is_nan = (a[14:7] == 8'hFF) & (a[6:0] != 7'h0);
    b_is_nan = (b[14:7] == 8'hFF) & (b[6:0] != 7'h0);

    // Handle NaN
    if (a_is_nan) return b;
    if (b_is_nan) return a;

    // Compare
    if (a_sign != b_sign) begin
        a_greater = ~a_sign;  // Positive > negative
    end else if (a_sign == 1'b0) begin
        a_greater = (a_mag >= b_mag);
    end else begin
        a_greater = (a_mag <= b_mag);
    end

    return a_greater ? a : b;
endfunction

// Comparison function returning 1 if a > b
function automatic logic fp_gt(
    input logic [15:0] a,
    input logic [15:0] b
);
    logic a_sign, b_sign;
    logic [14:0] a_mag, b_mag;
    logic a_is_nan, b_is_nan;

    a_sign = a[15];
    b_sign = b[15];
    a_mag = a[14:0];
    b_mag = b[14:0];
    a_is_nan = (a[14:7] == 8'hFF) & (a[6:0] != 7'h0);
    b_is_nan = (b[14:7] == 8'hFF) & (b[6:0] != 7'h0);

    if (a_is_nan | b_is_nan) return 1'b0;

    if (a_sign != b_sign) begin
        return ~a_sign;
    end else if (a_sign == 1'b0) begin
        return (a_mag > b_mag);
    end else begin
        return (a_mag < b_mag);
    end
endfunction

// Binary reduction tree

// Level 0: 8 -> 4
logic [15:0] w_level0 [4];
assign w_level0[0] = fp_max(i_data[0], i_data[1]);
assign w_level0[1] = fp_max(i_data[2], i_data[3]);
assign w_level0[2] = fp_max(i_data[4], i_data[5]);
assign w_level0[3] = fp_max(i_data[6], i_data[7]);

// Level 1: 4 -> 2
logic [15:0] w_level1 [2];
assign w_level1[0] = fp_max(w_level0[0], w_level0[1]);
assign w_level1[1] = fp_max(w_level0[2], w_level0[3]);

// Level 2: 2 -> 1
logic [15:0] w_level2 [1];
assign w_level2[0] = fp_max(w_level1[0], w_level1[1]);

// Final output
assign ow_max = w_level2[0];

// Generate one-hot index of maximum
// Compare each input against the maximum
genvar gi;
generate
    for (gi = 0; gi < 8; gi = gi + 1) begin : gen_idx
        assign ow_max_idx[gi] = (i_data[gi] == ow_max);
    end
endgenerate

endmodule

