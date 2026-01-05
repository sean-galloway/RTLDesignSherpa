// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp16_clamp
// Purpose: FP16 clamp to [min, max] range
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

module math_fp16_clamp (
    input  logic [15:0] i_x,
    input  logic [15:0] i_min,
    input  logic [15:0] i_max,
    output logic [15:0] ow_result
);

// FP16 Clamp: clamp(x, min, max) = min(max(x, min), max)
// Returns x constrained to [min, max] range

// Field extraction
wire w_sign_x = i_x[15];
wire [4:0] w_exp_x = i_x[14:10];
wire [9:0] w_mant_x = i_x[9:0];

wire w_sign_min = i_min[15];
wire [4:0] w_exp_min = i_min[14:10];
wire [9:0] w_mant_min = i_min[9:0];

wire w_sign_max = i_max[15];
wire [4:0] w_exp_max = i_max[14:10];
wire [9:0] w_mant_max = i_max[9:0];

// NaN detection
wire w_x_is_nan = (w_exp_x == 5'h1F) & (w_mant_x != 10'h0);
wire w_min_is_nan = (w_exp_min == 5'h1F) & (w_mant_min != 10'h0);
wire w_max_is_nan = (w_exp_max == 5'h1F) & (w_mant_max != 10'h0);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

// Magnitude for comparison
wire [14:0] w_mag_x = i_x[14:0];
wire [14:0] w_mag_min = i_min[14:0];
wire [14:0] w_mag_max = i_max[14:0];

// Comparison logic
function automatic logic fp_less_than(
    input logic [15:0] a,
    input logic [15:0] b
);
    logic a_sign, b_sign;
    logic [14:0] a_mag, b_mag;

    a_sign = a[15];
    b_sign = b[15];
    a_mag = a[14:0];
    b_mag = b[14:0];

    if (a_sign != b_sign) begin
        return a_sign;  // Negative < positive
    end else if (a_sign == 1'b0) begin
        return (a_mag < b_mag);
    end else begin
        return (a_mag > b_mag);
    end
endfunction

wire w_x_lt_min = fp_less_than(i_x, i_min);
wire w_x_gt_max = fp_less_than(i_max, i_x);

// Result selection
assign ow_result = w_any_nan ? i_x :       // Propagate NaN
                   w_x_lt_min ? i_min :    // x < min: return min
                   w_x_gt_max ? i_max :    // x > max: return max
                   i_x;                    // min <= x <= max: return x

endmodule

