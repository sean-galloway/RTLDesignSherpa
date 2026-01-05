// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_clamp
// Purpose: FP8_E4M3 clamp to [min, max] range
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

module math_fp8_e4m3_clamp (
    input  logic [7:0] i_x,
    input  logic [7:0] i_min,
    input  logic [7:0] i_max,
    output logic [7:0] ow_result
);

// FP8_E4M3 Clamp: clamp(x, min, max) = min(max(x, min), max)
// Returns x constrained to [min, max] range

// Field extraction
wire w_sign_x = i_x[7];
wire [3:0] w_exp_x = i_x[6:3];
wire [2:0] w_mant_x = i_x[2:0];

wire w_sign_min = i_min[7];
wire [3:0] w_exp_min = i_min[6:3];
wire [2:0] w_mant_min = i_min[2:0];

wire w_sign_max = i_max[7];
wire [3:0] w_exp_max = i_max[6:3];
wire [2:0] w_mant_max = i_max[2:0];

// NaN detection
wire w_x_is_nan = (w_exp_x == 4'hF) & (w_mant_x == 3'h7);
wire w_min_is_nan = (w_exp_min == 4'hF) & (w_mant_min == 3'h7);
wire w_max_is_nan = (w_exp_max == 4'hF) & (w_mant_max == 3'h7);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

// Magnitude for comparison
wire [6:0] w_mag_x = i_x[6:0];
wire [6:0] w_mag_min = i_min[6:0];
wire [6:0] w_mag_max = i_max[6:0];

// Comparison logic
function automatic logic fp_less_than(
    input logic [7:0] a,
    input logic [7:0] b
);
    logic a_sign, b_sign;
    logic [6:0] a_mag, b_mag;

    a_sign = a[7];
    b_sign = b[7];
    a_mag = a[6:0];
    b_mag = b[6:0];

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

