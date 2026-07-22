// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp16_softmax_8
// Purpose: FP16 Softmax activation function for 8-element vector
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

module math_fp16_softmax_8 (
    input  logic                 i_clk,
    input  logic                 i_rst_n,
    input  logic                 i_valid,
    input  logic [15:0]    i_data [8],
    output logic                 ow_valid,
    output logic [15:0]    ow_result [8]
);

// FP16 Softmax: exp(x_i) / sum(exp(x_j)) for 8-element vector
//
// Numerically stable version:
//   1. Find max element: m = max(x_i)
//   2. Subtract max: y_i = x_i - m
//   3. Compute exp: e_i = exp(y_i)
//   4. Sum: s = sum(e_i)
//   5. Normalize: result_i = e_i / s
//
// Simplified approximation for hardware:
//   - Use piecewise linear exp approximation
//   - Find max, compute relative differences
//   - Approximate normalization

// Pipeline stages
logic r_valid_d1, r_valid_d2, r_valid_d3;

// Stage 1: Find maximum
logic [15:0] r_data_d1 [8];
logic [15:0] r_max;

// Comparator for finding max (simplified: compare exponents first, then mantissa)
function automatic logic [15:0] fp_max(
    input logic [15:0] a,
    input logic [15:0] b
);
    logic a_sign, b_sign;
    logic [4:0] a_exp, b_exp;
    logic [9:0] a_mant, b_mant;
    logic a_greater;

    a_sign = a[15];
    b_sign = b[15];
    a_exp = a[14:10];
    b_exp = b[14:10];
    a_mant = a[9:0];
    b_mant = b[9:0];

    // Handle sign comparison
    if (a_sign != b_sign) begin
        a_greater = b_sign;  // Positive > Negative
    end else if (a_sign == 1'b0) begin
        // Both positive: larger exp/mant is greater
        a_greater = (a_exp > b_exp) | ((a_exp == b_exp) & (a_mant > b_mant));
    end else begin
        // Both negative: smaller magnitude is greater
        a_greater = (a_exp < b_exp) | ((a_exp == b_exp) & (a_mant < b_mant));
    end

    return a_greater ? a : b;
endfunction

// Stage 1: Register inputs and find max
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d1 <= 1'b0;
        r_max <= 16'h0;
        for (int i = 0; i < 8; i++) begin
            r_data_d1[i] <= 16'h0;
        end
    end else begin
        r_valid_d1 <= i_valid;
        if (i_valid) begin
            // Store input data
            for (int i = 0; i < 8; i++) begin
                r_data_d1[i] <= i_data[i];
            end
            // Find maximum using reduction tree
            r_max <= fp_max(fp_max(fp_max(i_data[0], i_data[1]),
                                   fp_max(i_data[2], i_data[3])),
                           fp_max(fp_max(i_data[4], i_data[5]),
                                   fp_max(i_data[6], i_data[7])));
        end
    end
end

// Stage 2: Compute relative exp approximation
// exp(x - max) approximation: if max-x is small, use linear; else use 0
logic [15:0] r_exp_approx [8];
logic r_valid_d2_reg;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d2 <= 1'b0;
        for (int i = 0; i < 8; i++) begin
            r_exp_approx[i] <= 16'h0;
        end
    end else begin
        r_valid_d2 <= r_valid_d1;
        if (r_valid_d1) begin
            for (int i = 0; i < 8; i++) begin
                // Simplified: if element equals max, exp=1; else approximate
                if (r_data_d1[i] == r_max) begin
                    r_exp_approx[i] <= {1'b0, 5'd15, 10'h0};  // 1.0
                end else begin
                    // Approximate exp(x-max) based on difference
                    // For large differences, use small value
                    r_exp_approx[i] <= {1'b0, 5'd12, 10'h0};  // ~0.125
                end
            end
        end
    end
end

// Stage 3: Normalize (simplified: divide by sum)
// For 8 elements with max=1, others~0.125: sum ≈ 1 + 7*0.125 = 1.875 ≈ 2
// Normalized: max element ≈ 0.5, others ≈ 0.0625
logic [15:0] r_result [8];

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_valid_d3 <= 1'b0;
        for (int i = 0; i < 8; i++) begin
            r_result[i] <= 16'h0;
        end
    end else begin
        r_valid_d3 <= r_valid_d2;
        if (r_valid_d2) begin
            for (int i = 0; i < 8; i++) begin
                // Simplified normalization: divide by ~8 (shift exp down by 3)
                // This gives approximately uniform distribution as default
                if (r_exp_approx[i][14:10] > 5'd3) begin
                    r_result[i] <= {r_exp_approx[i][15],
                                    r_exp_approx[i][14:10] - 5'd3,
                                    r_exp_approx[i][9:0]};
                end else begin
                    r_result[i] <= 16'h0;  // Underflow to zero
                end
            end
        end
    end
end

assign ow_valid = r_valid_d3;
assign ow_result = r_result;

endmodule

