// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp16_tanh
//
// Verifies:
//   - NaN passthrough
//   - Sign handling
//   - Output in valid FP range
//   - Known vector: tanh(0) = 0

`timescale 1ns / 1ps

module formal_math_fp16_tanh (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] result;

    math_fp16_tanh dut (
        .i_a       (a),
        .ow_result (result)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[15];
    wire [4:0] exp    = a[14:10];
    wire [9:0] mant   = a[9:0];

    wire        sign_r = result[15];
    wire [4:0] exp_r  = result[14:10];
    wire [9:0] mant_r = result[9:0];

    // Special value classification
    wire a_is_zero     = (exp == 5'd0) && (mant == 10'd0);
    wire a_is_subnormal = (exp == 5'd0) && (mant != 10'd0);
    wire a_is_nan      = (exp == 5'h1F) && (mant != 10'h0);
    wire a_is_inf      = (exp == 5'h1F) && (mant == 10'h0);

    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 10'h0);

    // =========================================================================
    // Property: NaN input produces NaN output (passthrough)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_nan) begin
            p_nan_passthrough: assert (result == a);
        end
    end

    // =========================================================================
    // Property: Non-NaN input must not produce NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_no_spurious_nan: assert (!r_is_nan);
        end
    end

    // Property: tanh(+0) = +0 (or input itself since tanh(x)~x for small x)
    always @(posedge clk) begin
        if (a == 16'h0000) begin
            p_tanh_zero: assert (result == 16'h0000);
        end
    end

    // Property: tanh(+inf) = +1.0
    always @(posedge clk) begin
        if (!sign_a && a_is_inf) begin
            p_pos_inf_gives_pos_one: assert (result == 16'h3C00);
        end
    end

    // Property: tanh(-inf) = -1.0
    always @(posedge clk) begin
        if (sign_a && a_is_inf) begin
            p_neg_inf_gives_neg_one: assert (result == 16'hBC00);
        end
    end

    // Property: |tanh(x)| <= 1.0 for non-NaN
    // Check magnitude (clear sign bit) <= 1.0 encoding (clear sign bit)
    always @(posedge clk) begin
        if (!a_is_nan && !r_is_nan) begin
            p_output_le_one: assert (result[14:0] <= 15'h3C00);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_input: cover (!a_is_nan && !a_is_inf && !a_is_zero && !a_is_subnormal);
        c_zero_input:   cover (a_is_zero);
        c_nan_input:    cover (a_is_nan);
        c_positive:     cover (!sign_a && !a_is_nan && !a_is_zero);
        c_negative:     cover (sign_a && !a_is_nan && !a_is_zero);
    end

endmodule
