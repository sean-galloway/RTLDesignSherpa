// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_sigmoid
//
// Verifies:
//   - NaN passthrough
//   - Sign handling
//   - Output in valid FP range
//   - Known vector: sigmoid(0) ~ 0.5

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_sigmoid (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [7:0] a;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] result;

    math_fp8_e5m2_sigmoid dut (
        .i_a       (a),
        .ow_result (result)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[7];
    wire [4:0] exp    = a[6:2];
    wire [1:0] mant   = a[1:0];

    wire        sign_r = result[7];
    wire [4:0] exp_r  = result[6:2];
    wire [1:0] mant_r = result[1:0];

    // Special value classification
    wire a_is_zero     = (exp == 5'd0) && (mant == 2'd0);
    wire a_is_subnormal = (exp == 5'd0) && (mant != 2'd0);
    wire a_is_nan      = (exp == 5'h1F) && (mant != 2'h0);
    wire a_is_inf      = (exp == 5'h1F) && (mant == 2'h0);

    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 2'h0);

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

    // Property: sigmoid(+0) = 0.5
    always @(posedge clk) begin
        if (a == 8'h00) begin
            p_sigmoid_zero: assert (result == 8'h38);
        end
    end

    // Property: sigmoid(+inf) = 1.0
    always @(posedge clk) begin
        if (!sign_a && a_is_inf) begin
            p_pos_inf_gives_one: assert (result == 8'h3C);
        end
    end

    // Property: sigmoid(-inf) = 0
    always @(posedge clk) begin
        if (sign_a && a_is_inf) begin
            p_neg_inf_gives_zero: assert (result == 8'h00);
        end
    end

    // Property: output is non-negative (sign bit = 0) for non-NaN
    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_output_non_negative: assert (result[7] == 1'b0);
        end
    end

    // Property: output <= 1.0 for non-NaN
    // For sigmoid, output is always in [0, 1]
    always @(posedge clk) begin
        if (!a_is_nan && !r_is_nan) begin
            p_output_le_one: assert (result <= 8'h3C);
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
