// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp16_to_fp32
//
// Verifies lossless FP16 -> FP32 upconversion properties:
//   - Sign preservation
//   - NaN propagation
//   - Infinity preservation
//   - Zero preservation (including subnormal flush-to-zero)
//   - Exponent bias adjustment (FP16 bias=15, FP32 bias=127, diff=112)
//   - Mantissa zero-extension correctness

`timescale 1ns / 1ps

module formal_math_fp16_to_fp32 (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [31:0] result;
    logic        invalid;

    math_fp16_to_fp32 dut (
        .i_a       (a),
        .ow_result (result),
        .ow_invalid(invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[15];
    wire [4:0]  exp_a  = a[14:10];
    wire [9:0]  mant_a = a[9:0];

    wire        sign_r = result[31];
    wire [7:0]  exp_r  = result[30:23];
    wire [22:0] mant_r = result[22:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 10'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 10'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 10'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 10'h0);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_inf && !a_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 23'h0);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 23'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 23'h0);

    // =========================================================================
    // Properties
    // =========================================================================
    always @(posedge clk) begin
        // Sign preservation
        p_sign_preserved: assert (sign_r == sign_a);
    end

    always @(posedge clk) begin
        if (a_is_nan) begin
            p_nan_out: assert (r_is_nan);
            p_nan_invalid: assert (invalid);
        end
    end

    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_preserved: assert (r_is_inf);
        end
    end

    always @(posedge clk) begin
        if (a_is_zero) begin
            p_zero_preserved: assert (r_is_zero);
        end
    end

    always @(posedge clk) begin
        if (a_is_subnorm) begin
            p_subnorm_ftz: assert (r_is_zero);
        end
    end

    // Exponent: FP16 exp + 112 = FP32 exp
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_exp_bias: assert (exp_r == ({3'b0, exp_a} + 8'd112));
        end
    end

    // Mantissa: {mant_a[9:0], 13'b0}
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_mant_upper: assert (mant_r[22:13] == mant_a);
            p_mant_lower: assert (mant_r[12:0] == 13'h0);
        end
    end

    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_no_spurious_invalid: assert (!invalid);
        end
    end

    // Known test vector: FP16 1.0 = 0x3C00 -> FP32 1.0 = 0x3F800000
    always @(posedge clk) begin
        if (a == 16'h3C00) begin
            p_one_to_one: assert (result == 32'h3F800000);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal: cover (a_is_normal && !invalid);
        c_zero: cover (a_is_zero);
        c_inf: cover (a_is_inf);
        c_nan: cover (a_is_nan);
        c_subnorm: cover (a_is_subnorm);
    end

endmodule
