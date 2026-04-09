// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_to_fp16
//
// Verifies lossless FP8_E5M2 -> FP16 upconversion properties:
//   - Sign preservation
//   - NaN propagation
//   - Infinity preservation (E5M2 has infinity)
//   - Zero preservation (including subnormal flush-to-zero)
//   - Exponent identity (E5M2 bias=15, FP16 bias=15, diff=0)
//   - Mantissa zero-extension correctness

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_to_fp16 (
    input logic clk
);

    (* anyconst *) logic [7:0] a;

    logic [15:0] result;
    logic        invalid;

    math_fp8_e5m2_to_fp16 dut (
        .i_a       (a),
        .ow_result (result),
        .ow_invalid(invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[7];
    wire [4:0]  exp_a  = a[6:2];
    wire [1:0]  mant_a = a[1:0];

    wire        sign_r = result[15];
    wire [4:0]  exp_r  = result[14:10];
    wire [9:0]  mant_r = result[9:0];

    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 2'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 2'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 2'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 2'h0);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_inf && !a_is_nan;

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 10'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 10'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 10'h0);

    // =========================================================================
    // Properties
    // =========================================================================
    always @(posedge clk) begin
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

    // Exponent: same bias (15), so exp unchanged
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_exp_identity: assert (exp_r == exp_a);
        end
    end

    // Mantissa: {mant_a[1:0], 8'b0}
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_mant_upper: assert (mant_r[9:8] == mant_a);
            p_mant_lower: assert (mant_r[7:0] == 8'h0);
        end
    end

    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_no_spurious_invalid: assert (!invalid);
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
