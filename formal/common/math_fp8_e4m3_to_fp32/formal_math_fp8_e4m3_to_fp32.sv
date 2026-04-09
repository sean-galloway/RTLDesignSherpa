// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_to_fp32
//
// Verifies lossless FP8_E4M3 -> FP32 upconversion properties:
//   - Sign preservation
//   - NaN propagation (E4M3 NaN: exp=15, mant=7)
//   - FP8_E4M3 has no infinity representation
//   - Zero preservation (including subnormal flush-to-zero)
//   - Exponent bias adjustment (E4M3 bias=7, FP32 bias=127, diff=120)
//   - Mantissa zero-extension correctness

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_to_fp32 (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [7:0] a;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [31:0] result;
    logic        invalid;

    math_fp8_e4m3_to_fp32 dut (
        .i_a       (a),
        .ow_result (result),
        .ow_invalid(invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[7];
    wire [3:0]  exp_a  = a[6:3];
    wire [2:0]  mant_a = a[2:0];

    wire        sign_r = result[31];
    wire [7:0]  exp_r  = result[30:23];
    wire [22:0] mant_r = result[22:0];

    // FP8_E4M3: NaN is exp=0xF, mant=0x7 (only one NaN encoding)
    // FP8_E4M3 has NO infinity representation
    wire a_is_zero     = (exp_a == 4'h0) && (mant_a == 3'h0);
    wire a_is_subnorm  = (exp_a == 4'h0) && (mant_a != 3'h0);
    wire a_is_nan      = (exp_a == 4'hF) && (mant_a == 3'h7);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 23'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 23'h0);

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
        if (a_is_zero) begin
            p_zero_preserved: assert (r_is_zero);
        end
    end

    always @(posedge clk) begin
        if (a_is_subnorm) begin
            p_subnorm_ftz: assert (r_is_zero);
        end
    end

    // Exponent: E4M3 exp + 120 = FP32 exp
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_exp_bias: assert (exp_r == ({4'b0, exp_a} + 8'd120));
        end
    end

    // Mantissa: {mant_a[2:0], 20'b0}
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_mant_upper: assert (mant_r[22:20] == mant_a);
            p_mant_lower: assert (mant_r[19:0] == 20'h0);
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
        c_nan: cover (a_is_nan);
        c_subnorm: cover (a_is_subnorm);
    end

endmodule
