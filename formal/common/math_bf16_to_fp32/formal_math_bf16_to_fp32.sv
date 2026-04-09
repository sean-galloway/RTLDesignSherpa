// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_to_fp32
//
// Verifies lossless BF16 -> FP32 upconversion properties:
//   - Sign preservation
//   - NaN propagation (with quiet NaN canonical form)
//   - Infinity preservation
//   - Zero preservation (including subnormal flush-to-zero)
//   - Exponent bias correctness (BF16 bias=127, FP32 bias=127, same)
//   - Mantissa zero-extension correctness
//   - Invalid flag consistency

`timescale 1ns / 1ps

module formal_math_bf16_to_fp32 (
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

    math_bf16_to_fp32 dut (
        .i_a       (a),
        .ow_result (result),
        .ow_invalid(invalid)
    );

    // =========================================================================
    // BF16 field extraction
    // =========================================================================
    wire        sign_a = a[15];
    wire [7:0]  exp_a  = a[14:7];
    wire [6:0]  mant_a = a[6:0];

    // FP32 field extraction
    wire        sign_r = result[31];
    wire [7:0]  exp_r  = result[30:23];
    wire [22:0] mant_r = result[22:0];

    // Special value classification - input
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 7'h00);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 7'h00);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 7'h00);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 7'h00);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_inf && !a_is_nan;

    // Special value classification - output
    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 23'h0);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 23'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 23'h0);

    // =========================================================================
    // Property 1: Sign preservation
    // =========================================================================
    always @(posedge clk) begin
        p_sign_preserved: assert (sign_r == sign_a);
    end

    // =========================================================================
    // Property 2: NaN propagation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_nan) begin
            p_nan_out: assert (r_is_nan);
            p_nan_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Infinity preservation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_preserved: assert (r_is_inf);
            p_inf_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 4: Zero preservation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_zero) begin
            p_zero_preserved: assert (r_is_zero);
            p_zero_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 5: Subnormal flush to zero
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm) begin
            p_subnorm_ftz: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 6: Normal value - exponent identity (same bias)
    // BF16 exp bias = 127, FP32 exp bias = 127, so exp unchanged
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_exp_identity: assert (exp_r == exp_a);
        end
    end

    // =========================================================================
    // Property 7: Normal value - mantissa zero-extension
    // BF16 has 7-bit mantissa, FP32 has 23-bit mantissa
    // Result mantissa = {mant_a, 16'b0}
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal) begin
            p_mant_upper: assert (mant_r[22:16] == mant_a);
            p_mant_lower: assert (mant_r[15:0] == 16'h0);
        end
    end

    // =========================================================================
    // Property 8: Invalid flag only set for NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (a_is_nan);
        end
    end

    // =========================================================================
    // Property 9: Non-NaN input produces no invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_no_spurious_invalid: assert (!invalid);
        end
    end

    // =========================================================================
    // Property 10: Known test vector: BF16 1.0 -> FP32 1.0
    // BF16 1.0 = 0x3F80, FP32 1.0 = 0x3F800000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3F80) begin
            p_one_to_one: assert (result == 32'h3F800000);
        end
    end

    // =========================================================================
    // Property 11: Known test vector: BF16 -2.0 -> FP32 -2.0
    // BF16 -2.0 = 0xC000, FP32 -2.0 = 0xC0000000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'hC000) begin
            p_neg2_to_neg2: assert (result == 32'hC0000000);
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
