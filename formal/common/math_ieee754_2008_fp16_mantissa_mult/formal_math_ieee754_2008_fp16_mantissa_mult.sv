// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp16_mantissa_mult
//
// Verifies 11x11 mantissa multiplication (with implied leading 1):
//   - Product correctness (22-bit unsigned mul)
//   - Normalization detection (product[21])
//   - Mantissa extraction from correct positions
//   - Round/sticky bit extraction
//   - Implied leading 1 handling for normal vs subnormal (FTZ)

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp16_mantissa_mult (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [9:0] mant_a;
    (* anyconst *) logic [9:0] mant_b;
    (* anyconst *) logic       a_is_normal;
    (* anyconst *) logic       b_is_normal;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [21:0] product;
    logic        needs_norm;
    logic [9:0]  mant_out;
    logic        round_bit;
    logic        sticky_bit;

    math_ieee754_2008_fp16_mantissa_mult dut (
        .i_mant_a      (mant_a),
        .i_mant_b      (mant_b),
        .i_a_is_normal (a_is_normal),
        .i_b_is_normal (b_is_normal),
        .ow_product    (product),
        .ow_needs_norm (needs_norm),
        .ow_mant_out   (mant_out),
        .ow_round_bit  (round_bit),
        .ow_sticky_bit (sticky_bit)
    );

    // =========================================================================
    // Reference model
    // =========================================================================
    wire [10:0] ref_mant_a_ext = a_is_normal ? {1'b1, mant_a} : 11'h0;
    wire [10:0] ref_mant_b_ext = b_is_normal ? {1'b1, mant_b} : 11'h0;
    wire [21:0] ref_product = ref_mant_a_ext * ref_mant_b_ext;

    // =========================================================================
    // Property 1: Product matches reference
    // =========================================================================
    always @(posedge clk) begin
        p_product_correct: assert (product == ref_product);
    end

    // =========================================================================
    // Property 2: Normalization detection
    // =========================================================================
    always @(posedge clk) begin
        p_needs_norm: assert (needs_norm == product[21]);
    end

    // =========================================================================
    // Property 3: Mantissa output extraction
    // needs_norm: product[20:11], else: product[19:10]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_mant_norm: assert (mant_out == product[20:11]);
        end else begin
            p_mant_nonorm: assert (mant_out == product[19:10]);
        end
    end

    // =========================================================================
    // Property 4: Round bit extraction
    // needs_norm: product[10], else: product[9]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_round_norm: assert (round_bit == product[10]);
        end else begin
            p_round_nonorm: assert (round_bit == product[9]);
        end
    end

    // =========================================================================
    // Property 5: Sticky bit
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_sticky_norm: assert (sticky_bit == |product[9:0]);
        end else begin
            p_sticky_nonorm: assert (sticky_bit == |product[8:0]);
        end
    end

    // =========================================================================
    // Property 6: Both normal -> product >= 1.0 * 1.0 = 0x100 * 0x100 = 0x100000
    // With implied bits at position 10 * position 10, min product bit is at pos 20
    // Min: 0x400 * 0x400 = 0x100000 (2^20)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_min: assert (product >= 22'h100000);
        end
    end

    // =========================================================================
    // Property 7: Both normal -> product < 4.0 (max 0x7FF * 0x7FF = 0x3FF001)
    // Since product bit 21 not always set, must be < 2^22
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_max: assert (product <= 22'h3FF001);
        end
    end

    // =========================================================================
    // Property 8: When either input has implied 0 (subnormal/FTZ), product smaller
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal) begin
            p_not_normal_a: assert (product == 22'h0);
        end
        if (!b_is_normal) begin
            p_not_normal_b: assert (product == 22'h0);
        end
    end

    // =========================================================================
    // Property 9: Known vector: 1.0 * 1.0
    // mant=0, both normal -> ext = 0x400 * 0x400 = 0x100000
    // needs_norm=0, mant_out = product[19:10] = 0x000
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 10'd0 && mant_b == 10'd0 && a_is_normal && b_is_normal) begin
            p_one_times_one_product: assert (product == 22'h100000);
            p_one_times_one_no_norm: assert (!needs_norm);
            p_one_times_one_mant: assert (mant_out == 10'd0);
        end
    end

    // =========================================================================
    // Property 10: Known vector: 1.5 * 1.5
    // mant=0x200 (0.5), ext = 0x600, product = 0x600*0x600 = 0x240000
    // bit[21]=1 -> needs_norm, mant_out = product[20:11] = 0x080
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 10'h200 && mant_b == 10'h200 && a_is_normal && b_is_normal) begin
            p_1p5_squared_product: assert (product == 22'h240000);
            p_1p5_squared_norm: assert (needs_norm);
            p_1p5_squared_mant: assert (mant_out == 10'h080);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_needs_norm:   cover (needs_norm);
        c_no_norm:      cover (!needs_norm && a_is_normal && b_is_normal);
        c_zero_product: cover (product == 22'h0);
        c_round_bit:    cover (round_bit);
        c_sticky_bit:   cover (sticky_bit);
        c_both_normal:  cover (a_is_normal && b_is_normal);
    end

endmodule
