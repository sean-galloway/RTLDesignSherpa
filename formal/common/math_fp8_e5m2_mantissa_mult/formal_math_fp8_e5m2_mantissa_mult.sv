// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_mantissa_mult
//
// Verifies 3x3 mantissa multiplication with implied 1 handling:
//   - Product width and value correctness
//   - Normalization detection (needs_norm when product[5] set)
//   - Mantissa extraction from correct bit positions
//   - Round/sticky bit extraction
//   - Implied leading 1 handling for normal vs subnormal
//
// FP8 E5M2 mantissa: 2 bits + implied 1 = 3-bit extended mantissa
// Product: 3x3 -> 6-bit wide. Format: xx.xxxx (2 int bits, 4 frac bits)
// Note: when either input is NOT normal (subnormal/zero), the DUT forces
// the extended mantissa to zero (FTZ mode).

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_mantissa_mult (
    input logic clk
);

    // =========================================================================
    // Free inputs (fully enumerable: 2^6 = 64 states)
    // =========================================================================
    (* anyconst *) logic [1:0] mant_a;
    (* anyconst *) logic [1:0] mant_b;
    (* anyconst *) logic       a_is_normal;
    (* anyconst *) logic       b_is_normal;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [5:0] product;
    logic       needs_norm;
    logic [1:0] mant_out;
    logic       round_bit;
    logic       sticky_bit;

    math_fp8_e5m2_mantissa_mult dut (
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
    // DUT forces the extended mantissa to zero when not normal (FTZ)
    // =========================================================================
    wire [2:0] ref_mant_a_ext = a_is_normal ? {1'b1, mant_a} : 3'h0;
    wire [2:0] ref_mant_b_ext = b_is_normal ? {1'b1, mant_b} : 3'h0;
    wire [5:0] ref_product = ref_mant_a_ext * ref_mant_b_ext;

    // =========================================================================
    // Property 1: Product matches reference multiplication
    // =========================================================================
    always @(posedge clk) begin
        p_product_correct: assert (product == ref_product);
    end

    // =========================================================================
    // Property 2: Normalization detection is correct
    // needs_norm when product bit 5 is set (product >= 2.0 in fixed point)
    // =========================================================================
    always @(posedge clk) begin
        p_needs_norm: assert (needs_norm == product[5]);
    end

    // =========================================================================
    // Property 3: Mantissa output extracted from correct positions
    // If needs_norm: product[4:3] (shift right by 1)
    // Else: product[3:2]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_mant_norm: assert (mant_out == product[4:3]);
        end else begin
            p_mant_nonorm: assert (mant_out == product[3:2]);
        end
    end

    // =========================================================================
    // Property 4: Round bit extracted from correct position
    // If needs_norm: product[2], else: product[1]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_round_norm: assert (round_bit == product[2]);
        end else begin
            p_round_nonorm: assert (round_bit == product[1]);
        end
    end

    // =========================================================================
    // Property 5: Sticky bit (OR of remaining bits)
    // If needs_norm: |product[1:0]
    // Else: product[0]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_sticky_norm: assert (sticky_bit == |product[1:0]);
        end else begin
            p_sticky_nonorm: assert (sticky_bit == product[0]);
        end
    end

    // =========================================================================
    // Property 6: Both inputs normal -> product >= 1.0*1.0
    // Ext: 1.xx = 4..7. Min product = 4*4 = 16
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_min: assert (product >= 6'd16);
        end
    end

    // =========================================================================
    // Property 7: Both inputs normal -> product <= 49 (max 7*7)
    // Max ext = 0x7, max product = 7*7 = 49. Bit 6 never set (product is 6 bits).
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_max: assert (product <= 6'd49);
        end
    end

    // =========================================================================
    // Property 8: Subnormal/non-normal input -> product is zero
    // DUT forces ext to 0 when not normal, so product = 0.
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal) begin
            p_subnorm_a_zero: assert (product == 6'd0);
        end
        if (!b_is_normal) begin
            p_subnorm_b_zero: assert (product == 6'd0);
        end
    end

    // =========================================================================
    // Property 9: Known vector: 1.0 * 1.0
    // mant_a=0, mant_b=0, both normal -> ext = 0x4 * 0x4 = 0x10
    // product = 16 = 0x10, bit[5]=0, bit[4]=1
    // needs_norm = 0, mant_out = product[3:2] = 2'b00
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 2'd0 && mant_b == 2'd0 && a_is_normal && b_is_normal) begin
            p_one_times_one_product: assert (product == 6'h10);
            p_one_times_one_no_norm: assert (!needs_norm);
            p_one_times_one_mant: assert (mant_out == 2'd0);
        end
    end

    // =========================================================================
    // Property 10: Known vector: 1.5 * 1.5
    // mant = 2'b10 = 0x2, ext = 0x6, product = 6*6 = 36 = 0x24
    // bit[5]=1 -> needs_norm, mant_out = product[4:3] = 2'b00 (0x24 = 100100)
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 2'h2 && mant_b == 2'h2 && a_is_normal && b_is_normal) begin
            p_1p5_squared_product: assert (product == 6'h24);
            p_1p5_squared_norm: assert (needs_norm);
            p_1p5_squared_mant: assert (mant_out == 2'h0);
        end
    end

    // =========================================================================
    // Property 11: Known vector: 1.75 * 1.75
    // mant = 2'b11 = 0x3, ext = 0x7, product = 7*7 = 49 = 0x31
    // bit[5]=1 -> needs_norm, mant_out = product[4:3] = 2'b10 (0x31 = 110001)
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 2'h3 && mant_b == 2'h3 && a_is_normal && b_is_normal) begin
            p_1p75_squared_product: assert (product == 6'h31);
            p_1p75_squared_norm: assert (needs_norm);
            p_1p75_squared_mant: assert (mant_out == 2'h2);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_needs_norm:   cover (needs_norm);
        c_no_norm:      cover (!needs_norm && a_is_normal && b_is_normal);
        c_zero_product: cover (product == 6'd0);
        c_round_bit:    cover (round_bit);
        c_sticky_bit:   cover (sticky_bit);
        c_both_normal:  cover (a_is_normal && b_is_normal);
        c_not_normal_a: cover (!a_is_normal && b_is_normal);
    end

endmodule
