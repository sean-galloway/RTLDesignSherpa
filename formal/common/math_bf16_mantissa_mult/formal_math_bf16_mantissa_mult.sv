// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_mantissa_mult
//
// Verifies 8x8 mantissa multiplication with implied 1 handling:
//   - Product width and value correctness
//   - Normalization detection (needs_norm when product[15] set)
//   - Mantissa extraction from correct bit positions
//   - Round/sticky bit extraction
//   - Implied leading 1 handling for normal vs subnormal

`timescale 1ns / 1ps

module formal_math_bf16_mantissa_mult (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [6:0] mant_a;
    (* anyconst *) logic [6:0] mant_b;
    (* anyconst *) logic       a_is_normal;
    (* anyconst *) logic       b_is_normal;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] product;
    logic        needs_norm;
    logic [6:0]  mant_out;
    logic        round_bit;
    logic        sticky_bit;

    math_bf16_mantissa_mult dut (
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
    wire [7:0] ref_mant_a_ext = {a_is_normal, mant_a};
    wire [7:0] ref_mant_b_ext = {b_is_normal, mant_b};
    wire [15:0] ref_product = ref_mant_a_ext * ref_mant_b_ext;

    // =========================================================================
    // Property 1: Product matches reference multiplication
    // =========================================================================
    always @(posedge clk) begin
        p_product_correct: assert (product == ref_product);
    end

    // =========================================================================
    // Property 2: Normalization detection is correct
    // needs_norm when product bit 15 is set (product >= 2.0 in fixed point)
    // =========================================================================
    always @(posedge clk) begin
        p_needs_norm: assert (needs_norm == product[15]);
    end

    // =========================================================================
    // Property 3: Mantissa output extracted from correct positions
    // If needs_norm: product[14:8], else: product[13:7]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_mant_norm: assert (mant_out == product[14:8]);
        end else begin
            p_mant_nonorm: assert (mant_out == product[13:7]);
        end
    end

    // =========================================================================
    // Property 4: Round bit extracted from correct position
    // If needs_norm: product[6], else: product[5]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_round_norm: assert (round_bit == product[6]);
        end else begin
            p_round_nonorm: assert (round_bit == product[5]);
        end
    end

    // =========================================================================
    // Property 5: Sticky bit includes guard and remaining bits
    // If needs_norm: guard=product[7], sticky=|product[5:0]
    //   -> sticky_bit = guard | |product[5:0]
    // If not: guard=product[6], sticky=|product[4:0]
    //   -> sticky_bit = guard | |product[4:0]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_sticky_norm: assert (sticky_bit == (product[7] | (|product[5:0])));
        end else begin
            p_sticky_nonorm: assert (sticky_bit == (product[6] | (|product[4:0])));
        end
    end

    // =========================================================================
    // Property 6: When both inputs are normal (implied 1), product >= 1.0*1.0
    // Product of two normals: (1.x * 1.y) >= 1.0, so product >= 128*128 = 16384
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_min: assert (product >= 16'd16384);
        end
    end

    // =========================================================================
    // Property 7: When both inputs are normal, product < 4.0
    // Max: 1.1111111 * 1.1111111 < 4.0, so product < 256*256 = 65536
    // Actually max is 255*255 = 65025 < 65536, and bit 16 is never set
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_max: assert (product <= 16'd65025);
        end
    end

    // =========================================================================
    // Property 8: When either input has implied 0 (subnormal/zero),
    // product is smaller
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal) begin
            // Without implied 1, max mant_a = 127, so max product = 127*255 = 32385
            p_subnorm_a_bound: assert (product <= 16'd32385);
        end
        if (!b_is_normal) begin
            p_subnorm_b_bound: assert (product <= 16'd32385);
        end
    end

    // =========================================================================
    // Property 9: Both inputs zero mantissa with no implied 1 -> product = 0
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal && mant_a == 7'd0) begin
            p_zero_a_product: assert (product == 16'd0);
        end
        if (!b_is_normal && mant_b == 7'd0) begin
            p_zero_b_product: assert (product == 16'd0);
        end
    end

    // =========================================================================
    // Property 10: Known vector: 1.0 * 1.0
    // mant_a=0, mant_b=0, both normal -> ext = 0x80 * 0x80 = 0x4000
    // product = 16384 = 0x4000, bit[15]=0, bit[14]=1
    // needs_norm = 0, mant_out = product[13:7] = 0x00
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 7'd0 && mant_b == 7'd0 && a_is_normal && b_is_normal) begin
            p_one_times_one_product: assert (product == 16'h4000);
            p_one_times_one_no_norm: assert (!needs_norm);
            p_one_times_one_mant: assert (mant_out == 7'd0);
        end
    end

    // =========================================================================
    // Property 11: Known vector: 1.5 * 1.5
    // mant = 0x40 (0.5), ext = 0xC0, product = 0xC0 * 0xC0 = 0x9000
    // bit[15]=1 -> needs_norm, mant_out = product[14:8] = 0x10
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 7'h40 && mant_b == 7'h40 && a_is_normal && b_is_normal) begin
            p_1p5_squared_product: assert (product == 16'h9000);
            p_1p5_squared_norm: assert (needs_norm);
            p_1p5_squared_mant: assert (mant_out == 7'h10);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_needs_norm:   cover (needs_norm);
        c_no_norm:      cover (!needs_norm && a_is_normal && b_is_normal);
        c_zero_product: cover (product == 16'd0);
        c_round_bit:    cover (round_bit);
        c_sticky_bit:   cover (sticky_bit);
        c_both_normal:  cover (a_is_normal && b_is_normal);
        c_subnorm_a:    cover (!a_is_normal && b_is_normal);
    end

endmodule
