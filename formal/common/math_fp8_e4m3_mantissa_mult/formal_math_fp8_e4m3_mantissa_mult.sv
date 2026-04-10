// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_mantissa_mult
//
// Verifies 4x4 mantissa multiplication with implied 1 handling:
//   - Product width and value correctness
//   - Normalization detection (needs_norm when product[7] set)
//   - Mantissa extraction from correct bit positions
//   - Round/sticky bit extraction
//   - Implied leading 1 handling for normal vs subnormal
//
// FP8 E4M3 mantissa: 3 bits + implied 1 = 4-bit extended mantissa
// Product: 4x4 -> 8-bit wide. Format: xx.xxxxxx (2 int bits, 6 frac bits)

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_mantissa_mult (
    input logic clk
);

    // =========================================================================
    // Free inputs (fully enumerable: 2^8 = 256 states)
    // =========================================================================
    (* anyconst *) logic [2:0] mant_a;
    (* anyconst *) logic [2:0] mant_b;
    (* anyconst *) logic       a_is_normal;
    (* anyconst *) logic       b_is_normal;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] product;
    logic       needs_norm;
    logic [2:0] mant_out;
    logic       round_bit;
    logic       sticky_bit;

    math_fp8_e4m3_mantissa_mult dut (
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
    // Reference model (matches DUT FTZ semantics: subnormal -> 0)
    // =========================================================================
    wire [3:0] ref_mant_a_ext = a_is_normal ? {1'b1, mant_a} : 4'h0;
    wire [3:0] ref_mant_b_ext = b_is_normal ? {1'b1, mant_b} : 4'h0;
    wire [7:0] ref_product = ref_mant_a_ext * ref_mant_b_ext;

    // =========================================================================
    // Property 1: Product matches reference multiplication
    // =========================================================================
    always @(posedge clk) begin
        p_product_correct: assert (product == ref_product);
    end

    // =========================================================================
    // Property 2: Normalization detection is correct
    // needs_norm when product bit 7 is set (product >= 2.0 in fixed point)
    // =========================================================================
    always @(posedge clk) begin
        p_needs_norm: assert (needs_norm == product[7]);
    end

    // =========================================================================
    // Property 3: Mantissa output extracted from correct positions
    // If needs_norm: product[6:4] (shift right by 1)
    // Else: product[5:3]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_mant_norm: assert (mant_out == product[6:4]);
        end else begin
            p_mant_nonorm: assert (mant_out == product[5:3]);
        end
    end

    // =========================================================================
    // Property 4: Round bit extracted from correct position
    // If needs_norm: product[3], else: product[2]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_round_norm: assert (round_bit == product[3]);
        end else begin
            p_round_nonorm: assert (round_bit == product[2]);
        end
    end

    // =========================================================================
    // Property 5: Sticky bit (OR of remaining bits)
    // If needs_norm: |product[2:0]
    // Else: |product[1:0]
    // =========================================================================
    always @(posedge clk) begin
        if (needs_norm) begin
            p_sticky_norm: assert (sticky_bit == |product[2:0]);
        end else begin
            p_sticky_nonorm: assert (sticky_bit == |product[1:0]);
        end
    end

    // =========================================================================
    // Property 6: Both inputs normal -> product >= 1.0*1.0
    // Ext: 1.xxx = 0x8..0xF. Min product = 8*8 = 64
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_min: assert (product >= 8'd64);
        end
    end

    // =========================================================================
    // Property 7: Both inputs normal -> product < 256
    // Max ext = 0xF, max product = 15*15 = 225 < 256 (bit 8 never set)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal) begin
            p_normal_product_max: assert (product <= 8'd225);
        end
    end

    // =========================================================================
    // Property 8: Subnormal/FTZ input -> product is zero
    // DUT uses FTZ semantics: if input not normal, extended mantissa = 0
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal) begin
            p_subnorm_a_zero: assert (product == 8'd0);
        end
        if (!b_is_normal) begin
            p_subnorm_b_zero: assert (product == 8'd0);
        end
    end

    // =========================================================================
    // Property 9: Any FTZ operand -> product output is zero
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_normal || !b_is_normal) begin
            p_ftz_product_zero: assert (product == 8'd0);
        end
    end

    // =========================================================================
    // Property 10: Known vector: 1.0 * 1.0
    // mant_a=0, mant_b=0, both normal -> ext = 0x8 * 0x8 = 0x40
    // product = 64 = 0x40, bit[7]=0, bit[6]=1
    // needs_norm = 0, mant_out = product[5:3] = 0x0
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 3'd0 && mant_b == 3'd0 && a_is_normal && b_is_normal) begin
            p_one_times_one_product: assert (product == 8'h40);
            p_one_times_one_no_norm: assert (!needs_norm);
            p_one_times_one_mant: assert (mant_out == 3'd0);
        end
    end

    // =========================================================================
    // Property 11: Known vector: 1.5 * 1.5
    // mant = 3'b100 = 0x4, ext = 0xC, product = 0xC * 0xC = 0x90
    // bit[7]=1 -> needs_norm, mant_out = product[6:4] = 3'b001
    // =========================================================================
    always @(posedge clk) begin
        if (mant_a == 3'h4 && mant_b == 3'h4 && a_is_normal && b_is_normal) begin
            p_1p5_squared_product: assert (product == 8'h90);
            p_1p5_squared_norm: assert (needs_norm);
            p_1p5_squared_mant: assert (mant_out == 3'h1);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_needs_norm:   cover (needs_norm);
        c_no_norm:      cover (!needs_norm && a_is_normal && b_is_normal);
        c_zero_product: cover (product == 8'd0);
        c_round_bit:    cover (round_bit);
        c_sticky_bit:   cover (sticky_bit);
        c_both_normal:  cover (a_is_normal && b_is_normal);
        c_subnorm_a:    cover (!a_is_normal && b_is_normal);
    end

endmodule
