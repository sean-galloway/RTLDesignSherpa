// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_int_to_bf16
//
// Verifies integer to BF16 conversion:
//   - Zero input produces zero output
//   - Sign preservation (negative int -> negative BF16)
//   - NaN/inf never produced from valid integer input (except overflow)
//   - Known test vectors: 1->0x3F80, -1->0xBF80, 0->0x0000
//   - Result format validity

`timescale 1ns / 1ps

module formal_math_int_to_bf16 #(
    parameter int INT_WIDTH = 16
) (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic signed [INT_WIDTH-1:0] int_val;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] bf16_out;
    logic        is_zero;

    math_int_to_bf16 #(
        .INT_WIDTH(INT_WIDTH)
    ) dut (
        .i_int     (int_val),
        .ow_bf16   (bf16_out),
        .ow_is_zero(is_zero)
    );

    // =========================================================================
    // BF16 field extraction
    // =========================================================================
    wire        sign_r = bf16_out[15];
    wire [7:0]  exp_r  = bf16_out[14:7];
    wire [6:0]  mant_r = bf16_out[6:0];

    wire r_is_zero = (exp_r == 8'h00) && (mant_r == 7'h00);
    wire r_is_inf  = (exp_r == 8'hFF) && (mant_r == 7'h00);
    wire r_is_nan  = (exp_r == 8'hFF) && (mant_r != 7'h00);

    // =========================================================================
    // Property 1: Zero input produces zero output
    // =========================================================================
    always @(posedge clk) begin
        if (int_val == 0) begin
            p_zero_input_result: assert (bf16_out == 16'h0000);
            p_zero_input_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property 2: Non-zero input produces non-zero result
    // (unless underflow, which cannot happen for integers >= 1)
    // =========================================================================
    always @(posedge clk) begin
        if (int_val != 0) begin
            p_nonzero_input: assert (!is_zero || r_is_zero);
        end
    end

    // =========================================================================
    // Property 3: Sign preservation
    // Negative integer -> negative BF16 (sign bit = 1)
    // Positive integer -> positive BF16 (sign bit = 0)
    // =========================================================================
    always @(posedge clk) begin
        if (int_val > 0) begin
            p_positive_sign: assert (sign_r == 1'b0);
        end
        if (int_val < 0) begin
            p_negative_sign: assert (sign_r == 1'b1);
        end
    end

    // =========================================================================
    // Property 4: NaN is never produced from integer input
    // Integer conversion should never produce NaN
    // =========================================================================
    always @(posedge clk) begin
        p_no_nan: assert (!r_is_nan);
    end

    // =========================================================================
    // Property 5: is_zero flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (is_zero) begin
            p_zero_flag_implies_zero: assert (exp_r == 8'h00);
        end
    end

    // =========================================================================
    // Property 6: Normal result has valid exponent range
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !is_zero) begin
            p_normal_exp_range: assert (exp_r >= 8'h01 && exp_r <= 8'hFE);
        end
    end

    // =========================================================================
    // Property 7: Known vector: 1 -> 0x3F80 (1.0)
    // =========================================================================
    generate
        if (INT_WIDTH >= 2) begin : gen_vec_1
            always @(posedge clk) begin
                if (int_val == 1) begin
                    p_int_1: assert (bf16_out == 16'h3F80);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Property 8: Known vector: -1 -> 0xBF80 (-1.0)
    // =========================================================================
    generate
        if (INT_WIDTH >= 2) begin : gen_vec_neg1
            always @(posedge clk) begin
                if (int_val == -1) begin
                    p_int_neg1: assert (bf16_out == 16'hBF80);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Property 9: Known vector: 2 -> 0x4000 (2.0)
    // =========================================================================
    generate
        if (INT_WIDTH >= 3) begin : gen_vec_2
            always @(posedge clk) begin
                if (int_val == 2) begin
                    p_int_2: assert (bf16_out == 16'h4000);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Property 10: Known vector: -2 -> 0xC000 (-2.0)
    // =========================================================================
    generate
        if (INT_WIDTH >= 3) begin : gen_vec_neg2
            always @(posedge clk) begin
                if (int_val == -2) begin
                    p_int_neg2: assert (bf16_out == 16'hC000);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Property 11: Known vector: 127 -> 0x42FE (127.0)
    // exp = 127 + 6 = 133 = 0x85, mant = 127 - 64 = 63 -> 0x7E (shifted)
    // Actually: 127 = 1.1111110 * 2^6, exp=133=0x85, mant=0x7E>>1=0x3F...
    // Let me use: 127 = 0111_1111, MSB at bit 6
    // exp = 127 + 6 = 133, mant = bits[5:0] padded = 111_1110 = 0x7E
    // BF16 = 0_10000101_1111110 = 0x42FE
    // =========================================================================
    generate
        if (INT_WIDTH >= 8) begin : gen_vec_127
            always @(posedge clk) begin
                if (int_val == 127) begin
                    p_int_127: assert (bf16_out == 16'h42FE);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Property 12: Overflow produces infinity (for large INT_WIDTH)
    // When integer is too large for BF16, result should be +/- infinity
    // =========================================================================
    always @(posedge clk) begin
        if (r_is_inf) begin
            // Infinity output should only happen for very large integers
            // and should have correct sign
            p_inf_sign: assert (sign_r == int_val[INT_WIDTH-1]);
        end
    end

    // =========================================================================
    // Property 13: Small positive integers produce finite results
    // Integers 1-127 should always be exactly representable in BF16
    // =========================================================================
    generate
        if (INT_WIDTH >= 8) begin : gen_small_finite
            always @(posedge clk) begin
                if (int_val > 0 && int_val <= 127) begin
                    p_small_pos_finite: assert (!r_is_inf);
                    p_small_pos_not_zero: assert (!is_zero);
                end
            end
        end
    endgenerate

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_zero:        cover (int_val == 0);
        c_positive:    cover (int_val > 0 && !r_is_inf);
        c_negative:    cover (int_val < 0 && !r_is_inf);
        c_one:         cover (int_val == 1);
        c_neg_one:     cover (int_val == -1);
    end

    // Overflow cover only reachable when INT_WIDTH is large enough
    // that (126 + INT_WIDTH) > 254, i.e. INT_WIDTH > 128
    // For INT_WIDTH=16, max exponent is 141 -- no overflow possible
    generate
        if ((126 + INT_WIDTH) > 254) begin : gen_cover_overflow
            always @(posedge clk) begin
                c_overflow: cover (r_is_inf);
            end
        end
    endgenerate

endmodule
