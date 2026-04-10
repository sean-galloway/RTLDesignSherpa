// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_adder
//
// Verifies structural FP8 E5M2 addition properties:
//   - Identity: a + 0 = a
//   - Additive inverse: a + (-a) = 0
//   - NaN propagation
//   - Infinity handling (inf + x, inf - inf)
//   - Known test vectors
//   - Flag consistency
//
// FP8 E5M2 format: [7]=sign, [6:2]=exp (bias=15), [1:0]=mant
// Inf: exp=31, mant=0
// NaN: exp=31, mant!=0

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs (8-bit each, fully enumerable: 2^16 = 65536 states)
    // =========================================================================
    (* anyconst *) logic [7:0] a;
    (* anyconst *) logic [7:0] b;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] result;
    logic       overflow, underflow, invalid;

    math_fp8_e5m2_adder dut (
        .i_a         (a),
        .i_b         (b),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP8 E5M2 field extraction
    // =========================================================================
    wire       sign_a = a[7];
    wire [4:0] exp_a  = a[6:2];
    wire [1:0] mant_a = a[1:0];

    wire       sign_b = b[7];
    wire [4:0] exp_b  = b[6:2];
    wire [1:0] mant_b = b[1:0];

    wire       sign_r = result[7];
    wire [4:0] exp_r  = result[6:2];
    wire [1:0] mant_r = result[1:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 2'h0);
    wire b_is_zero     = (exp_b == 5'h00) && (mant_b == 2'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 2'h0);
    wire b_is_subnorm  = (exp_b == 5'h00) && (mant_b != 2'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 2'h0);
    wire b_is_inf      = (exp_b == 5'h1F) && (mant_b == 2'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 2'h0);
    wire b_is_nan      = (exp_b == 5'h1F) && (mant_b != 2'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 2'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 2'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 2'h0);

    wire any_nan       = a_is_nan || b_is_nan;
    wire inf_minus_inf = a_is_inf && b_is_inf && (sign_a != sign_b);

    // Negation of b: flip sign bit only
    wire [7:0] neg_b = {~b[7], b[6:0]};

    // =========================================================================
    // Property 1: NaN propagation
    // Any NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 2: Infinity minus infinity = NaN
    // inf + (-inf) is an invalid operation
    // =========================================================================
    always @(posedge clk) begin
        if (inf_minus_inf && !any_nan) begin
            p_inf_minus_inf_nan: assert (r_is_nan);
            p_inf_minus_inf_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Identity -- a + (+0) = a for normal numbers
    // +0 = 8'h00
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == 8'h00) begin
            p_add_pos_zero: assert (result == a);
        end
    end

    // =========================================================================
    // Property 4: Identity -- (+0) + b = b for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_normal && a == 8'h00) begin
            p_zero_plus_b: assert (result == b);
        end
    end

    // =========================================================================
    // Property 5: Additive inverse -- a + (-a) = +0 for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == neg_b && a[6:0] == b[6:0] && sign_a != sign_b) begin
            p_additive_inverse: assert (result == 8'h00);
        end
    end

    // =========================================================================
    // Property 6: Infinity + normal = infinity (preserving sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && !b_is_inf && !b_is_nan) begin
            p_inf_plus_normal: assert (r_is_inf);
            p_inf_plus_normal_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 7: normal + infinity = infinity (preserving sign)
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_inf && !a_is_inf && !a_is_nan) begin
            p_normal_plus_inf: assert (r_is_inf);
            p_normal_plus_inf_sign: assert (sign_r == sign_b);
        end
    end

    // =========================================================================
    // Property 8: inf + inf (same sign) = inf (same sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf && sign_a == sign_b) begin
            p_inf_plus_inf: assert (r_is_inf);
            p_inf_plus_inf_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 9: Both inputs zero
    // 0 + 0 = 0
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_eff_zero && !any_nan) begin
            p_both_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 10: Known test vector: 1.0 + 1.0 = 2.0
    // 1.0 = 0x3C, 2.0 = 0x40
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h3C && b == 8'h3C) begin
            p_one_plus_one: assert (result == 8'h40);
        end
    end

    // =========================================================================
    // Property 11: Known test vector: 1.0 + (-1.0) = 0.0
    // 1.0 = 0x3C, -1.0 = 0xBC
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h3C && b == 8'hBC) begin
            p_one_minus_one: assert (result == 8'h00);
        end
    end

    // =========================================================================
    // Property 12: Known test vector: 2.0 + 2.0 = 4.0
    // 2.0 = 0x40, 4.0 = 0x44
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h40) begin
            p_two_plus_two: assert (result == 8'h44);
        end
    end

    // =========================================================================
    // Property 13: Overflow flag -> result is infinity
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 14: Underflow flag -> result is zero
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 15: Invalid flag -> result is NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 16: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 17: Result exponent validity for normal results
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 5'h01 && exp_r <= 5'h1E);
        end
    end

    // =========================================================================
    // Property 18: Subnormal inputs treated as zero (FTZ mode)
    // subnorm + normal = normal (subnorm flushed to zero)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm && b_is_normal) begin
            p_subnorm_a_identity: assert (result == b);
        end
        if (b_is_subnorm && a_is_normal) begin
            p_subnorm_b_identity: assert (result == a);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_add: cover (a_is_normal && b_is_normal && !overflow && !underflow);
        c_normal_sub: cover (a_is_normal && b_is_normal && sign_a != sign_b && !r_is_zero);
        c_exact_zero: cover (a_is_normal && b_is_normal && r_is_zero);
        c_overflow:   cover (overflow);
        c_underflow:  cover (underflow);
        c_nan:        cover (r_is_nan);
        c_inf_overflow: cover (a_is_normal && b_is_normal && r_is_inf);
    end

endmodule
