// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_fma
//
// Verifies structural FP8 E5M2 fused multiply-add properties:
//   result = (a * b) + c   where a, b, c are all FP8 E5M2
//
// Properties verified:
//   - NaN propagation from any input
//   - Invalid operations (0*inf, inf + (-inf))
//   - Zero product pass-through: 0*b + c = c
//   - Infinity propagation
//   - Known test vectors
//   - Flag consistency
//
// FP8 E5M2 format: [7]=sign, [6:2]=exp (bias=15), [1:0]=mant
// Inf: exp=31, mant=0
// NaN: exp=31, mant!=0

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_fma (
    input logic clk
);

    // =========================================================================
    // Free inputs (three 8-bit operands, fully enumerable: 2^24 ~ 16M states)
    // =========================================================================
    (* anyconst *) logic [7:0] a;
    (* anyconst *) logic [7:0] b;
    (* anyconst *) logic [7:0] c;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] result;
    logic       overflow, underflow, invalid;

    math_fp8_e5m2_fma dut (
        .i_a         (a),
        .i_b         (b),
        .i_c         (c),
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

    wire       sign_c = c[7];
    wire [4:0] exp_c  = c[6:2];
    wire [1:0] mant_c = c[1:0];

    wire       sign_r = result[7];
    wire [4:0] exp_r  = result[6:2];
    wire [1:0] mant_r = result[1:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 2'h0);
    wire b_is_zero     = (exp_b == 5'h00) && (mant_b == 2'h0);
    wire c_is_zero     = (exp_c == 5'h00) && (mant_c == 2'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 2'h0);
    wire b_is_subnorm  = (exp_b == 5'h00) && (mant_b != 2'h0);
    wire c_is_subnorm  = (exp_c == 5'h00) && (mant_c != 2'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 2'h0);
    wire b_is_inf      = (exp_b == 5'h1F) && (mant_b == 2'h0);
    wire c_is_inf      = (exp_c == 5'h1F) && (mant_c == 2'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 2'h0);
    wire b_is_nan      = (exp_b == 5'h1F) && (mant_b != 2'h0);
    wire c_is_nan      = (exp_c == 5'h1F) && (mant_c != 2'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire c_eff_zero    = c_is_zero || c_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;
    wire c_is_normal   = !c_eff_zero && !c_is_inf && !c_is_nan;

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 2'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 2'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 2'h0);

    // Derived flags
    wire any_nan       = a_is_nan || b_is_nan || c_is_nan;
    wire prod_sign     = sign_a ^ sign_b;
    wire prod_is_inf   = (a_is_inf || b_is_inf);
    wire prod_is_zero  = a_eff_zero || b_eff_zero;
    wire invalid_mul   = (a_eff_zero && b_is_inf) || (b_eff_zero && a_is_inf);
    wire invalid_add   = prod_is_inf && c_is_inf && !invalid_mul && (prod_sign != sign_c);

    // =========================================================================
    // Property 1: NaN propagation -- any NaN input produces NaN
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 2: Invalid multiply (0 * inf) produces NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_mul && !any_nan) begin
            p_invalid_mul_nan: assert (r_is_nan);
            p_invalid_mul_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Invalid add (inf + (-inf)) produces NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_add && !any_nan) begin
            p_invalid_add_nan: assert (r_is_nan);
            p_invalid_add_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 4: 0 * b + c = c (product zero, c passthrough)
    // When a is zero, b normal, c normal
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_is_normal && c_is_normal) begin
            p_zero_a_passthrough: assert (result == c);
        end
    end

    // =========================================================================
    // Property 5: a * 0 + c = c (product zero, c passthrough)
    // =========================================================================
    always @(posedge clk) begin
        if (b_eff_zero && a_is_normal && c_is_normal) begin
            p_zero_b_passthrough: assert (result == c);
        end
    end

    // =========================================================================
    // Property 6: Product infinity propagation
    // inf * normal + normal = inf (with product sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_normal && !c_is_inf && !c_is_nan) begin
            p_inf_a_result: assert (r_is_inf);
            p_inf_a_sign: assert (sign_r == prod_sign);
        end
        if (b_is_inf && a_is_normal && !c_is_inf && !c_is_nan) begin
            p_inf_b_result: assert (r_is_inf);
            p_inf_b_sign: assert (sign_r == prod_sign);
        end
    end

    // =========================================================================
    // Property 7: Addend infinity propagation
    // normal * normal + inf = inf (with c sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal && c_is_inf) begin
            p_inf_c_result: assert (r_is_inf);
            p_inf_c_sign: assert (sign_r == sign_c);
        end
    end

    // =========================================================================
    // Property 8: Both product and addend zero -> zero result
    // =========================================================================
    always @(posedge clk) begin
        if (prod_is_zero && c_eff_zero && !any_nan && !prod_is_inf) begin
            p_all_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 9: Known test vector: 1.0 * 1.0 + 0.0 = 1.0
    // 1.0 = 0x3C, 0.0 = 0x00
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h3C && b == 8'h3C && c == 8'h00) begin
            p_one_times_one_plus_zero: assert (result == 8'h3C);
        end
    end

    // =========================================================================
    // Property 10: Known test vector: 1.0 * 1.0 + 1.0 = 2.0
    // 2.0 = 0x40
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h3C && b == 8'h3C && c == 8'h3C) begin
            p_one_times_one_plus_one: assert (result == 8'h40);
        end
    end

    // =========================================================================
    // Property 11: Known test vector: 2.0 * 2.0 + 0.0 = 4.0
    // 2.0 = 0x40, 4.0 = 0x44
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h40 && c == 8'h00) begin
            p_two_times_two_plus_zero: assert (result == 8'h44);
        end
    end

    // =========================================================================
    // Property 12: Overflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 13: Underflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 14: Invalid flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 15: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 16: Result exponent validity for normal results
    // E5M2 normal: exp in [1, 30]
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 5'h01 && exp_r <= 5'h1E);
        end
    end

    // =========================================================================
    // Property 16b: c=0 with product overflow produces infinity
    // When c is effectively zero and the product overflows, the result must
    // be infinity (not garbage from truncated exponent bits).
    // =========================================================================
    always @(posedge clk) begin
        if (c_eff_zero && a_is_normal && b_is_normal && !any_nan && overflow) begin
            p_c_zero_prod_overflow_inf: assert (r_is_inf);
            p_c_zero_prod_overflow_sign: assert (sign_r == prod_sign);
        end
    end

    // =========================================================================
    // Property 16c: c=0 with product underflow produces zero
    // When c is effectively zero and the product underflows, the result must
    // be zero (not garbage from raw product bits).
    // =========================================================================
    always @(posedge clk) begin
        if (c_eff_zero && a_is_normal && b_is_normal && !any_nan && underflow) begin
            p_c_zero_prod_underflow_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_fma: cover (a_is_normal && b_is_normal && c_is_normal &&
                             !overflow && !underflow && !invalid);
        c_zero_product: cover (prod_is_zero && c_is_normal);
        c_nan_result: cover (r_is_nan);
        c_overflow:   cover (overflow);
        c_underflow:  cover (underflow);
        c_invalid_mul: cover (invalid_mul && !any_nan);
        c_inf_product: cover (prod_is_inf && c_is_normal && !invalid_mul);
    end

endmodule
