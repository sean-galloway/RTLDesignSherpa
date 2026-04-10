// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp16_fma
//
// Verifies structural IEEE 754-2008 FP16 FMA properties:
//   result = (a * b) + c   where a, b, c are all FP16
//
//   - Special value handling (zero, infinity, NaN)
//   - NaN propagation
//   - Invalid operations (0*inf, inf + (-inf))
//   - c passthrough when product is zero
//   - Known test vectors
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp16_fma (
    input logic clk
);

    // =========================================================================
    // Free inputs (all FP16)
    // =========================================================================
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;
    (* anyconst *) logic [15:0] c;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] result;
    logic        overflow, underflow, invalid;

    math_ieee754_2008_fp16_fma dut (
        .i_a         (a),
        .i_b         (b),
        .i_c         (c),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP16 field extraction
    // =========================================================================
    wire        sign_a  = a[15];
    wire [4:0]  exp_a   = a[14:10];
    wire [9:0]  mant_a  = a[9:0];

    wire        sign_b  = b[15];
    wire [4:0]  exp_b   = b[14:10];
    wire [9:0]  mant_b  = b[9:0];

    wire        sign_c  = c[15];
    wire [4:0]  exp_c   = c[14:10];
    wire [9:0]  mant_c  = c[9:0];

    wire        sign_r  = result[15];
    wire [4:0]  exp_r   = result[14:10];
    wire [9:0]  mant_r  = result[9:0];

    // A special cases
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 10'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 10'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 10'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 10'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;

    // B special cases
    wire b_is_zero     = (exp_b == 5'h00) && (mant_b == 10'h0);
    wire b_is_subnorm  = (exp_b == 5'h00) && (mant_b != 10'h0);
    wire b_is_inf      = (exp_b == 5'h1F) && (mant_b == 10'h0);
    wire b_is_nan      = (exp_b == 5'h1F) && (mant_b != 10'h0);
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    // C special cases
    wire c_is_zero     = (exp_c == 5'h00) && (mant_c == 10'h0);
    wire c_is_subnorm  = (exp_c == 5'h00) && (mant_c != 10'h0);
    wire c_is_inf      = (exp_c == 5'h1F) && (mant_c == 10'h0);
    wire c_is_nan      = (exp_c == 5'h1F) && (mant_c != 10'h0);
    wire c_eff_zero    = c_is_zero || c_is_subnorm;
    wire c_is_normal   = !c_eff_zero && !c_is_inf && !c_is_nan;

    // Result classification
    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 10'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 10'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 10'h0);

    wire any_nan       = a_is_nan || b_is_nan || c_is_nan;
    wire prod_sign     = sign_a ^ sign_b;
    wire prod_is_inf   = a_is_inf || b_is_inf;
    wire prod_is_zero  = a_eff_zero || b_eff_zero;
    wire invalid_mul   = (a_eff_zero && b_is_inf) || (b_eff_zero && a_is_inf);
    wire invalid_add   = prod_is_inf && c_is_inf && (prod_sign != sign_c);

    // =========================================================================
    // Property 1: NaN propagation
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 2: Invalid mul (0 * inf) -> NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_mul && !any_nan) begin
            p_invalid_mul_nan: assert (r_is_nan);
            p_invalid_mul_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Invalid add (inf + (-inf)) -> NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_add && !any_nan && !invalid_mul) begin
            p_invalid_add_nan: assert (r_is_nan);
            p_invalid_add_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 4: 0 * b + c = c when c is normal
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_zero && b_is_normal && c_is_normal) begin
            p_zero_a_passthrough: assert (result == c);
        end
    end

    // =========================================================================
    // Property 5: a * 0 + c = c when c is normal
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_zero && a_is_normal && c_is_normal) begin
            p_zero_b_passthrough: assert (result == c);
        end
    end

    // =========================================================================
    // Property 6: Product infinity propagation
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
    // Property 7: Addend infinity
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_normal && c_is_inf) begin
            p_inf_c_result: assert (r_is_inf);
            p_inf_c_sign: assert (sign_r == sign_c);
        end
    end

    // =========================================================================
    // Property 8: All zero
    // =========================================================================
    always @(posedge clk) begin
        if (prod_is_zero && c_eff_zero && !any_nan && !prod_is_inf) begin
            p_all_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 9: Known vector 1.0 * 1.0 + 0.0 = 1.0
    // FP16 1.0 = 0x3C00, 0.0 = 0x0000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3C00 && b == 16'h3C00 && c == 16'h0000) begin
            p_one_times_one_plus_zero: assert (result == 16'h3C00);
        end
    end

    // =========================================================================
    // Property 10: Known vector 1.0 * 1.0 + 1.0 = 2.0
    // FP16 2.0 = 0x4000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3C00 && b == 16'h3C00 && c == 16'h3C00) begin
            p_one_times_one_plus_one: assert (result == 16'h4000);
        end
    end

    // =========================================================================
    // Property 11: Known vector 2.0 * 3.0 + 0.0 = 6.0
    // FP16 2.0=0x4000, 3.0=0x4200, 6.0=0x4600
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h4000 && b == 16'h4200 && c == 16'h0000) begin
            p_two_times_three_plus_zero: assert (result == 16'h4600);
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
    // Property 15: Flags mutex
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 16: c=0 product overflow -> inf
    // =========================================================================
    always @(posedge clk) begin
        if (c_eff_zero && a_is_normal && b_is_normal && !any_nan && overflow) begin
            p_c_zero_prod_overflow_inf: assert (r_is_inf);
            p_c_zero_prod_overflow_sign: assert (sign_r == prod_sign);
        end
    end

    // =========================================================================
    // Property 17: c=0 product underflow -> zero
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
        c_overflow: cover (overflow);
        c_underflow: cover (underflow);
        c_invalid_mul: cover (invalid_mul && !any_nan);
        c_inf_product: cover (prod_is_inf && c_is_normal && !invalid_mul);
    end

endmodule
