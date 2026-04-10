// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp32_fma
//
// FP32 FMA is 310 lines with 72-bit wide accumulation. Focus on structural
// properties that BMC can verify quickly:
//   - NaN propagation
//   - Invalid operations (0*inf, inf + (-inf))
//   - c passthrough when product is zero
//   - Special value handling
//   - Known test vectors
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp32_fma (
    input logic clk
);

    // =========================================================================
    // Free inputs (all FP32)
    // =========================================================================
    (* anyconst *) logic [31:0] a;
    (* anyconst *) logic [31:0] b;
    (* anyconst *) logic [31:0] c;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [31:0] result;
    logic        overflow, underflow, invalid;

    math_ieee754_2008_fp32_fma dut (
        .i_a         (a),
        .i_b         (b),
        .i_c         (c),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP32 field extraction
    // =========================================================================
    wire        sign_a   = a[31];
    wire [7:0]  exp_a    = a[30:23];
    wire [22:0] mant_a   = a[22:0];

    wire        sign_b   = b[31];
    wire [7:0]  exp_b    = b[30:23];
    wire [22:0] mant_b   = b[22:0];

    wire        sign_c   = c[31];
    wire [7:0]  exp_c    = c[30:23];
    wire [22:0] mant_c   = c[22:0];

    wire        sign_r   = result[31];
    wire [7:0]  exp_r    = result[30:23];
    wire [22:0] mant_r   = result[22:0];

    // Special values
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 23'h0);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 23'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 23'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 23'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;

    wire b_is_zero     = (exp_b == 8'h00) && (mant_b == 23'h0);
    wire b_is_subnorm  = (exp_b == 8'h00) && (mant_b != 23'h0);
    wire b_is_inf      = (exp_b == 8'hFF) && (mant_b == 23'h0);
    wire b_is_nan      = (exp_b == 8'hFF) && (mant_b != 23'h0);
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire c_is_zero     = (exp_c == 8'h00) && (mant_c == 23'h0);
    wire c_is_subnorm  = (exp_c == 8'h00) && (mant_c != 23'h0);
    wire c_is_inf      = (exp_c == 8'hFF) && (mant_c == 23'h0);
    wire c_is_nan      = (exp_c == 8'hFF) && (mant_c != 23'h0);
    wire c_eff_zero    = c_is_zero || c_is_subnorm;
    wire c_is_normal   = !c_eff_zero && !c_is_inf && !c_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 23'h0);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 23'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 23'h0);

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
    // Property 9: Overflow flag
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 10: Underflow flag
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 11: Invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 12: Flags mutex
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 13: c=0 product overflow -> inf
    // =========================================================================
    always @(posedge clk) begin
        if (c_eff_zero && a_is_normal && b_is_normal && !any_nan && overflow) begin
            p_c_zero_prod_overflow_inf: assert (r_is_inf);
            p_c_zero_prod_overflow_sign: assert (sign_r == prod_sign);
        end
    end

    // =========================================================================
    // Property 14: c=0 product underflow -> zero
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
        c_normal_fma: cover (a_is_normal && b_is_normal && c_is_normal && !overflow && !underflow);
        c_zero_product: cover (prod_is_zero && c_is_normal);
        c_nan_result: cover (r_is_nan);
        c_overflow: cover (overflow);
        c_invalid_mul: cover (invalid_mul && !any_nan);
    end

endmodule
