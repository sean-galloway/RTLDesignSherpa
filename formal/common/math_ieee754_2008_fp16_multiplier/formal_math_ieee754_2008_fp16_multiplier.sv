// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp16_multiplier
//
// Verifies structural IEEE 754-2008 FP16 multiplication properties:
//   - Sign correctness (sign_a XOR sign_b)
//   - Special value handling (zero, infinity, NaN)
//   - Known test vectors (1.0 * 1.0 = 1.0, etc.)
//   - Overflow/underflow flag consistency
//   - Result format validity

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp16_multiplier (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] result;
    logic        overflow, underflow, invalid;

    math_ieee754_2008_fp16_multiplier dut (
        .i_a         (a),
        .i_b         (b),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP16 field extraction
    // =========================================================================
    wire        sign_a   = a[15];
    wire [4:0]  exp_a    = a[14:10];
    wire [9:0]  mant_a   = a[9:0];

    wire        sign_b   = b[15];
    wire [4:0]  exp_b    = b[14:10];
    wire [9:0]  mant_b   = b[9:0];

    wire        sign_r   = result[15];
    wire [4:0]  exp_r    = result[14:10];
    wire [9:0]  mant_r   = result[9:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 10'h000);
    wire b_is_zero     = (exp_b == 5'h00) && (mant_b == 10'h000);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 10'h000);
    wire b_is_subnorm  = (exp_b == 5'h00) && (mant_b != 10'h000);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 10'h000);
    wire b_is_inf      = (exp_b == 5'h1F) && (mant_b == 10'h000);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 10'h000);
    wire b_is_nan      = (exp_b == 5'h1F) && (mant_b != 10'h000);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 10'h000);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 10'h000);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 10'h000);

    wire any_nan       = a_is_nan || b_is_nan;
    wire invalid_op    = (a_eff_zero && b_is_inf) || (b_eff_zero && a_is_inf);

    wire expected_sign = sign_a ^ sign_b;

    // =========================================================================
    // Property 1: Sign correctness (non-NaN cases)
    // =========================================================================
    always @(posedge clk) begin
        if (!any_nan && !invalid_op) begin
            p_sign_xor: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 2: NaN propagation
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 3: Invalid operation (0 * inf = NaN)
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_op && !any_nan) begin
            p_zero_times_inf_is_nan: assert (r_is_nan);
            p_invalid_flag_set: assert (invalid);
        end
    end

    // =========================================================================
    // Property 4: Zero input produces zero output (FTZ subnormals)
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && !b_is_inf && !b_is_nan) begin
            p_zero_a_result: assert (r_is_zero);
            p_zero_a_sign: assert (sign_r == expected_sign);
        end
        if (b_eff_zero && !a_is_inf && !a_is_nan) begin
            p_zero_b_result: assert (r_is_zero);
            p_zero_b_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 4b: Strict zero -- zero * non-special = exact 0
    // =========================================================================
    always @(posedge clk) begin
        if ((a_eff_zero || b_eff_zero) && !any_nan && !invalid_op) begin
            p_zero_strict: assert (result == {expected_sign, 5'h00, 10'h000});
        end
    end

    // =========================================================================
    // Property 5: Infinity propagation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_normal) begin
            p_inf_a_result: assert (r_is_inf);
            p_inf_a_sign: assert (sign_r == expected_sign);
        end
        if (b_is_inf && a_is_normal) begin
            p_inf_b_result: assert (r_is_inf);
            p_inf_b_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 6: inf * inf = inf
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf) begin
            p_inf_times_inf: assert (r_is_inf);
            p_inf_times_inf_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 7: Known vector 1.0 * 1.0 = 1.0
    // FP16 1.0: sign=0, exp=15 (0x0F), mant=0 -> 0x3C00
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3C00 && b == 16'h3C00) begin
            p_one_times_one: assert (result == 16'h3C00);
        end
    end

    // =========================================================================
    // Property 8: Known vector 2.0 * 3.0 = 6.0
    // FP16: 2.0 = 0x4000, 3.0 = 0x4200, 6.0 = 0x4600
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h4000 && b == 16'h4200) begin
            p_two_times_three: assert (result == 16'h4600);
        end
    end

    // =========================================================================
    // Property 9: Known vector -1.0 * 1.0 = -1.0
    // FP16 -1.0 = 0xBC00
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'hBC00 && b == 16'h3C00) begin
            p_neg_one_times_one: assert (result == 16'hBC00);
        end
    end

    // =========================================================================
    // Property 10: Known vector -1.0 * -1.0 = 1.0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'hBC00 && b == 16'hBC00) begin
            p_neg_one_times_neg_one: assert (result == 16'h3C00);
        end
    end

    // =========================================================================
    // Property 11: Overflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 12: Underflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 13: Invalid flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 14: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 15: Subnormal inputs treated as zero (FTZ)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm && b_is_normal) begin
            p_subnorm_a_ftz: assert (r_is_zero);
        end
        if (b_is_subnorm && a_is_normal) begin
            p_subnorm_b_ftz: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 16: Normal result exp range [1, 30]
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 5'h01 && exp_r <= 5'h1E);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_mult: cover (a_is_normal && b_is_normal && !overflow && !underflow && !invalid);
        c_overflow:    cover (overflow);
        c_underflow:   cover (underflow);
        c_invalid:     cover (invalid);
        c_nan_input:   cover (any_nan);
        c_inf_from_normal: cover (a_is_normal && b_is_normal && r_is_inf);
        c_zero_from_normal: cover (a_is_normal && b_is_normal && r_is_zero);
    end

endmodule
