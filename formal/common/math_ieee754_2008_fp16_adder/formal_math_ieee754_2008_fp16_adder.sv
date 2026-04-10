// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp16_adder
//
// Verifies structural IEEE 754-2008 FP16 addition properties:
//   - Identity: a + 0 = a
//   - Additive inverse: a + (-a) = 0
//   - NaN propagation
//   - Infinity handling (inf + x, inf - inf)
//   - Known test vectors
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp16_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;

    // =========================================================================
    // DUT instantiation (combinational mode)
    // =========================================================================
    logic [15:0] result;
    logic        overflow, underflow, invalid, valid_out;

    math_ieee754_2008_fp16_adder #(
        .PIPE_STAGE_1(0),
        .PIPE_STAGE_2(0),
        .PIPE_STAGE_3(0),
        .PIPE_STAGE_4(0)
    ) dut (
        .i_clk       (clk),
        .i_rst_n     (1'b1),
        .i_a         (a),
        .i_b         (b),
        .i_valid     (1'b1),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid),
        .ow_valid    (valid_out)
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

    wire        sign_r  = result[15];
    wire [4:0]  exp_r   = result[14:10];
    wire [9:0]  mant_r  = result[9:0];

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
    wire inf_minus_inf = a_is_inf && b_is_inf && (sign_a != sign_b);

    // =========================================================================
    // Property 1: NaN propagation
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 2: inf - inf = NaN
    // =========================================================================
    always @(posedge clk) begin
        if (inf_minus_inf && !any_nan) begin
            p_inf_minus_inf_nan: assert (r_is_nan);
            p_inf_minus_inf_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: a + (+0) = a for normal numbers
    // FP16 +0 = 0x0000
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == 16'h0000) begin
            p_add_pos_zero: assert (result == a);
        end
    end

    // =========================================================================
    // Property 4: (+0) + b = b for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_normal && a == 16'h0000) begin
            p_zero_plus_b: assert (result == b);
        end
    end

    // =========================================================================
    // Property 5: inf + normal = inf
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && !b_is_inf && !b_is_nan) begin
            p_inf_plus_normal: assert (r_is_inf);
            p_inf_plus_normal_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 6: normal + inf = inf
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_inf && !a_is_inf && !a_is_nan) begin
            p_normal_plus_inf: assert (r_is_inf);
            p_normal_plus_inf_sign: assert (sign_r == sign_b);
        end
    end

    // =========================================================================
    // Property 7: inf + inf (same sign) = inf
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf && sign_a == sign_b) begin
            p_inf_plus_inf: assert (r_is_inf);
            p_inf_plus_inf_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 8: Known vector 1.0 + 1.0 = 2.0
    // FP16: 1.0 = 0x3C00, 2.0 = 0x4000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3C00 && b == 16'h3C00) begin
            p_one_plus_one: assert (result == 16'h4000);
        end
    end

    // =========================================================================
    // Property 9: Known vector 1.0 + (-1.0) = 0.0
    // FP16: 1.0 = 0x3C00, -1.0 = 0xBC00
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3C00 && b == 16'hBC00) begin
            p_one_minus_one: assert (result == 16'h0000);
        end
    end

    // =========================================================================
    // Property 10: Known vector 3.0 + 4.0 = 7.0
    // FP16: 3.0 = 0x4200, 4.0 = 0x4400, 7.0 = 0x4700
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h4200 && b == 16'h4400) begin
            p_three_plus_four: assert (result == 16'h4700);
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
    // Property 15: Valid passthrough
    // =========================================================================
    always @(posedge clk) begin
        p_valid_passthrough: assert (valid_out == 1'b1);
    end

    // =========================================================================
    // Property 16: Normal result exp in [1, 30]
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
        c_normal_add: cover (a_is_normal && b_is_normal && !overflow && !underflow);
        c_normal_sub: cover (a_is_normal && b_is_normal && sign_a != sign_b && !r_is_zero);
        c_exact_zero: cover (a_is_normal && b_is_normal && r_is_zero);
        c_overflow:   cover (overflow);
        c_underflow:  cover (underflow);
        c_nan:        cover (r_is_nan);
        c_inf_overflow: cover (a_is_normal && b_is_normal && r_is_inf);
    end

endmodule
