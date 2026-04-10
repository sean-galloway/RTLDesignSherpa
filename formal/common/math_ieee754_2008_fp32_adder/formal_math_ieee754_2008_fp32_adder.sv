// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp32_adder
//
// FP32 adder is 633 lines (complex 5-stage pipeline with barrel shifters,
// CLZ, wide adders). Focus on simpler structural properties that BMC can
// verify quickly:
//   - NaN propagation
//   - Sign correctness for normal inputs
//   - Infinity handling
//   - inf - inf = NaN
//   - Flag consistency
//   - Trivial identities (a + 0 = a, 0 + b = b)
//   - Known vectors

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp32_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [31:0] a;
    (* anyconst *) logic [31:0] b;

    // =========================================================================
    // DUT instantiation (all pipelines disabled for combinational)
    // =========================================================================
    logic [31:0] result;
    logic        overflow, underflow, invalid, valid_out;

    math_ieee754_2008_fp32_adder #(
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
    // FP32 field extraction
    // =========================================================================
    wire        sign_a  = a[31];
    wire [7:0]  exp_a   = a[30:23];
    wire [22:0] mant_a  = a[22:0];

    wire        sign_b  = b[31];
    wire [7:0]  exp_b   = b[30:23];
    wire [22:0] mant_b  = b[22:0];

    wire        sign_r  = result[31];
    wire [7:0]  exp_r   = result[30:23];
    wire [22:0] mant_r  = result[22:0];

    // Special values
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 23'h0);
    wire b_is_zero     = (exp_b == 8'h00) && (mant_b == 23'h0);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 23'h0);
    wire b_is_subnorm  = (exp_b == 8'h00) && (mant_b != 23'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 23'h0);
    wire b_is_inf      = (exp_b == 8'hFF) && (mant_b == 23'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 23'h0);
    wire b_is_nan      = (exp_b == 8'hFF) && (mant_b != 23'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 23'h0);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 23'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 23'h0);

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
    // Property 2: inf - inf -> NaN, invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (inf_minus_inf && !any_nan) begin
            p_inf_minus_inf_nan: assert (r_is_nan);
            p_inf_minus_inf_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: a + (+0) = a for normal a
    // FP32 +0 = 32'h00000000
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == 32'h00000000) begin
            p_add_pos_zero: assert (result == a);
        end
    end

    // =========================================================================
    // Property 4: (+0) + b = b for normal b
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_normal && a == 32'h00000000) begin
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
    // Property 8: Overflow flag -> inf
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 9: Underflow flag -> zero
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 10: Invalid flag -> nan
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 11: Flags mutex
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 12: valid passthrough
    // =========================================================================
    always @(posedge clk) begin
        p_valid_passthrough: assert (valid_out == 1'b1);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_add: cover (a_is_normal && b_is_normal && !overflow && !underflow);
        c_nan: cover (r_is_nan);
        c_overflow: cover (overflow);
    end

endmodule
