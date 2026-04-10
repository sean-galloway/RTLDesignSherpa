// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_reciprocal
//
// Verifies:
//   - NaN handling (NaN -> NaN with invalid flag)
//   - 1/0 = infinity with div_by_zero flag
//   - 1/inf = 0 with is_zero flag
//   - Sign preservation
//   - Known vector: 1/1.0 = 1.0

`timescale 1ns / 1ps

module formal_math_bf16_reciprocal (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] x;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] recip;
    logic        dut_div_by_zero, dut_is_zero, dut_invalid;

    math_bf16_reciprocal dut (
        .i_x            (x),
        .ow_reciprocal  (recip),
        .ow_div_by_zero (dut_div_by_zero),
        .ow_is_zero     (dut_is_zero),
        .ow_invalid     (dut_invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_x  = x[15];
    wire [7:0]  exp_x   = x[14:7];
    wire [6:0]  mant_x  = x[6:0];

    wire        sign_r  = recip[15];
    wire [7:0]  exp_r   = recip[14:7];
    wire [6:0]  mant_r  = recip[6:0];

    wire x_is_zero     = (exp_x == 8'h00) && (mant_x == 7'h00);
    wire x_is_subnorm  = (exp_x == 8'h00) && (mant_x != 7'h00);
    wire x_eff_zero    = x_is_zero || x_is_subnorm;
    wire x_is_inf      = (exp_x == 8'hFF) && (mant_x == 7'h00);
    wire x_is_nan      = (exp_x == 8'hFF) && (mant_x != 7'h00);
    wire x_is_normal   = !x_eff_zero && !x_is_inf && !x_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 7'h00);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 7'h00);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 7'h00);

    // =========================================================================
    // Property: NaN input -> NaN output with invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_nan) begin
            p_nan_produces_nan: assert (r_is_nan);
            p_nan_invalid_flag: assert (dut_invalid);
        end
    end

    // =========================================================================
    // Property: 1/0 = infinity with div_by_zero flag
    // =========================================================================
    always @(posedge clk) begin
        if (x_eff_zero) begin
            p_zero_gives_inf: assert (r_is_inf);
            p_zero_div_flag:  assert (dut_div_by_zero);
        end
    end

    // =========================================================================
    // Property: 1/inf = 0 with is_zero flag
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_inf) begin
            p_inf_gives_zero: assert (r_is_zero);
            p_inf_zero_flag:  assert (dut_is_zero);
        end
    end

    // =========================================================================
    // Property: Sign preservation (1/x has same sign as x)
    // =========================================================================
    always @(posedge clk) begin
        if (!x_is_nan) begin
            p_sign_preserved: assert (sign_r == sign_x);
        end
    end

    // =========================================================================
    // Property: Known vector 1/1.0 = 1.0 (BF16 0x3F80)
    // =========================================================================
    always @(posedge clk) begin
        if (x == 16'h3F80) begin
            p_recip_one: assert (recip == 16'h3F80);
        end
    end

    // =========================================================================
    // Property: Normal input produces non-NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_normal) begin
            p_normal_no_nan: assert (!r_is_nan);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_recip: cover (x_is_normal && !r_is_zero && !r_is_inf);
        c_div_by_zero:  cover (dut_div_by_zero);
        c_zero_result:  cover (dut_is_zero);
        c_nan_input:    cover (x_is_nan);
    end

endmodule
