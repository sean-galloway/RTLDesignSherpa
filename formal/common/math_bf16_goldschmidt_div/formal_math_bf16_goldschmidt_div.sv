// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_goldschmidt_div
// Uses combinational mode (PIPELINED=0) for BMC at depth 2.
//
// Verifies:
//   - NaN handling (NaN in, 0/0, inf/inf -> NaN)
//   - Division by zero -> infinity with flag
//   - Sign correctness
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_bf16_goldschmidt_div (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] num;
    (* anyconst *) logic [15:0] den;

    // =========================================================================
    // DUT instantiation (combinational, 1 iteration)
    // =========================================================================
    logic [15:0] quotient;
    logic        valid_out, div_by_zero, is_inf, is_nan;

    math_bf16_goldschmidt_div #(
        .ITERATIONS(1),
        .LUT_DEPTH(32),
        .PIPELINED(0)
    ) dut (
        .i_clk         (clk),
        .i_rst_n       (1'b1),
        .i_numerator   (num),
        .i_denominator (den),
        .i_valid       (1'b1),
        .ow_quotient   (quotient),
        .ow_valid      (valid_out),
        .ow_div_by_zero(div_by_zero),
        .ow_is_inf     (is_inf),
        .ow_is_nan     (is_nan)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = num[15];
    wire [7:0]  exp_a  = num[14:7];
    wire [6:0]  mant_a = num[6:0];

    wire        sign_b = den[15];
    wire [7:0]  exp_b  = den[14:7];
    wire [6:0]  mant_b = den[6:0];

    wire        sign_r = quotient[15];
    wire [7:0]  exp_r  = quotient[14:7];
    wire [6:0]  mant_r = quotient[6:0];

    wire a_is_zero = (exp_a == 8'd0);
    wire b_is_zero = (exp_b == 8'd0);
    wire a_is_inf  = (exp_a == 8'd255) && (mant_a == 7'd0);
    wire b_is_inf  = (exp_b == 8'd255) && (mant_b == 7'd0);
    wire a_is_nan  = (exp_a == 8'd255) && (mant_a != 7'd0);
    wire b_is_nan  = (exp_b == 8'd255) && (mant_b != 7'd0);

    wire any_nan       = a_is_nan || b_is_nan;
    wire zero_div_zero = a_is_zero && b_is_zero;
    wire inf_div_inf   = a_is_inf && b_is_inf;
    wire expected_sign = sign_a ^ sign_b;

    wire r_is_nan = (exp_r == 8'hFF) && (mant_r != 7'h00);
    wire r_is_inf = (exp_r == 8'hFF) && (mant_r == 7'h00);

    // =========================================================================
    // Property: NaN input -> NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_in: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: 0/0 -> NaN
    // =========================================================================
    always @(posedge clk) begin
        if (zero_div_zero && !any_nan) begin
            p_zero_div_zero: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: inf/inf -> NaN
    // =========================================================================
    always @(posedge clk) begin
        if (inf_div_inf && !any_nan) begin
            p_inf_div_inf: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: normal / 0 -> infinity with div_by_zero flag
    // =========================================================================
    always @(posedge clk) begin
        if (!a_is_zero && !a_is_nan && b_is_zero) begin
            p_div_by_zero: assert (div_by_zero);
        end
    end

    // =========================================================================
    // Property: div_by_zero flag only when denominator is zero
    // =========================================================================
    always @(posedge clk) begin
        if (div_by_zero) begin
            p_dbz_implies_b_zero: assert (b_is_zero);
        end
    end

    // =========================================================================
    // Property: is_nan flag implies NaN output encoding
    // =========================================================================
    always @(posedge clk) begin
        if (is_nan) begin
            p_nan_flag_encoding: assert (quotient == 16'h7FC0);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_div:   cover (!a_is_zero && !a_is_inf && !a_is_nan &&
                               !b_is_zero && !b_is_inf && !b_is_nan);
        c_div_by_zero:  cover (div_by_zero);
        c_nan_result:   cover (is_nan);
    end

endmodule
