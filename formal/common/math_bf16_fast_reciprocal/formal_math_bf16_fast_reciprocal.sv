// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_fast_reciprocal
//
// Verifies:
//   - NaN handling (NaN -> NaN, flag set)
//   - 1/0 = infinity (flag set)
//   - 1/inf = 0 (flag set)
//   - Sign preservation
//   - Known vector: 1/1.0 = 1.0

`timescale 1ns / 1ps

module formal_math_bf16_fast_reciprocal (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] x;

    // =========================================================================
    // DUT instantiation (default LUT_DEPTH=32)
    // =========================================================================
    logic [15:0] recip;
    logic        is_zero, is_inf, is_nan, uflow;
    logic [6:0]  mant_approx;

    math_bf16_fast_reciprocal #(
        .LUT_DEPTH(32)
    ) dut (
        .i_bf16         (x),
        .ow_reciprocal  (recip),
        .ow_is_zero     (is_zero),
        .ow_is_inf      (is_inf),
        .ow_is_nan      (is_nan),
        .ow_underflow   (uflow),
        .ow_mant_approx (mant_approx)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_x = x[15];
    wire [7:0]  exp_x  = x[14:7];
    wire [6:0]  mant_x = x[6:0];

    wire        sign_r = recip[15];
    wire [7:0]  exp_r  = recip[14:7];
    wire [6:0]  mant_r = recip[6:0];

    wire x_is_zero_or_sub = (exp_x == 8'd0);
    wire x_is_inf         = (exp_x == 8'd255) && (mant_x == 7'd0);
    wire x_is_nan         = (exp_x == 8'd255) && (mant_x != 7'd0);
    wire x_is_normal      = !x_is_zero_or_sub && !x_is_inf && !x_is_nan;

    wire r_is_zero = (exp_r == 8'h00) && (mant_r == 7'h00);
    wire r_is_inf  = (exp_r == 8'hFF) && (mant_r == 7'h00);
    wire r_is_nan  = (exp_r == 8'hFF) && (mant_r != 7'h00);

    // =========================================================================
    // Property: NaN -> NaN, flag set
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_nan) begin
            p_nan_out: assert (r_is_nan || recip == 16'h7FC0);
            p_nan_flag: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: zero/subnormal -> infinity
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_zero_or_sub) begin
            p_zero_to_inf: assert (r_is_inf);
            p_zero_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property: infinity -> zero
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_inf) begin
            p_inf_to_zero: assert (r_is_zero);
            p_inf_flag: assert (is_inf);
        end
    end

    // =========================================================================
    // Property: Sign preservation
    // =========================================================================
    always @(posedge clk) begin
        if (!x_is_nan) begin
            p_sign_preserved: assert (sign_r == sign_x);
        end
    end

    // =========================================================================
    // Property: Known vector 1/1.0 = 1.0
    // When exp=127, mant=0: recip should be exp=127, mant=0 (exact power of 2)
    // =========================================================================
    always @(posedge clk) begin
        if (x == 16'h3F80) begin
            p_recip_one: assert (recip == 16'h3F80);
        end
    end

    // =========================================================================
    // Property: Normal input doesn't produce NaN
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_normal) begin
            p_no_spurious_nan: assert (!r_is_nan);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal:   cover (x_is_normal && !uflow);
        c_underflow: cover (uflow);
        c_zero_in:  cover (is_zero);
        c_inf_in:   cover (is_inf);
        c_nan_in:   cover (is_nan);
    end

endmodule
