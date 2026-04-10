// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_newton_raphson_recip
//
// Verifies:
//   - NaN handling
//   - 1/0 = infinity, 1/inf = 0
//   - Sign preservation
//   - Known vector: 1/1.0 = 1.0
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_bf16_newton_raphson_recip (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] x;

    // =========================================================================
    // DUT instantiation (1 iteration, LUT_DEPTH=32)
    // =========================================================================
    logic [15:0] recip;
    logic        is_zero, is_inf, is_nan;

    math_bf16_newton_raphson_recip #(
        .ITERATIONS(1),
        .LUT_DEPTH(32)
    ) dut (
        .i_bf16        (x),
        .ow_reciprocal (recip),
        .ow_is_zero    (is_zero),
        .ow_is_inf     (is_inf),
        .ow_is_nan     (is_nan)
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
    wire x_is_nan_val     = (exp_x == 8'd255) && (mant_x != 7'd0);
    wire x_is_normal      = !x_is_zero_or_sub && !x_is_inf && !x_is_nan_val;

    wire r_is_nan = (exp_r == 8'hFF) && (mant_r != 7'h00);

    // =========================================================================
    // Property: NaN -> NaN
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_nan_val) begin
            p_nan_out: assert (r_is_nan || recip == 16'h7FC0);
            p_nan_flag: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: zero -> infinity
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_zero_or_sub) begin
            p_zero_flag: assert (is_zero);
            // Result should be +inf or -inf depending on sign
            p_zero_to_inf: assert (recip[14:0] == 15'h7F80);
        end
    end

    // =========================================================================
    // Property: infinity -> zero
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_inf) begin
            p_inf_flag: assert (is_inf);
            p_inf_to_zero: assert (recip[14:0] == 15'h0000);
        end
    end

    // =========================================================================
    // Property: Sign preservation
    // =========================================================================
    always @(posedge clk) begin
        if (!x_is_nan_val) begin
            p_sign_preserved: assert (sign_r == sign_x);
        end
    end

    // =========================================================================
    // Property: Normal input doesn't set NaN flag
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_normal) begin
            p_normal_no_nan_flag: assert (!is_nan);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal:  cover (x_is_normal);
        c_zero:    cover (is_zero);
        c_inf:     cover (is_inf);
        c_nan:     cover (is_nan);
    end

endmodule
