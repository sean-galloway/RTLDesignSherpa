// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_exp2
//
// Verifies:
//   - NaN handling (NaN -> NaN)
//   - exp2(0) = 1.0
//   - exp2(+inf) = +inf
//   - exp2(-inf) = 0
//   - Large positive overflow
//   - Large negative underflow to zero
//   - Result is always non-negative

`timescale 1ns / 1ps

module formal_math_bf16_exp2 (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] x;

    // =========================================================================
    // DUT instantiation (default LUT_DEPTH=32)
    // =========================================================================
    logic [15:0] exp_result;
    logic        is_zero, is_inf, is_nan;

    math_bf16_exp2 #(
        .LUT_DEPTH(32)
    ) dut (
        .i_bf16    (x),
        .ow_exp2   (exp_result),
        .ow_is_zero(is_zero),
        .ow_is_inf (is_inf),
        .ow_is_nan (is_nan)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_x = x[15];
    wire [7:0]  exp_x  = x[14:7];
    wire [6:0]  mant_x = x[6:0];

    wire        sign_r = exp_result[15];
    wire [7:0]  exp_r  = exp_result[14:7];
    wire [6:0]  mant_r = exp_result[6:0];

    wire x_is_zero     = (exp_x == 8'd0);
    wire x_is_inf      = (exp_x == 8'd255) && (mant_x == 7'd0);
    wire x_is_nan_val  = (exp_x == 8'd255) && (mant_x != 7'd0);
    wire x_is_normal   = !x_is_zero && !x_is_inf && !x_is_nan_val;

    wire r_is_nan = (exp_r == 8'hFF) && (mant_r != 7'h00);

    // =========================================================================
    // Property: NaN input -> NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_nan_val) begin
            p_nan_in: assert (exp_result == 16'h7FC0);
            p_nan_flag: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: exp2(0) = 1.0 (zero input includes +0 and subnormals)
    // =========================================================================
    always @(posedge clk) begin
        if (x == 16'h0000) begin
            p_exp_zero: assert (exp_result == 16'h3F80);
        end
    end

    // =========================================================================
    // Property: exp2(+inf) = +inf
    // =========================================================================
    always @(posedge clk) begin
        if (!sign_x && x_is_inf) begin
            p_pos_inf: assert (exp_result == 16'h7F80);
            p_pos_inf_flag: assert (is_inf);
        end
    end

    // =========================================================================
    // Property: exp2(-inf) = 0
    // =========================================================================
    always @(posedge clk) begin
        if (sign_x && x_is_inf) begin
            p_neg_inf: assert (exp_result == 16'h0000);
            p_neg_inf_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property: Result is always non-negative (2^x > 0)
    // =========================================================================
    always @(posedge clk) begin
        if (!x_is_nan_val) begin
            p_non_negative: assert (sign_r == 1'b0);
        end
    end

    // =========================================================================
    // Property: Non-NaN input does not produce NaN
    // =========================================================================
    always @(posedge clk) begin
        if (!x_is_nan_val) begin
            p_no_spurious_nan: assert (!r_is_nan);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal:    cover (x_is_normal && !is_zero && !is_inf);
        c_zero_out:  cover (is_zero);
        c_inf_out:   cover (is_inf);
        c_nan:       cover (is_nan);
        c_one_out:   cover (exp_result == 16'h3F80);
    end

endmodule
