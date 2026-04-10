// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_log2
//
// Verifies:
//   - NaN handling (NaN -> NaN, negative -> NaN)
//   - log2(0) = -inf
//   - log2(+inf) = +inf
//   - log2(1.0) = 0
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_bf16_log2 (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] x;

    // =========================================================================
    // DUT instantiation (default LUT_DEPTH=32)
    // =========================================================================
    logic [15:0] log_result;
    logic        is_zero, is_inf, is_nan, is_neg;

    math_bf16_log2 #(
        .LUT_DEPTH(32)
    ) dut (
        .i_bf16    (x),
        .ow_log2   (log_result),
        .ow_is_zero(is_zero),
        .ow_is_inf (is_inf),
        .ow_is_nan (is_nan),
        .ow_is_neg (is_neg)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_x = x[15];
    wire [7:0]  exp_x  = x[14:7];
    wire [6:0]  mant_x = x[6:0];

    wire x_is_zero_or_sub = (exp_x == 8'd0);
    wire x_is_inf         = (exp_x == 8'd255) && (mant_x == 7'd0);
    wire x_is_nan_val     = (exp_x == 8'd255) && (mant_x != 7'd0);
    wire x_is_negative    = sign_x && !x_is_nan_val;
    wire x_is_normal_pos  = !sign_x && !x_is_zero_or_sub && !x_is_inf && !x_is_nan_val;

    // =========================================================================
    // Property: NaN input -> NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_nan_val) begin
            p_nan_in: assert (log_result == 16'h7FC0);
            p_nan_flag: assert (is_nan);
        end
    end

    // =========================================================================
    // Property: Negative input -> NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_negative) begin
            p_neg_nan: assert (log_result == 16'h7FC0);
            p_neg_flag: assert (is_neg);
        end
    end

    // =========================================================================
    // Property: log2(0) = -inf
    // =========================================================================
    always @(posedge clk) begin
        if (!sign_x && x_is_zero_or_sub) begin
            p_log_zero: assert (log_result == 16'hFF80);  // -inf
            p_zero_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property: log2(+inf) = +inf
    // =========================================================================
    always @(posedge clk) begin
        if (!sign_x && x_is_inf) begin
            p_log_inf: assert (log_result == 16'h7F80);   // +inf
            p_inf_flag: assert (is_inf);
        end
    end

    // =========================================================================
    // Property: log2(1.0) = 0 (BF16 1.0 = 0x3F80)
    // =========================================================================
    always @(posedge clk) begin
        if (x == 16'h3F80) begin
            p_log_one: assert (log_result == 16'h0000);
        end
    end

    // =========================================================================
    // Property: Normal positive input does not produce NaN
    // =========================================================================
    always @(posedge clk) begin
        if (x_is_normal_pos) begin
            p_normal_no_nan: assert (log_result != 16'h7FC0);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_pos: cover (x_is_normal_pos);
        c_zero_in:    cover (is_zero);
        c_inf_in:     cover (is_inf);
        c_neg_in:     cover (is_neg);
        c_nan_in:     cover (x_is_nan_val);
    end

endmodule
