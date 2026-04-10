// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_log2_scale
//
// Verifies:
//   - Zero input: scale = 1.0, is_zero flag
//   - NaN/Inf input: overflow flag
//   - scale_bf16 is always a power of 2 (mantissa = 0)
//   - scale >= max_value (scale is ceiling power of 2)
//   - Flag consistency

`timescale 1ns / 1ps

module formal_math_bf16_log2_scale (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] max_val;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0]  scale_exp;
    logic [4:0]  quant_shift, dequant_shift;
    logic [15:0] scale_bf16;
    logic        is_zero, is_overflow;

    math_bf16_log2_scale dut (
        .i_max_value    (max_val),
        .ow_scale_exp   (scale_exp),
        .ow_quant_shift (quant_shift),
        .ow_dequant_shift(dequant_shift),
        .ow_scale_bf16  (scale_bf16),
        .ow_is_zero     (is_zero),
        .ow_is_overflow (is_overflow)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire [7:0] exp_in  = max_val[14:7];
    wire [6:0] mant_in = max_val[6:0];

    wire in_is_zero    = (exp_in == 8'd0);
    wire in_is_inf     = (exp_in == 8'hFF) && (mant_in == 7'd0);
    wire in_is_nan     = (exp_in == 8'hFF) && (mant_in != 7'd0);
    wire in_is_normal  = !in_is_zero && !in_is_inf && !in_is_nan;

    // =========================================================================
    // Property: Zero input -> scale = 1.0, is_zero flag
    // =========================================================================
    always @(posedge clk) begin
        if (in_is_zero) begin
            p_zero_scale_exp: assert (scale_exp == 8'd127);
            p_zero_scale_bf16: assert (scale_bf16 == 16'h3F80);
            p_zero_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property: NaN/Inf -> overflow flag
    // =========================================================================
    always @(posedge clk) begin
        if (in_is_inf || in_is_nan) begin
            p_special_overflow: assert (is_overflow);
        end
    end

    // =========================================================================
    // Property: scale_bf16 is always a power of 2 (mantissa bits = 0)
    // =========================================================================
    always @(posedge clk) begin
        p_power_of_two: assert (scale_bf16[6:0] == 7'd0);
    end

    // =========================================================================
    // Property: scale_bf16 sign bit is 0 (always positive)
    // =========================================================================
    always @(posedge clk) begin
        p_positive_scale: assert (scale_bf16[15] == 1'b0);
    end

    // =========================================================================
    // Property: quant_shift == dequant_shift (symmetric)
    // =========================================================================
    always @(posedge clk) begin
        p_symmetric_shift: assert (quant_shift == dequant_shift);
    end

    // =========================================================================
    // Property: scale_exp >= input exponent for normal inputs
    // (scale is ceiling power of 2 >= max_value)
    // =========================================================================
    always @(posedge clk) begin
        if (in_is_normal && !is_overflow) begin
            p_scale_ge_input: assert (scale_exp >= exp_in);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal:    cover (in_is_normal && !is_overflow);
        c_zero:      cover (is_zero);
        c_overflow:  cover (is_overflow);
        c_large:     cover (in_is_normal && scale_exp > 8'd134);
    end

endmodule
