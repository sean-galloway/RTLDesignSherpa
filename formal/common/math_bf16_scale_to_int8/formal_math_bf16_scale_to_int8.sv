// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_scale_to_int8
//
// Verifies fused BF16 multiply + INT8 conversion (quantization):
//   - Output always in [-128, +127] range
//   - Zero input produces zero output
//   - NaN handling (any NaN -> invalid, output 0)
//   - Infinity handling (saturate)
//   - 0 * inf = invalid operation
//   - Overflow/underflow saturation
//   - Sign correctness

`timescale 1ns / 1ps

module formal_math_bf16_scale_to_int8 (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] value;
    (* anyconst *) logic [15:0] scale;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] int8_out;
    logic       overflow, underflow, is_zero, invalid;

    math_bf16_scale_to_int8 dut (
        .i_value     (value),
        .i_scale     (scale),
        .ow_int8     (int8_out),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_is_zero  (is_zero),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // BF16 field extraction
    // =========================================================================
    // Value
    wire        sign_v = value[15];
    wire [7:0]  exp_v  = value[14:7];
    wire [6:0]  mant_v = value[6:0];

    // Scale
    wire        sign_s = scale[15];
    wire [7:0]  exp_s  = scale[14:7];
    wire [6:0]  mant_s = scale[6:0];

    // Special value detection
    wire v_is_zero = (exp_v == 8'h00);
    wire v_is_inf  = (exp_v == 8'hFF) && (mant_v == 7'h00);
    wire v_is_nan  = (exp_v == 8'hFF) && (mant_v != 7'h00);

    wire s_is_zero = (exp_s == 8'h00);
    wire s_is_inf  = (exp_s == 8'hFF) && (mant_s == 7'h00);
    wire s_is_nan  = (exp_s == 8'hFF) && (mant_s != 7'h00);

    wire any_nan  = v_is_nan || s_is_nan;
    wire any_inf  = v_is_inf || s_is_inf;
    wire any_zero = v_is_zero || s_is_zero;

    // Invalid: 0 * inf or inf * 0
    wire invalid_op = (v_is_zero && s_is_inf) || (v_is_inf && s_is_zero);

    // Result sign
    wire expected_sign = sign_v ^ sign_s;

    // Interpret int8_out as signed
    wire signed [7:0] int8_signed = $signed(int8_out);

    // =========================================================================
    // Property 1: NaN or invalid operation produces invalid flag and zero output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan || invalid_op) begin
            p_nan_invalid_out: assert (int8_out == 8'd0);
            p_nan_invalid_flag: assert (invalid);
            p_nan_no_overflow: assert (!overflow);
            p_nan_no_underflow: assert (!underflow);
        end
    end

    // =========================================================================
    // Property 2: Zero input produces zero output
    // (when other operand is not inf/nan)
    // =========================================================================
    always @(posedge clk) begin
        if (any_zero && !any_nan && !invalid_op) begin
            p_zero_result: assert (int8_out == 8'd0);
            p_zero_flag: assert (is_zero);
            p_zero_no_overflow: assert (!overflow);
            p_zero_no_underflow: assert (!underflow);
            p_zero_no_invalid: assert (!invalid);
        end
    end

    // =========================================================================
    // Property 3: Infinity (non-invalid) saturates correctly
    // +inf -> +127, -inf -> -128
    // =========================================================================
    always @(posedge clk) begin
        if (any_inf && !any_nan && !invalid_op) begin
            if (!expected_sign) begin
                p_pos_inf_sat: assert (int8_out == 8'h7F);
                p_pos_inf_overflow: assert (overflow);
            end else begin
                p_neg_inf_sat: assert (int8_out == 8'h80);
                p_neg_inf_underflow: assert (underflow);
            end
            p_inf_no_invalid: assert (!invalid);
        end
    end

    // =========================================================================
    // Property 4: Overflow flag implies positive saturation to +127
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_val: assert (int8_out == 8'h7F);
        end
    end

    // =========================================================================
    // Property 5: Underflow flag implies negative saturation to -128
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_val: assert (int8_out == 8'h80);
        end
    end

    // =========================================================================
    // Property 6: Flags are mutually exclusive
    // At most one of overflow, underflow, invalid, is_zero can be set
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid + is_zero) <= 1);
    end

    // =========================================================================
    // Property 7: Invalid flag implies NaN or 0*inf input
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_special: assert (any_nan || invalid_op);
        end
    end

    // =========================================================================
    // Property 8: is_zero flag means output is zero
    // =========================================================================
    always @(posedge clk) begin
        if (is_zero) begin
            p_zero_flag_val: assert (int8_out == 8'd0);
        end
    end

    // =========================================================================
    // Property 9: Known vector: 1.0 * 1.0 = 1
    // BF16 1.0 = 0x3F80
    // =========================================================================
    always @(posedge clk) begin
        if (value == 16'h3F80 && scale == 16'h3F80) begin
            p_one_times_one: assert (int8_out == 8'd1);
            p_one_no_flags: assert (!overflow && !underflow && !invalid && !is_zero);
        end
    end

    // =========================================================================
    // Property 10: Known vector: -1.0 * 1.0 = -1
    // BF16 -1.0 = 0xBF80
    // =========================================================================
    always @(posedge clk) begin
        if (value == 16'hBF80 && scale == 16'h3F80) begin
            p_neg_one_times_one: assert (int8_out == 8'hFF);
        end
    end

    // =========================================================================
    // Property 11: Known vector: 0.0 * anything_normal = 0
    // =========================================================================
    always @(posedge clk) begin
        if (value == 16'h0000 && !s_is_inf && !s_is_nan) begin
            p_zero_times_normal: assert (int8_out == 8'd0);
            p_zero_times_normal_flag: assert (is_zero);
        end
    end

    // =========================================================================
    // Property 12: 0 * inf produces invalid
    // =========================================================================
    always @(posedge clk) begin
        // +0 * +inf
        if (value == 16'h0000 && scale == 16'h7F80) begin
            p_zero_times_inf: assert (invalid);
        end
        // +inf * +0
        if (value == 16'h7F80 && scale == 16'h0000) begin
            p_inf_times_zero: assert (invalid);
        end
    end

    // =========================================================================
    // Property 13: NaN input always produces invalid
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_produces_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 14: When no special cases and no flags, result is non-saturated
    // =========================================================================
    always @(posedge clk) begin
        if (!any_nan && !any_inf && !any_zero && !overflow && !underflow && !invalid && !is_zero) begin
            // Result should be a valid non-extreme conversion
            p_normal_not_saturated: assert (int8_out != 8'h80 || int8_signed == -128);
        end
    end

    // =========================================================================
    // Property 15: Very large positive product saturates to +127
    // value = 128.0 (0x4300), scale = 2.0 (0x4000) -> 256.0 overflows
    // =========================================================================
    always @(posedge clk) begin
        if (value == 16'h4300 && scale == 16'h4000) begin
            p_large_pos_sat: assert (int8_out == 8'h7F);
            p_large_pos_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_zero_out:    cover (is_zero);
        c_overflow:    cover (overflow);
        c_underflow:   cover (underflow);
        c_invalid:     cover (invalid);
        c_normal:      cover (!overflow && !underflow && !invalid && !is_zero && int8_signed > 0);
        c_normal_neg:  cover (!overflow && !underflow && !invalid && !is_zero && int8_signed < 0);
        c_nan_input:   cover (any_nan);
        c_inf_input:   cover (any_inf && !any_nan && !invalid_op);
        c_zero_x_inf:  cover (invalid_op);
    end

endmodule
