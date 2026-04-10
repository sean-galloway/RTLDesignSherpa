// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_ieee754_2008_fp32_exponent_adder
//
// Verifies FP32 exponent addition with bias handling:
//   - Overflow detection (result > 254)
//   - Underflow detection (result <= 0)
//   - Special case flags (zero, inf, nan)
//   - Normal result in valid range [1, 254]
//   - Saturation behavior on overflow/underflow
//   - Bias = 127 per IEEE 754-2008 FP32

`timescale 1ns / 1ps

module formal_math_ieee754_2008_fp32_exponent_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [7:0] exp_a;
    (* anyconst *) logic [7:0] exp_b;
    (* anyconst *) logic       norm_adjust;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] exp_out;
    logic       overflow, underflow;
    logic       a_is_zero, b_is_zero;
    logic       a_is_inf, b_is_inf;
    logic       a_is_nan, b_is_nan;

    math_ieee754_2008_fp32_exponent_adder dut (
        .i_exp_a       (exp_a),
        .i_exp_b       (exp_b),
        .i_norm_adjust (norm_adjust),
        .ow_exp_out    (exp_out),
        .ow_overflow   (overflow),
        .ow_underflow  (underflow),
        .ow_a_is_zero  (a_is_zero),
        .ow_b_is_zero  (b_is_zero),
        .ow_a_is_inf   (a_is_inf),
        .ow_b_is_inf   (b_is_inf),
        .ow_a_is_nan   (a_is_nan),
        .ow_b_is_nan   (b_is_nan)
    );

    // =========================================================================
    // Reference model (bias = 127)
    // =========================================================================
    wire [9:0] ref_sum_raw = {2'b0, exp_a} + {2'b0, exp_b} +
                             {9'b0, norm_adjust} - 10'd127;
    wire ref_underflow_raw = ref_sum_raw[9] | (ref_sum_raw == 10'd0);
    wire ref_overflow_raw  = ~ref_underflow_raw & (ref_sum_raw > 10'd254);
    wire either_special    = a_is_inf | b_is_inf | a_is_zero | b_is_zero;

    // =========================================================================
    // Property 1: Zero detection
    // =========================================================================
    always @(posedge clk) begin
        p_a_zero: assert (a_is_zero == (exp_a == 8'h00));
        p_b_zero: assert (b_is_zero == (exp_b == 8'h00));
    end

    // =========================================================================
    // Property 2: Inf/NaN detection
    // =========================================================================
    always @(posedge clk) begin
        p_a_inf: assert (a_is_inf == (exp_a == 8'hFF));
        p_b_inf: assert (b_is_inf == (exp_b == 8'hFF));
        p_a_nan: assert (a_is_nan == (exp_a == 8'hFF));
        p_b_nan: assert (b_is_nan == (exp_b == 8'hFF));
    end

    // =========================================================================
    // Property 3: Overflow detection
    // =========================================================================
    always @(posedge clk) begin
        if (!either_special) begin
            p_overflow_detect: assert (overflow == ref_overflow_raw);
        end
    end

    // =========================================================================
    // Property 4: Underflow detection
    // =========================================================================
    always @(posedge clk) begin
        if (!either_special) begin
            p_underflow_detect: assert (underflow == ref_underflow_raw);
        end
    end

    // =========================================================================
    // Property 5: Special cases suppress overflow/underflow
    // =========================================================================
    always @(posedge clk) begin
        if (either_special) begin
            p_special_no_overflow: assert (!overflow);
            p_special_no_underflow: assert (!underflow);
        end
    end

    // =========================================================================
    // Property 6: Overflow saturates to 0xFF
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_sat: assert (exp_out == 8'hFF);
        end
    end

    // =========================================================================
    // Property 7: Underflow saturates to 0x00
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_sat: assert (exp_out == 8'h00);
        end
    end

    // =========================================================================
    // Property 8: Normal result in [1, 254]
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow && !either_special) begin
            p_normal_range: assert (exp_out >= 8'h01 && exp_out <= 8'hFE);
        end
    end

    // =========================================================================
    // Property 9: Overflow/underflow mutex
    // =========================================================================
    always @(posedge clk) begin
        p_flags_mutex: assert (!(overflow && underflow));
    end

    // =========================================================================
    // Property 10: Known vector: exp=127 + exp=127 - 127 + 0 = 127 (1.0 * 1.0)
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 8'd127 && exp_b == 8'd127 && !norm_adjust) begin
            p_one_times_one_exp: assert (exp_out == 8'd127);
            p_one_times_one_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 11: Known vector: with norm adjust = 128
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 8'd127 && exp_b == 8'd127 && norm_adjust) begin
            p_norm_adjust_exp: assert (exp_out == 8'd128);
            p_norm_adjust_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 12: Max exponents -> overflow
    // exp=254 + exp=254 - 127 = 381 > 254 -> overflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 8'd254 && exp_b == 8'd254 && !norm_adjust) begin
            p_max_exp_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Property 13: Min exponents -> underflow
    // exp=1 + exp=1 - 127 = -125 -> underflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 8'd1 && exp_b == 8'd1 && !norm_adjust) begin
            p_min_exp_underflow: assert (underflow);
        end
    end

    // =========================================================================
    // Property 14: Normal result matches raw computation
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow && !either_special) begin
            p_normal_value: assert (exp_out == ref_sum_raw[7:0]);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_overflow:     cover (overflow);
        c_underflow:    cover (underflow);
        c_normal:       cover (!overflow && !underflow && !either_special);
        c_zero_a:       cover (a_is_zero);
        c_zero_b:       cover (b_is_zero);
        c_inf_a:        cover (a_is_inf);
        c_norm_adjust:  cover (norm_adjust && !overflow && !underflow && !either_special);
    end

endmodule
