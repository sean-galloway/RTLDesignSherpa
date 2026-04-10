// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_exponent_adder
//
// Verifies FP8 E4M3 exponent addition with bias handling:
//   - Overflow detection (result > 15)
//   - Underflow detection (result < 1)
//   - Special case flags (zero, nan)
//   - Normal result in valid range [1, 15]
//   - Saturation behavior on overflow/underflow
//
// FP8 E4M3 format: bias=7, 4-bit exponent, valid range [1,15]
// Note: E4M3 has no infinity - exp=15 is valid for max normal value.
// NaN is encoded only as {sign, 4'hF, 3'h7}; mantissa check is external.

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_exponent_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs (fully enumerable: 2^9 = 512 states)
    // =========================================================================
    (* anyconst *) logic [3:0] exp_a;
    (* anyconst *) logic [3:0] exp_b;
    (* anyconst *) logic       norm_adjust;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [3:0] exp_out;
    logic       overflow, underflow;
    logic       a_is_zero, b_is_zero;
    logic       a_is_nan, b_is_nan;

    math_fp8_e4m3_exponent_adder dut (
        .i_exp_a       (exp_a),
        .i_exp_b       (exp_b),
        .i_norm_adjust (norm_adjust),
        .ow_exp_out    (exp_out),
        .ow_overflow   (overflow),
        .ow_underflow  (underflow),
        .ow_a_is_zero  (a_is_zero),
        .ow_b_is_zero  (b_is_zero),
        .ow_a_is_nan   (a_is_nan),
        .ow_b_is_nan   (b_is_nan)
    );

    // =========================================================================
    // Reference model: compute expected raw sum
    // ref = exp_a + exp_b - 7 + norm_adjust
    // =========================================================================
    wire signed [6:0] ref_sum_raw = $signed({3'b0, exp_a}) + $signed({3'b0, exp_b})
                                  + $signed({6'b0, norm_adjust}) - 7'sd7;
    wire ref_underflow_raw = ref_sum_raw[6] | (ref_sum_raw < 7'sd1);
    wire ref_overflow_raw  = ~ref_underflow_raw & (ref_sum_raw > 7'sd15);

    // =========================================================================
    // Property 1: Zero detection correctness
    // =========================================================================
    always @(posedge clk) begin
        p_a_zero: assert (a_is_zero == (exp_a == 4'h0));
        p_b_zero: assert (b_is_zero == (exp_b == 4'h0));
    end

    // =========================================================================
    // Property 2: NaN detection correctness (exp==0xF; mantissa check external)
    // =========================================================================
    always @(posedge clk) begin
        p_a_nan: assert (a_is_nan == (exp_a == 4'hF));
        p_b_nan: assert (b_is_nan == (exp_b == 4'hF));
    end

    // =========================================================================
    // Property 3: Overflow detection
    // raw sum > 15 -> overflow
    // =========================================================================
    always @(posedge clk) begin
        p_overflow_detect: assert (overflow == ref_overflow_raw);
    end

    // =========================================================================
    // Property 4: Underflow detection
    // raw sum < 1 -> underflow
    // =========================================================================
    always @(posedge clk) begin
        p_underflow_detect: assert (underflow == ref_underflow_raw);
    end

    // =========================================================================
    // Property 5: Overflow saturates to 0xF
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_sat: assert (exp_out == 4'hF);
        end
    end

    // =========================================================================
    // Property 6: Underflow saturates to 0x0
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_sat: assert (exp_out == 4'h0);
        end
    end

    // =========================================================================
    // Property 7: Normal result in valid range [1, 15]
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow) begin
            p_normal_range: assert (exp_out >= 4'h1 && exp_out <= 4'hF);
        end
    end

    // =========================================================================
    // Property 8: Overflow and underflow are mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_mutex: assert (!(overflow && underflow));
    end

    // =========================================================================
    // Property 9: Known vector: exp=7 + exp=7 - 7 = 7 (1.0 * 1.0 exponent)
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 4'd7 && exp_b == 4'd7 && !norm_adjust) begin
            p_one_times_one_exp: assert (exp_out == 4'd7);
            p_one_times_one_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 10: Known vector: exp=7 + exp=7 - 7 + 1 = 8 (with norm adjust)
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 4'd7 && exp_b == 4'd7 && norm_adjust) begin
            p_norm_adjust_exp: assert (exp_out == 4'd8);
            p_norm_adjust_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 11: Known vector: max exponents overflow
    // exp=15 + exp=15 - 7 = 23 > 15 -> overflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 4'd15 && exp_b == 4'd15 && !norm_adjust) begin
            p_max_exp_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Property 12: Known vector: min exponents underflow
    // exp=1 + exp=1 - 7 = -5 -> underflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 4'd1 && exp_b == 4'd1 && !norm_adjust) begin
            p_min_exp_underflow: assert (underflow);
        end
    end

    // =========================================================================
    // Property 13: Normal result matches raw computation
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow) begin
            p_normal_value: assert (exp_out == ref_sum_raw[3:0]);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_overflow:     cover (overflow);
        c_underflow:    cover (underflow);
        c_normal:       cover (!overflow && !underflow);
        c_zero_a:       cover (a_is_zero);
        c_nan_a:        cover (a_is_nan);
        c_norm_adjust:  cover (norm_adjust && !overflow && !underflow);
    end

endmodule
