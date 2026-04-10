// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_exponent_adder
//
// Verifies FP8 E5M2 exponent addition with bias handling:
//   - Overflow detection (result > 30)
//   - Underflow detection (result < 1)
//   - Special case flags (zero, inf)
//   - Normal result in valid range [1, 30]
//   - Saturation behavior on overflow/underflow
//
// FP8 E5M2 format: bias=15, 5-bit exponent
// exp=31 is infinity (mant=0) or NaN (mant!=0) -- RESERVED
// Valid normal range: [1, 30]

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_exponent_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs (fully enumerable: 2^11 = 2048 states)
    // =========================================================================
    (* anyconst *) logic [4:0] exp_a;
    (* anyconst *) logic [4:0] exp_b;
    (* anyconst *) logic       norm_adjust;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [4:0] exp_out;
    logic       overflow, underflow;
    logic       a_is_zero, b_is_zero;
    logic       a_is_inf, b_is_inf;

    math_fp8_e5m2_exponent_adder dut (
        .i_exp_a       (exp_a),
        .i_exp_b       (exp_b),
        .i_norm_adjust (norm_adjust),
        .ow_exp_out    (exp_out),
        .ow_overflow   (overflow),
        .ow_underflow  (underflow),
        .ow_a_is_zero  (a_is_zero),
        .ow_b_is_zero  (b_is_zero),
        .ow_a_is_inf   (a_is_inf),
        .ow_b_is_inf   (b_is_inf)
    );

    // =========================================================================
    // Reference model: compute expected raw sum
    // ref = exp_a + exp_b - 15 + norm_adjust
    // =========================================================================
    wire signed [7:0] ref_sum_raw = $signed({3'b0, exp_a}) + $signed({3'b0, exp_b})
                                  + $signed({7'b0, norm_adjust}) - 8'sd15;
    wire ref_underflow_raw = ref_sum_raw[7] | (ref_sum_raw < 8'sd1);
    wire ref_overflow_raw  = ~ref_underflow_raw & (ref_sum_raw > 8'sd30);

    // =========================================================================
    // Property 1: Zero detection correctness
    // =========================================================================
    always @(posedge clk) begin
        p_a_zero: assert (a_is_zero == (exp_a == 5'h00));
        p_b_zero: assert (b_is_zero == (exp_b == 5'h00));
    end

    // =========================================================================
    // Property 2: Infinity detection correctness (exp==0x1F, mantissa check external)
    // =========================================================================
    always @(posedge clk) begin
        p_a_inf: assert (a_is_inf == (exp_a == 5'h1F));
        p_b_inf: assert (b_is_inf == (exp_b == 5'h1F));
    end

    // =========================================================================
    // Property 3: Overflow detection
    // raw sum > 30 -> overflow
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
    // Property 5: Overflow saturates to 0x1F
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_sat: assert (exp_out == 5'h1F);
        end
    end

    // =========================================================================
    // Property 6: Underflow saturates to 0x00
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_sat: assert (exp_out == 5'h00);
        end
    end

    // =========================================================================
    // Property 7: Normal result in valid range [1, 30]
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow) begin
            p_normal_range: assert (exp_out >= 5'h01 && exp_out <= 5'h1E);
        end
    end

    // =========================================================================
    // Property 8: Overflow and underflow are mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_mutex: assert (!(overflow && underflow));
    end

    // =========================================================================
    // Property 9: Known vector: exp=15 + exp=15 - 15 = 15 (1.0 * 1.0 exponent)
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 5'd15 && exp_b == 5'd15 && !norm_adjust) begin
            p_one_times_one_exp: assert (exp_out == 5'd15);
            p_one_times_one_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 10: Known vector: exp=15 + exp=15 - 15 + 1 = 16 (with norm adjust)
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 5'd15 && exp_b == 5'd15 && norm_adjust) begin
            p_norm_adjust_exp: assert (exp_out == 5'd16);
            p_norm_adjust_no_flags: assert (!overflow && !underflow);
        end
    end

    // =========================================================================
    // Property 11: Known vector: max exponents overflow
    // exp=30 + exp=30 - 15 = 45 > 30 -> overflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 5'd30 && exp_b == 5'd30 && !norm_adjust) begin
            p_max_exp_overflow: assert (overflow);
        end
    end

    // =========================================================================
    // Property 12: Known vector: min exponents underflow
    // exp=1 + exp=1 - 15 = -13 -> underflow
    // =========================================================================
    always @(posedge clk) begin
        if (exp_a == 5'd1 && exp_b == 5'd1 && !norm_adjust) begin
            p_min_exp_underflow: assert (underflow);
        end
    end

    // =========================================================================
    // Property 13: Normal result matches raw computation
    // =========================================================================
    always @(posedge clk) begin
        if (!overflow && !underflow) begin
            p_normal_value: assert (exp_out == ref_sum_raw[4:0]);
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
        c_inf_a:        cover (a_is_inf);
        c_norm_adjust:  cover (norm_adjust && !overflow && !underflow);
    end

endmodule
