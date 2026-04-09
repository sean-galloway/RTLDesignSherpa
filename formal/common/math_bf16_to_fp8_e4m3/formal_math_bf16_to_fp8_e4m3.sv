// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_to_fp8_e4m3
//
// Verifies lossy BF16 -> FP8_E4M3 downconversion properties:
//   - Sign preservation
//   - NaN propagation (E4M3 NaN = {sign, 4'hF, 3'h7})
//   - Infinity saturates to max normal (E4M3 has no infinity)
//   - Zero preservation, subnormal/underflow flush-to-zero
//   - Flag consistency and mutual exclusivity

`timescale 1ns / 1ps

module formal_math_bf16_to_fp8_e4m3 (
    input logic clk
);

    (* anyconst *) logic [15:0] a;

    logic [7:0]  result;
    logic        overflow, underflow, invalid;

    math_bf16_to_fp8_e4m3 dut (
        .i_a          (a),
        .ow_result    (result),
        .ow_overflow  (overflow),
        .ow_underflow (underflow),
        .ow_invalid   (invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[15];
    wire [7:0]  exp_a  = a[14:7];
    wire [6:0]  mant_a = a[6:0];

    wire        sign_r = result[7];
    wire [3:0]  exp_r  = result[6:3];
    wire [2:0]  mant_r = result[2:0];

    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 7'h0);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 7'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 7'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 7'h0);

    wire r_is_zero     = (exp_r == 4'h0) && (mant_r == 3'h0);
    wire r_is_nan      = (exp_r == 4'hF) && (mant_r == 3'h7);
    // E4M3 max normal: {sign, 4'hF, 3'h6}
    wire r_is_max      = (exp_r == 4'hF) && (mant_r == 3'h6);

    // =========================================================================
    // Properties
    // =========================================================================
    always @(posedge clk) begin
        p_sign_preserved: assert (sign_r == sign_a);
    end

    always @(posedge clk) begin
        if (a_is_nan) begin
            p_nan_out: assert (r_is_nan);
            p_nan_invalid: assert (invalid);
        end
    end

    // E4M3 has no infinity - inf input saturates to max normal
    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_saturates: assert (r_is_max);
        end
    end

    always @(posedge clk) begin
        if (a_is_zero) begin
            p_zero_preserved: assert (r_is_zero);
        end
    end

    always @(posedge clk) begin
        if (a_is_subnorm) begin
            p_subnorm_ftz: assert (r_is_zero);
        end
    end

    // Overflow saturates to max normal (not infinity - E4M3 has none)
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_saturates: assert (r_is_max);
        end
    end

    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // Normal result: exponent in [1, 14] (E4M3 max biased exp for normal = 14)
    // exp=15 with mant<7 is also normal in E4M3
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_nan) begin
            p_normal_exp_range: assert (exp_r >= 4'h1);
        end
    end

    // Result is never the NaN pattern unless input was NaN
    always @(posedge clk) begin
        if (!a_is_nan) begin
            p_no_spurious_nan: assert (!r_is_nan);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal: cover (!a_is_zero && !a_is_subnorm && !a_is_inf && !a_is_nan && !overflow && !underflow);
        c_overflow: cover (overflow);
        c_underflow: cover (underflow);
        c_nan: cover (a_is_nan);
        c_inf: cover (a_is_inf);
    end

endmodule
