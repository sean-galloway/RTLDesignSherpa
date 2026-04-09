// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_to_fp16
//
// Verifies BF16 -> FP16 conversion properties (exponent range narrowing):
//   - Sign preservation
//   - NaN/Inf/Zero preservation
//   - Overflow to infinity, underflow to zero
//   - Flag consistency and mutual exclusivity

`timescale 1ns / 1ps

module formal_math_bf16_to_fp16 (
    input logic clk
);

    (* anyconst *) logic [15:0] a;

    logic [15:0] result;
    logic        overflow, underflow, invalid;

    math_bf16_to_fp16 dut (
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

    wire        sign_r = result[15];
    wire [4:0]  exp_r  = result[14:10];
    wire [9:0]  mant_r = result[9:0];

    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 7'h0);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 7'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 7'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 7'h0);

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 10'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 10'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 10'h0);

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

    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_preserved: assert (r_is_inf);
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

    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
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

    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan) begin
            p_normal_exp_range: assert (exp_r >= 5'h01 && exp_r <= 5'h1E);
        end
    end

    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_no_overflow: assert (!overflow);
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
