// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_to_fp8_e5m2
//
// Verifies FP8_E4M3 -> FP8_E5M2 conversion properties:
//   - Sign preservation
//   - NaN propagation (E4M3 NaN -> E5M2 NaN)
//   - E4M3 has no infinity; E5M2 has infinity
//   - Zero preservation, subnormal flush-to-zero
//   - Overflow to infinity (E5M2 has infinity)
//   - Flag consistency and mutual exclusivity

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_to_fp8_e5m2 (
    input logic clk
);

    (* anyconst *) logic [7:0] a;

    logic [7:0]  result;
    logic        overflow, underflow, invalid;

    math_fp8_e4m3_to_fp8_e5m2 dut (
        .i_a          (a),
        .ow_result    (result),
        .ow_overflow  (overflow),
        .ow_underflow (underflow),
        .ow_invalid   (invalid)
    );

    // E4M3 fields
    wire        sign_a = a[7];
    wire [3:0]  exp_a  = a[6:3];
    wire [2:0]  mant_a = a[2:0];

    // E5M2 fields
    wire        sign_r = result[7];
    wire [4:0]  exp_r  = result[6:2];
    wire [1:0]  mant_r = result[1:0];

    // E4M3 special values (no infinity, NaN = exp=0xF mant=0x7)
    wire a_is_zero     = (exp_a == 4'h0) && (mant_a == 3'h0);
    wire a_is_subnorm  = (exp_a == 4'h0) && (mant_a != 3'h0);
    wire a_is_nan      = (exp_a == 4'hF) && (mant_a == 3'h7);
    // E4M3 has no infinity, but the DUT checks for it defensively
    wire a_is_inf      = (exp_a == 4'hF) && (mant_a == 3'h0);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_nan && !a_is_inf;

    // E5M2 special values
    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 2'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 2'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 2'h0);

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
        c_normal: cover (a_is_normal && !overflow && !underflow);
        // c_overflow removed: E4M3 max biased exp=14, +8 bias diff = 22,
        // well within E5M2 range [1..30], so overflow is unreachable
        c_nan: cover (a_is_nan);
        c_zero: cover (a_is_zero);
    end

endmodule
