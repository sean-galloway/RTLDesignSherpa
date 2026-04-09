// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp32_to_bf16
//
// Verifies lossy FP32 -> BF16 downconversion properties:
//   - Sign preservation
//   - NaN propagation
//   - Infinity preservation / overflow to infinity
//   - Zero preservation (including subnormal/underflow flush-to-zero)
//   - Flag consistency (overflow, underflow, invalid)
//   - Flags mutually exclusive
//   - Output format validity

`timescale 1ns / 1ps

module formal_math_fp32_to_bf16 (
    input logic clk
);

    (* anyconst *) logic [31:0] a;

    logic [15:0] result;
    logic        overflow, underflow, invalid;

    math_fp32_to_bf16 dut (
        .i_a          (a),
        .ow_result    (result),
        .ow_overflow  (overflow),
        .ow_underflow (underflow),
        .ow_invalid   (invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a = a[31];
    wire [7:0]  exp_a  = a[30:23];
    wire [22:0] mant_a = a[22:0];

    wire        sign_r = result[15];
    wire [7:0]  exp_r  = result[14:7];
    wire [6:0]  mant_r = result[6:0];

    // Input classification
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 23'h0);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 23'h0);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 23'h0);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 23'h0);
    wire a_is_normal   = !a_is_zero && !a_is_subnorm && !a_is_inf && !a_is_nan;

    // Output classification
    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 7'h0);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 7'h0);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 7'h0);

    // =========================================================================
    // Property 1: Sign always preserved
    // =========================================================================
    always @(posedge clk) begin
        p_sign_preserved: assert (sign_r == sign_a);
    end

    // =========================================================================
    // Property 2: NaN propagation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_nan) begin
            p_nan_out: assert (r_is_nan);
            p_nan_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Infinity preservation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_preserved: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 4: Zero preservation
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_zero) begin
            p_zero_preserved: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 5: Subnormal flush to zero
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm) begin
            p_subnorm_ftz: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 6: Overflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 7: Underflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 8: Invalid flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 9: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 10: Normal result has valid exponent
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan) begin
            p_normal_exp_range: assert (exp_r >= 8'h01 && exp_r <= 8'hFE);
        end
    end

    // =========================================================================
    // Property 11: Inf input does not set overflow flag
    // (overflow is only for normal inputs that exceeded range)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf) begin
            p_inf_no_overflow: assert (!overflow);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal: cover (a_is_normal && !overflow && !underflow && !invalid);
        c_overflow: cover (overflow);
        // c_underflow removed: FP32 and BF16 share 8-bit exponent with same bias,
        // so FP32 normal values can never underflow to BF16
        c_invalid: cover (invalid);
        c_nan: cover (a_is_nan);
        c_inf: cover (a_is_inf);
        c_zero: cover (a_is_zero);
    end

endmodule
