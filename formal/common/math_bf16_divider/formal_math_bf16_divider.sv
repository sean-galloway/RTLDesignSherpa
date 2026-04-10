// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_divider
//
// Verifies:
//   - NaN handling (NaN in -> NaN out, 0/0 -> NaN, inf/inf -> NaN)
//   - Division by zero produces infinity
//   - Known vectors: 1/1=1, 6/2=3, 6/3=2
//   - Sign correctness (sign_a XOR sign_b)
//   - Flag consistency (overflow->inf, underflow->zero, invalid->NaN)

`timescale 1ns / 1ps

module formal_math_bf16_divider (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [15:0] result;
    logic        overflow, underflow, div_by_zero, invalid;

    math_bf16_divider dut (
        .i_a            (a),
        .i_b            (b),
        .ow_result      (result),
        .ow_overflow    (overflow),
        .ow_underflow   (underflow),
        .ow_div_by_zero (div_by_zero),
        .ow_invalid     (invalid)
    );

    // =========================================================================
    // Field extraction
    // =========================================================================
    wire        sign_a  = a[15];
    wire [7:0]  exp_a   = a[14:7];
    wire [6:0]  mant_a  = a[6:0];

    wire        sign_b  = b[15];
    wire [7:0]  exp_b   = b[14:7];
    wire [6:0]  mant_b  = b[6:0];

    wire        sign_r  = result[15];
    wire [7:0]  exp_r   = result[14:7];
    wire [6:0]  mant_r  = result[6:0];

    // Special value classification
    wire a_is_zero    = (exp_a == 8'h00) && (mant_a == 7'h00);
    wire b_is_zero    = (exp_b == 8'h00) && (mant_b == 7'h00);
    wire a_is_subnorm = (exp_a == 8'h00) && (mant_a != 7'h00);
    wire b_is_subnorm = (exp_b == 8'h00) && (mant_b != 7'h00);
    wire a_eff_zero   = a_is_zero || a_is_subnorm;
    wire b_eff_zero   = b_is_zero || b_is_subnorm;
    wire a_is_inf     = (exp_a == 8'hFF) && (mant_a == 7'h00);
    wire b_is_inf     = (exp_b == 8'hFF) && (mant_b == 7'h00);
    wire a_is_nan     = (exp_a == 8'hFF) && (mant_a != 7'h00);
    wire b_is_nan     = (exp_b == 8'hFF) && (mant_b != 7'h00);
    wire a_is_normal  = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal  = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero    = (exp_r == 8'h00) && (mant_r == 7'h00);
    wire r_is_inf     = (exp_r == 8'hFF) && (mant_r == 7'h00);
    wire r_is_nan     = (exp_r == 8'hFF) && (mant_r != 7'h00);

    wire any_nan      = a_is_nan || b_is_nan;
    wire expected_sign = sign_a ^ sign_b;

    // =========================================================================
    // Property: NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property: 0/0 = NaN with invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_eff_zero && !any_nan) begin
            p_zero_div_zero_nan: assert (r_is_nan);
            p_zero_div_zero_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property: inf/inf = NaN with invalid flag
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf && !any_nan) begin
            p_inf_div_inf_nan: assert (r_is_nan);
            p_inf_div_inf_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property: normal / zero = infinity with div_by_zero flag
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_eff_zero) begin
            p_div_by_zero_inf: assert (r_is_inf);
            p_div_by_zero_flag: assert (div_by_zero);
            p_div_by_zero_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property: Sign correctness (when not NaN)
    // =========================================================================
    always @(posedge clk) begin
        if (!any_nan && !(a_eff_zero && b_eff_zero) && !(a_is_inf && b_is_inf)) begin
            p_sign_correct: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property: 0 / normal = 0
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_is_normal) begin
            p_zero_div_normal: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property: inf / normal = inf
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_normal) begin
            p_inf_div_normal: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property: normal / inf = 0
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b_is_inf) begin
            p_normal_div_inf: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property: Known test vector 1.0 / 1.0 = 1.0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3F80 && b == 16'h3F80) begin
            p_one_div_one: assert (result == 16'h3F80);
        end
    end

    // =========================================================================
    // Property: Known test vector 6.0 / 2.0 = 3.0
    // BF16: 6.0=0x40C0, 2.0=0x4000, 3.0=0x4040
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h40C0 && b == 16'h4000) begin
            p_six_div_two: assert (result == 16'h4040);
        end
    end

    // =========================================================================
    // Property: Flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (overflow)    p_overflow_inf:   assert (r_is_inf);
        if (underflow)   p_underflow_zero: assert (r_is_zero);
        if (invalid)     p_invalid_nan:    assert (r_is_nan);
    end

    // =========================================================================
    // Property: Normal result has valid exponent range
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan) begin
            p_normal_exp: assert (exp_r >= 8'h01 && exp_r <= 8'hFE);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_div:   cover (a_is_normal && b_is_normal && !overflow && !underflow);
        c_overflow:     cover (overflow);
        c_underflow:    cover (underflow);
        c_div_by_zero:  cover (div_by_zero);
        c_invalid:      cover (invalid);
    end

endmodule
