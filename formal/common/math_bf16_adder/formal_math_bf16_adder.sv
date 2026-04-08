// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_adder
//
// Verifies structural IEEE 754 BF16 addition properties:
//   - Identity: a + 0 = a
//   - Additive inverse: a + (-a) = 0
//   - NaN propagation
//   - Infinity handling (inf + x, inf - inf)
//   - Known test vectors
//   - Flag consistency
//
// Uses combinational mode (all pipeline stages = 0) to keep BMC depth low.
// The adder is 707 lines with barrel shifters and CLZ -- focus on structural
// properties rather than full IEEE compliance.

`timescale 1ns / 1ps

module formal_math_bf16_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;

    // =========================================================================
    // DUT instantiation (combinational mode: all pipeline stages = 0)
    // =========================================================================
    logic [15:0] result;
    logic        overflow, underflow, invalid, valid_out;

    math_bf16_adder #(
        .PIPE_STAGE_1(0),
        .PIPE_STAGE_2(0),
        .PIPE_STAGE_3(0),
        .PIPE_STAGE_4(0)
    ) dut (
        .i_clk       (clk),
        .i_rst_n     (1'b1),
        .i_a         (a),
        .i_b         (b),
        .i_valid     (1'b1),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid),
        .ow_valid    (valid_out)
    );

    // =========================================================================
    // BF16 field extraction
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
    wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 7'h00);
    wire b_is_zero     = (exp_b == 8'h00) && (mant_b == 7'h00);
    wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 7'h00);
    wire b_is_subnorm  = (exp_b == 8'h00) && (mant_b != 7'h00);
    wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 7'h00);
    wire b_is_inf      = (exp_b == 8'hFF) && (mant_b == 7'h00);
    wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 7'h00);
    wire b_is_nan      = (exp_b == 8'hFF) && (mant_b != 7'h00);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero     = (exp_r == 8'h00) && (mant_r == 7'h00);
    wire r_is_inf      = (exp_r == 8'hFF) && (mant_r == 7'h00);
    wire r_is_nan      = (exp_r == 8'hFF) && (mant_r != 7'h00);

    wire any_nan       = a_is_nan || b_is_nan;
    wire inf_minus_inf = a_is_inf && b_is_inf && (sign_a != sign_b);
    wire any_special   = any_nan || a_is_inf || b_is_inf || a_eff_zero || b_eff_zero;

    // Negation of b: flip sign bit only
    wire [15:0] neg_b = {~b[15], b[14:0]};

    // =========================================================================
    // Property 1: NaN propagation
    // Any NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 2: Infinity minus infinity = NaN
    // inf + (-inf) is an invalid operation
    // =========================================================================
    always @(posedge clk) begin
        if (inf_minus_inf && !any_nan) begin
            p_inf_minus_inf_nan: assert (r_is_nan);
            p_inf_minus_inf_invalid: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Identity -- a + (+0) = a for normal numbers
    // +0 in BF16 = 16'h0000
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == 16'h0000) begin
            p_add_pos_zero: assert (result == a);
        end
    end

    // =========================================================================
    // Property 4: Identity -- (+0) + b = b for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_normal && a == 16'h0000) begin
            p_zero_plus_b: assert (result == b);
        end
    end

    // =========================================================================
    // Property 5: Additive inverse -- a + (-a) = +0 for normal numbers
    // Per IEEE 754 RNE mode, x - x = +0
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == neg_b && a[14:0] == b[14:0] && sign_a != sign_b) begin
            p_additive_inverse: assert (result == 16'h0000);
        end
    end

    // =========================================================================
    // Property 6: Infinity + normal = infinity (preserving sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && !b_is_inf && !b_is_nan) begin
            p_inf_plus_normal: assert (r_is_inf);
            p_inf_plus_normal_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 7: normal + infinity = infinity (preserving sign)
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_inf && !a_is_inf && !a_is_nan) begin
            p_normal_plus_inf: assert (r_is_inf);
            p_normal_plus_inf_sign: assert (sign_r == sign_b);
        end
    end

    // =========================================================================
    // Property 8: inf + inf (same sign) = inf (same sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf && sign_a == sign_b) begin
            p_inf_plus_inf: assert (r_is_inf);
            p_inf_plus_inf_sign: assert (sign_r == sign_a);
        end
    end

    // =========================================================================
    // Property 9: Both inputs zero
    // 0 + 0 = 0; -0 + -0 = -0; +0 + -0 = +0
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_eff_zero) begin
            p_both_zero: assert (r_is_zero);
            p_both_zero_sign: assert (sign_r == (sign_a & sign_b));
        end
    end

    // =========================================================================
    // Property 10: Known test vector: 1.0 + 1.0 = 2.0
    // BF16: 1.0 = 0x3F80, 2.0 = 0x4000
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3F80 && b == 16'h3F80) begin
            p_one_plus_one: assert (result == 16'h4000);
        end
    end

    // =========================================================================
    // Property 11: Known test vector: 1.0 + (-1.0) = 0.0
    // BF16: 1.0 = 0x3F80, -1.0 = 0xBF80
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3F80 && b == 16'hBF80) begin
            p_one_minus_one: assert (result == 16'h0000);
        end
    end

    // =========================================================================
    // Property 12: Known test vector: 3.0 + 4.0 = 7.0
    // BF16: 3.0 = 0x4040, 4.0 = 0x4080, 7.0 = 0x40E0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h4040 && b == 16'h4080) begin
            p_three_plus_four: assert (result == 16'h40E0);
        end
    end

    // =========================================================================
    // Property 13: Overflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 14: Underflow flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 15: Invalid flag consistency
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 16: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 17: Valid output tracks valid input (combinational mode)
    // =========================================================================
    always @(posedge clk) begin
        p_valid_passthrough: assert (valid_out == 1'b1);
    end

    // =========================================================================
    // Property 18: Result exponent validity for normal results
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 8'h01 && exp_r <= 8'hFE);
        end
    end

    // =========================================================================
    // Property 19: Subnormal inputs treated as zero (FTZ mode)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm && b_is_normal) begin
            // subnorm + normal = normal (subnorm flushed to zero)
            p_subnorm_a_identity: assert (result[14:0] == b[14:0]);
        end
        if (b_is_subnorm && a_is_normal) begin
            p_subnorm_b_identity: assert (result[14:0] == a[14:0]);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        // Normal addition
        c_normal_add: cover (a_is_normal && b_is_normal && !overflow && !underflow);

        // Normal subtraction (different signs)
        c_normal_sub: cover (a_is_normal && b_is_normal && sign_a != sign_b && !r_is_zero);

        // Exact zero from subtraction
        c_exact_zero: cover (a_is_normal && b_is_normal && r_is_zero);

        // Overflow
        c_overflow: cover (overflow);

        // Underflow
        c_underflow: cover (underflow);

        // NaN result
        c_nan: cover (r_is_nan);

        // Infinity from overflow
        c_inf_overflow: cover (a_is_normal && b_is_normal && r_is_inf);
    end

endmodule
