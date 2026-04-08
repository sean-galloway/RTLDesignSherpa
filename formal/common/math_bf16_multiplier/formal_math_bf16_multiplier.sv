// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_multiplier
//
// Verifies structural IEEE 754 BF16 multiplication properties:
//   - Sign correctness (sign_a XOR sign_b)
//   - Special value handling (zero, infinity, NaN)
//   - Known test vectors (1.0 * 1.0 = 1.0, etc.)
//   - Overflow/underflow flag consistency
//   - Result format validity

`timescale 1ns / 1ps

module formal_math_bf16_multiplier (
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
    logic        overflow, underflow, invalid;

    math_bf16_multiplier dut (
        .i_a         (a),
        .i_b         (b),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // BF16 field extraction (for assertions)
    // =========================================================================
    wire        sign_a   = a[15];
    wire [7:0]  exp_a    = a[14:7];
    wire [6:0]  mant_a   = a[6:0];

    wire        sign_b   = b[15];
    wire [7:0]  exp_b    = b[14:7];
    wire [6:0]  mant_b   = b[6:0];

    wire        sign_r   = result[15];
    wire [7:0]  exp_r    = result[14:7];
    wire [6:0]  mant_r   = result[6:0];

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
    wire invalid_op    = (a_eff_zero && b_is_inf) || (b_eff_zero && a_is_inf);
    wire any_special   = any_nan || a_is_inf || b_is_inf || a_eff_zero || b_eff_zero;

    // Expected result sign for multiplication
    wire expected_sign = sign_a ^ sign_b;

    // =========================================================================
    // Property 1: Sign correctness
    // For normal * normal (no special cases), sign = sign_a XOR sign_b
    // =========================================================================
    always @(posedge clk) begin
        // Sign of result is always XOR of input signs (even for special cases
        // like zero, infinity), EXCEPT for NaN which uses canonical form
        if (!any_nan && !invalid_op) begin
            p_sign_xor: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 2: NaN propagation
    // Any NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 3: Invalid operation (0 * inf = NaN)
    // =========================================================================
    always @(posedge clk) begin
        if (invalid_op && !any_nan) begin
            p_zero_times_inf_is_nan: assert (r_is_nan);
            p_invalid_flag_set: assert (invalid);
        end
    end

    // =========================================================================
    // Property 4: Zero input produces zero output
    // (when other input is normal, not inf/nan)
    //
    // Zero * normal = zero with correct sign. The DUT checks w_result_zero
    // before w_final_overflow in the priority cascade, so even when the
    // exponent adder produces a spurious 0xFF, the zero check takes priority.
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && !b_is_inf && !b_is_nan) begin
            p_zero_a_result: assert (r_is_zero);
            p_zero_a_sign: assert (sign_r == expected_sign);
        end
        if (b_eff_zero && !a_is_inf && !a_is_nan) begin
            p_zero_b_result: assert (r_is_zero);
            p_zero_b_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 4b: Strict zero assertion -- zero * normal = exactly zero
    // Verifies that the full result encoding is {sign, 8'h00, 7'h00}
    // =========================================================================
    always @(posedge clk) begin
        if ((a_eff_zero || b_eff_zero) && !any_nan && !invalid_op) begin
            p_zero_strict: assert (result == {expected_sign, 8'h00, 7'h00});
        end
    end

    // =========================================================================
    // Property 5: Infinity propagation
    // inf * normal = inf (with correct sign)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_normal) begin
            p_inf_a_result: assert (r_is_inf);
            p_inf_a_sign: assert (sign_r == expected_sign);
        end
        if (b_is_inf && a_is_normal) begin
            p_inf_b_result: assert (r_is_inf);
            p_inf_b_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 6: inf * inf = inf
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_inf && b_is_inf) begin
            p_inf_times_inf: assert (r_is_inf);
            p_inf_times_inf_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 7: Known test vector: 1.0 * 1.0 = 1.0
    // BF16 encoding of 1.0: sign=0, exp=127 (0x7F), mant=0x00
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h3F80 && b == 16'h3F80) begin
            p_one_times_one: assert (result == 16'h3F80);
        end
    end

    // =========================================================================
    // Property 8: Known test vector: 2.0 * 3.0 = 6.0
    // BF16: 2.0 = 0x4000, 3.0 = 0x4040, 6.0 = 0x40C0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'h4000 && b == 16'h4040) begin
            p_two_times_three: assert (result == 16'h40C0);
        end
    end

    // =========================================================================
    // Property 9: Known test vector: -1.0 * 1.0 = -1.0
    // BF16: -1.0 = 0xBF80
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'hBF80 && b == 16'h3F80) begin
            p_neg_one_times_one: assert (result == 16'hBF80);
        end
    end

    // =========================================================================
    // Property 10: Known test vector: -1.0 * -1.0 = 1.0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 16'hBF80 && b == 16'hBF80) begin
            p_neg_one_times_neg_one: assert (result == 16'h3F80);
        end
    end

    // =========================================================================
    // Property 11: Overflow flag consistency
    // Overflow flag set implies result is infinity
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 12: Underflow flag consistency
    // Underflow flag set implies result is zero
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 13: Invalid flag consistency
    // Invalid flag only set for 0 * inf
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 14: Flags are mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 15: Subnormal inputs flushed to zero (FTZ mode)
    // Subnormals are treated as effective zeros, so subnorm * normal = zero.
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm && b_is_normal) begin
            p_subnorm_a_ftz: assert (r_is_zero);
        end
        if (b_is_subnorm && a_is_normal) begin
            p_subnorm_b_ftz: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 16: Result exponent validity
    // Normal results must have exp in [1, 254] range
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 8'h01 && exp_r <= 8'hFE);
        end
    end

    // =========================================================================
    // Cover properties: ensure interesting scenarios are reachable
    // =========================================================================
    always @(posedge clk) begin
        // Normal * normal with no flags
        c_normal_mult: cover (a_is_normal && b_is_normal && !overflow && !underflow && !invalid);

        // Overflow case
        c_overflow: cover (overflow);

        // Underflow case
        c_underflow: cover (underflow);

        // Invalid operation
        c_invalid: cover (invalid);

        // NaN propagation
        c_nan_input: cover (any_nan);

        // Infinity result from normal inputs (overflow)
        c_inf_from_normal: cover (a_is_normal && b_is_normal && r_is_inf);

        // Zero result from normal inputs (underflow)
        c_zero_from_normal: cover (a_is_normal && b_is_normal && r_is_zero);
    end

endmodule
