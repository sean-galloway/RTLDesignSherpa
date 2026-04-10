// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e5m2_multiplier
//
// Verifies structural IEEE 754 FP8 E5M2 multiplication properties:
//   - Sign correctness (sign_a XOR sign_b)
//   - Special value handling (zero, infinity, NaN)
//   - Known test vectors (1.0 * 1.0 = 1.0, etc.)
//   - Overflow/underflow flag consistency
//   - Result format validity
//
// FP8 E5M2 format: [7]=sign, [6:2]=exp (5 bits), [1:0]=mant (2 bits)
// Bias = 15
// Has infinity: exp=31, mant=0
// Has NaN:      exp=31, mant!=0
// Max normal:   exp=30, mant=3
// On overflow:  produces infinity

`timescale 1ns / 1ps

module formal_math_fp8_e5m2_multiplier (
    input logic clk
);

    // =========================================================================
    // Free inputs (8-bit each, fully enumerable)
    // =========================================================================
    (* anyconst *) logic [7:0] a;
    (* anyconst *) logic [7:0] b;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] result;
    logic       overflow, underflow, invalid;

    math_fp8_e5m2_multiplier dut (
        .i_a         (a),
        .i_b         (b),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP8 E5M2 field extraction
    // =========================================================================
    wire       sign_a = a[7];
    wire [4:0] exp_a  = a[6:2];
    wire [1:0] mant_a = a[1:0];

    wire       sign_b = b[7];
    wire [4:0] exp_b  = b[6:2];
    wire [1:0] mant_b = b[1:0];

    wire       sign_r = result[7];
    wire [4:0] exp_r  = result[6:2];
    wire [1:0] mant_r = result[1:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 5'h00) && (mant_a == 2'h0);
    wire b_is_zero     = (exp_b == 5'h00) && (mant_b == 2'h0);
    wire a_is_subnorm  = (exp_a == 5'h00) && (mant_a != 2'h0);
    wire b_is_subnorm  = (exp_b == 5'h00) && (mant_b != 2'h0);
    wire a_is_inf      = (exp_a == 5'h1F) && (mant_a == 2'h0);
    wire b_is_inf      = (exp_b == 5'h1F) && (mant_b == 2'h0);
    wire a_is_nan      = (exp_a == 5'h1F) && (mant_a != 2'h0);
    wire b_is_nan      = (exp_b == 5'h1F) && (mant_b != 2'h0);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_inf && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_inf && !b_is_nan;

    wire r_is_zero     = (exp_r == 5'h00) && (mant_r == 2'h0);
    wire r_is_inf      = (exp_r == 5'h1F) && (mant_r == 2'h0);
    wire r_is_nan      = (exp_r == 5'h1F) && (mant_r != 2'h0);

    wire any_nan       = a_is_nan || b_is_nan;
    wire invalid_op    = (a_eff_zero && b_is_inf) || (b_eff_zero && a_is_inf);

    // Expected result sign for multiplication
    wire expected_sign = sign_a ^ sign_b;

    // =========================================================================
    // Property 1: Sign correctness
    // Result sign = sign_a XOR sign_b (except canonical NaN for invalid op)
    // =========================================================================
    always @(posedge clk) begin
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
    // Property 4: Zero input produces zero output (SAME BUG CHECK AS BF16!)
    // Zero * normal = zero with correct sign. Zero check must have priority
    // over any spurious overflow from the exponent adder.
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
    // Property 4b: Strict zero encoding
    // =========================================================================
    always @(posedge clk) begin
        if ((a_eff_zero || b_eff_zero) && !any_nan && !invalid_op) begin
            p_zero_strict: assert (result == {expected_sign, 5'h00, 2'h0});
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
    // Property 7: Known vector: 1.0 * 1.0 = 1.0
    // FP8 E5M2 1.0: sign=0, exp=15 (bias), mant=0 -> 0x3C
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h3C && b == 8'h3C) begin
            p_one_times_one: assert (result == 8'h3C);
        end
    end

    // =========================================================================
    // Property 8: Known vector: 2.0 * 2.0 = 4.0
    // 2.0: exp=16, mant=0 -> 0x40
    // 4.0: exp=17, mant=0 -> 0x44
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h40) begin
            p_two_times_two: assert (result == 8'h44);
        end
    end

    // =========================================================================
    // Property 9: Known vector: -1.0 * 1.0 = -1.0
    // -1.0 = 0xBC, 1.0 = 0x3C
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'hBC && b == 8'h3C) begin
            p_neg_one_times_one: assert (result == 8'hBC);
        end
    end

    // =========================================================================
    // Property 10: Known vector: -1.0 * -1.0 = 1.0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'hBC && b == 8'hBC) begin
            p_neg_one_times_neg_one: assert (result == 8'h3C);
        end
    end

    // =========================================================================
    // Property 11: Overflow flag consistency
    // Overflow flag -> result is infinity
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_implies_inf: assert (r_is_inf);
        end
    end

    // =========================================================================
    // Property 12: Underflow flag consistency
    // Underflow flag -> result is zero
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 13: Invalid flag consistency
    // Invalid flag -> result is NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 14: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 15: Subnormal inputs flushed to zero (FTZ mode)
    // subnorm * normal = zero
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
    // Normal result: exp in [1, 30] range
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_inf && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 5'h01 && exp_r <= 5'h1E);
        end
    end

    // =========================================================================
    // Cover properties: ensure interesting scenarios are reachable
    // =========================================================================
    always @(posedge clk) begin
        c_normal_mult: cover (a_is_normal && b_is_normal && !overflow && !underflow && !invalid);
        c_overflow:    cover (overflow);
        c_underflow:   cover (underflow);
        c_invalid:     cover (invalid);
        c_nan_input:   cover (any_nan);
        c_inf_from_normal: cover (a_is_normal && b_is_normal && r_is_inf);
        c_zero_from_normal: cover (a_is_normal && b_is_normal && r_is_zero);
    end

endmodule
