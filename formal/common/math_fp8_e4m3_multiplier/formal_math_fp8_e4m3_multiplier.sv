// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_multiplier
//
// Verifies structural IEEE 754 FP8 E4M3 multiplication properties:
//   - Sign correctness (sign_a XOR sign_b)
//   - Special value handling (zero, NaN)
//   - Known test vectors (1.0 * 1.0 = 1.0, etc.)
//   - Overflow/underflow flag consistency
//   - Result format validity
//
// FP8 E4M3 format: [7]=sign, [6:3]=exp (4 bits), [2:0]=mant (3 bits)
// Bias = 7
// NaN encoding: exp==15 AND mant==7 only
// NO infinity encoding - max normal is S1111.110 (0x7E positive)
// On overflow: saturates to max normal

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_multiplier (
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

    math_fp8_e4m3_multiplier dut (
        .i_a         (a),
        .i_b         (b),
        .ow_result   (result),
        .ow_overflow (overflow),
        .ow_underflow(underflow),
        .ow_invalid  (invalid)
    );

    // =========================================================================
    // FP8 E4M3 field extraction
    // =========================================================================
    wire       sign_a = a[7];
    wire [3:0] exp_a  = a[6:3];
    wire [2:0] mant_a = a[2:0];

    wire       sign_b = b[7];
    wire [3:0] exp_b  = b[6:3];
    wire [2:0] mant_b = b[2:0];

    wire       sign_r = result[7];
    wire [3:0] exp_r  = result[6:3];
    wire [2:0] mant_r = result[2:0];

    // Special value classification
    wire a_is_zero     = (exp_a == 4'h0) && (mant_a == 3'h0);
    wire b_is_zero     = (exp_b == 4'h0) && (mant_b == 3'h0);
    wire a_is_subnorm  = (exp_a == 4'h0) && (mant_a != 3'h0);
    wire b_is_subnorm  = (exp_b == 4'h0) && (mant_b != 3'h0);
    // NaN: exp=15, mant=7 (only)
    wire a_is_nan      = (exp_a == 4'hF) && (mant_a == 3'h7);
    wire b_is_nan      = (exp_b == 4'hF) && (mant_b == 3'h7);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_nan;

    wire r_is_zero     = (exp_r == 4'h0) && (mant_r == 3'h0);
    wire r_is_nan      = (exp_r == 4'hF) && (mant_r == 3'h7);
    // Max normal value: S1111.110 (exp=15, mant=6)
    wire r_is_max_norm = (exp_r == 4'hF) && (mant_r == 3'h6);

    wire any_nan       = a_is_nan || b_is_nan;

    // Expected result sign for multiplication
    wire expected_sign = sign_a ^ sign_b;

    // =========================================================================
    // Property 1: Sign correctness
    // Result sign = sign_a XOR sign_b (except NaN which uses canonical form)
    // Note: The DUT forces NaN output to sign=expected_sign per its code.
    // =========================================================================
    always @(posedge clk) begin
        p_sign_xor: assert (sign_r == expected_sign);
    end

    // =========================================================================
    // Property 2: NaN propagation
    // Any NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
            p_nan_invalid_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 3: Zero input produces zero output (SAME BUG CHECK AS BF16!)
    // When a is effectively zero and b is not NaN, result must be zero.
    // Critical: the DUT checks w_any_nan before w_final_overflow before
    // w_result_zero. We need to ensure spurious overflow/nan don't mask zero.
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && !any_nan) begin
            p_zero_a_result: assert (r_is_zero);
            p_zero_a_sign: assert (sign_r == expected_sign);
        end
        if (b_eff_zero && !any_nan) begin
            p_zero_b_result: assert (r_is_zero);
            p_zero_b_sign: assert (sign_r == expected_sign);
        end
    end

    // =========================================================================
    // Property 3b: Strict zero encoding
    // =========================================================================
    always @(posedge clk) begin
        if ((a_eff_zero || b_eff_zero) && !any_nan) begin
            p_zero_strict: assert (result == {expected_sign, 4'h0, 3'h0});
        end
    end

    // =========================================================================
    // Property 4: Known vector: 1.0 * 1.0 = 1.0
    // FP8 E4M3 1.0: sign=0, exp=7 (bias), mant=0 -> 0x38
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h38 && b == 8'h38) begin
            p_one_times_one: assert (result == 8'h38);
        end
    end

    // =========================================================================
    // Property 5: Known vector: 2.0 * 2.0 = 4.0
    // 2.0 = exp=8, mant=0 -> 0x40
    // 4.0 = exp=9, mant=0 -> 0x48
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h40) begin
            p_two_times_two: assert (result == 8'h48);
        end
    end

    // =========================================================================
    // Property 6: Known vector: -1.0 * 1.0 = -1.0
    // -1.0 = 0xB8, 1.0 = 0x38
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'hB8 && b == 8'h38) begin
            p_neg_one_times_one: assert (result == 8'hB8);
        end
    end

    // =========================================================================
    // Property 7: Known vector: -1.0 * -1.0 = 1.0
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'hB8 && b == 8'hB8) begin
            p_neg_one_times_neg_one: assert (result == 8'h38);
        end
    end

    // =========================================================================
    // Property 8: Known vector: 2.0 * 3.0 = 6.0
    // 2.0 = 0x40 (exp=8, mant=0)
    // 3.0 = 0x44 (exp=8, mant=4, i.e. 1.5 * 2^1)
    // 6.0 = 0x4C (exp=9, mant=4, i.e. 1.5 * 2^2)
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h44) begin
            p_two_times_three: assert (result == 8'h4C);
        end
    end

    // =========================================================================
    // Property 9: Overflow flag -> result saturates to max normal
    // E4M3 has no infinity. Overflow produces max normal (exp=15, mant=6).
    // =========================================================================
    always @(posedge clk) begin
        if (overflow) begin
            p_overflow_max_norm: assert (r_is_max_norm);
        end
    end

    // =========================================================================
    // Property 10: Underflow flag -> result is zero
    // =========================================================================
    always @(posedge clk) begin
        if (underflow) begin
            p_underflow_implies_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 11: Invalid flag -> result is NaN
    // =========================================================================
    always @(posedge clk) begin
        if (invalid) begin
            p_invalid_implies_nan: assert (r_is_nan);
        end
    end

    // =========================================================================
    // Property 12: Flags mutually exclusive
    // =========================================================================
    always @(posedge clk) begin
        p_flags_exclusive: assert ((overflow + underflow + invalid) <= 1);
    end

    // =========================================================================
    // Property 13: Subnormal inputs flushed to zero (FTZ mode)
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
    // Property 14: Result exponent validity
    // Normal/non-special result: exp in [1, 15], and if exp=15 then mant < 7
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 4'h1 && exp_r <= 4'hF);
            // If exp=15, mant must not be 7 (that would be NaN)
            if (exp_r == 4'hF) begin
                p_no_nan_pattern: assert (mant_r != 3'h7);
            end
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_mult: cover (a_is_normal && b_is_normal && !overflow && !underflow && !invalid);
        c_overflow:    cover (overflow);
        c_underflow:   cover (underflow);
        c_invalid:     cover (invalid);
        c_nan_input:   cover (any_nan);
        c_max_from_normal: cover (a_is_normal && b_is_normal && r_is_max_norm);
        c_zero_from_normal: cover (a_is_normal && b_is_normal && r_is_zero);
    end

endmodule
