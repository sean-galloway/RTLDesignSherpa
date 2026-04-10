// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_adder
//
// Verifies structural FP8 E4M3 addition properties:
//   - Identity: a + 0 = a
//   - Additive inverse: a + (-a) = 0
//   - NaN propagation
//   - Known test vectors
//   - Flag consistency
//
// FP8 E4M3 format: [7]=sign, [6:3]=exp (bias=7), [2:0]=mant
// NaN: exp=15, mant=7 only
// No infinity: overflow saturates to max normal (exp=15, mant=6)

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_adder (
    input logic clk
);

    // =========================================================================
    // Free inputs (8-bit each, fully enumerable: 2^16 = 65536 states)
    // =========================================================================
    (* anyconst *) logic [7:0] a;
    (* anyconst *) logic [7:0] b;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    logic [7:0] result;
    logic       overflow, underflow, invalid;

    math_fp8_e4m3_adder dut (
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
    wire a_is_nan      = (exp_a == 4'hF) && (mant_a == 3'h7);
    wire b_is_nan      = (exp_b == 4'hF) && (mant_b == 3'h7);
    wire a_eff_zero    = a_is_zero || a_is_subnorm;
    wire b_eff_zero    = b_is_zero || b_is_subnorm;
    wire a_is_normal   = !a_eff_zero && !a_is_nan;
    wire b_is_normal   = !b_eff_zero && !b_is_nan;

    wire r_is_zero     = (exp_r == 4'h0) && (mant_r == 3'h0);
    wire r_is_nan      = (exp_r == 4'hF) && (mant_r == 3'h7);
    wire r_is_max_norm = (exp_r == 4'hF) && (mant_r == 3'h6);

    wire any_nan       = a_is_nan || b_is_nan;

    // Negation of b: flip sign bit only
    wire [7:0] neg_b = {~b[7], b[6:0]};

    // =========================================================================
    // Property 1: NaN propagation
    // Any NaN input produces NaN output
    // =========================================================================
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_is_nan);
            p_nan_invalid_flag: assert (invalid);
        end
    end

    // =========================================================================
    // Property 2: Identity -- a + (+0) = a for normal numbers
    // +0 in E4M3 = 8'h00
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == 8'h00) begin
            p_add_pos_zero: assert (result == a);
        end
    end

    // =========================================================================
    // Property 3: Identity -- (+0) + b = b for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (b_is_normal && a == 8'h00) begin
            p_zero_plus_b: assert (result == b);
        end
    end

    // =========================================================================
    // Property 4: Additive inverse -- a + (-a) = +0 for normal numbers
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_normal && b == neg_b && a[6:0] == b[6:0] && sign_a != sign_b) begin
            p_additive_inverse: assert (result == 8'h00);
        end
    end

    // =========================================================================
    // Property 5: Both inputs zero
    // 0 + 0 = 0 (sign handling per FTZ)
    // =========================================================================
    always @(posedge clk) begin
        if (a_eff_zero && b_eff_zero && !any_nan) begin
            p_both_zero: assert (r_is_zero);
        end
    end

    // =========================================================================
    // Property 6: Known test vector: 1.0 + 1.0 = 2.0
    // 1.0 = 0x38, 2.0 = 0x40
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h38 && b == 8'h38) begin
            p_one_plus_one: assert (result == 8'h40);
        end
    end

    // =========================================================================
    // Property 7: Known test vector: 1.0 + (-1.0) = 0.0
    // 1.0 = 0x38, -1.0 = 0xB8
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h38 && b == 8'hB8) begin
            p_one_minus_one: assert (result == 8'h00);
        end
    end

    // =========================================================================
    // Property 8: Known test vector: 2.0 + 2.0 = 4.0
    // 2.0 = 0x40, 4.0 = 0x48
    // =========================================================================
    always @(posedge clk) begin
        if (a == 8'h40 && b == 8'h40) begin
            p_two_plus_two: assert (result == 8'h48);
        end
    end

    // =========================================================================
    // Property 9: Overflow flag -> result saturates to max normal
    // E4M3 has no infinity
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
    // Property 13: Result exponent validity for non-special results
    // If exp=15, mant < 7 (else would be NaN)
    // =========================================================================
    always @(posedge clk) begin
        if (!r_is_zero && !r_is_nan && !overflow && !underflow && !invalid) begin
            p_normal_exp_range: assert (exp_r >= 4'h1 && exp_r <= 4'hF);
            if (exp_r == 4'hF) begin
                p_no_nan_pattern: assert (mant_r != 3'h7);
            end
        end
    end

    // =========================================================================
    // Property 14: Subnormal inputs flushed to zero (FTZ)
    // subnorm + normal = normal (subnorm treated as zero)
    // =========================================================================
    always @(posedge clk) begin
        if (a_is_subnorm && b_is_normal) begin
            p_subnorm_a_identity: assert (result == b);
        end
        if (b_is_subnorm && a_is_normal) begin
            p_subnorm_b_identity: assert (result == a);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        c_normal_add: cover (a_is_normal && b_is_normal && !overflow && !underflow);
        c_normal_sub: cover (a_is_normal && b_is_normal && sign_a != sign_b && !r_is_zero);
        c_exact_zero: cover (a_is_normal && b_is_normal && r_is_zero);
        c_overflow:   cover (overflow);
        c_underflow:  cover (underflow);
        c_nan:        cover (r_is_nan);
        c_max_overflow: cover (a_is_normal && b_is_normal && r_is_max_norm);
    end

endmodule
