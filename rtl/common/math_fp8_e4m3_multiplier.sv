// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e4m3_multiplier
// Purpose: Complete FP8 E4M3 multiplier with special case handling and RNE rounding
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e4m3_multiplier.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e4m3_multiplier(
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic [7:0] ow_result,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_invalid
);

// FP8 E4M3 field extraction
// Format: [7]=sign, [6:3]=exponent, [2:0]=mantissa

wire       w_sign_a = i_a[7];
wire [3:0] w_exp_a  = i_a[6:3];
wire [2:0] w_mant_a = i_a[2:0];

wire       w_sign_b = i_b[7];
wire [3:0] w_exp_b  = i_b[6:3];
wire [2:0] w_mant_b = i_b[2:0];

// Special value detection

// Zero: exp=0, mant=0
wire w_a_is_zero = (w_exp_a == 4'h0) & (w_mant_a == 3'h0);
wire w_b_is_zero = (w_exp_b == 4'h0) & (w_mant_b == 3'h0);

// Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)
wire w_a_is_subnormal = (w_exp_a == 4'h0) & (w_mant_a != 3'h0);
wire w_b_is_subnormal = (w_exp_b == 4'h0) & (w_mant_b != 3'h0);

// NaN: exp=15, mant=111 (E4M3 specific - no infinity!)
wire w_a_is_nan = (w_exp_a == 4'hF) & (w_mant_a == 3'h7);
wire w_b_is_nan = (w_exp_b == 4'hF) & (w_mant_b == 3'h7);

// Effective zero (includes subnormals in FTZ mode)
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;

// Normal number (has implied leading 1)
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_nan;

// Result sign: XOR of input signs
wire w_sign_result = w_sign_a ^ w_sign_b;

// Mantissa multiplication (4x4 direct multiply)
wire [7:0] w_mant_product;
wire       w_needs_norm;
wire [2:0] w_mant_mult_out;
wire       w_round_bit;
wire       w_sticky_bit;

math_fp8_e4m3_mantissa_mult u_mant_mult (
    .i_mant_a(w_mant_a),
    .i_mant_b(w_mant_b),
    .i_a_is_normal(w_a_is_normal),
    .i_b_is_normal(w_b_is_normal),
    .ow_product(w_mant_product),
    .ow_needs_norm(w_needs_norm),
    .ow_mant_out(w_mant_mult_out),
    .ow_round_bit(w_round_bit),
    .ow_sticky_bit(w_sticky_bit)
);

// Exponent addition
wire [3:0] w_exp_sum;
wire       w_exp_overflow;
wire       w_exp_underflow;
wire       w_exp_a_zero, w_exp_b_zero;
wire       w_exp_a_nan, w_exp_b_nan;

math_fp8_e4m3_exponent_adder u_exp_add (
    .i_exp_a(w_exp_a),
    .i_exp_b(w_exp_b),
    .i_norm_adjust(w_needs_norm),
    .ow_exp_out(w_exp_sum),
    .ow_overflow(w_exp_overflow),
    .ow_underflow(w_exp_underflow),
    .ow_a_is_zero(w_exp_a_zero),
    .ow_b_is_zero(w_exp_b_zero),
    .ow_a_is_nan(w_exp_a_nan),
    .ow_b_is_nan(w_exp_b_nan)
);

// Round-to-Nearest-Even (RNE) rounding
// Round up if:
//   - round_bit=1 AND (sticky_bit=1 OR LSB=1)

wire w_lsb = w_mant_mult_out[0];
wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);

// Apply rounding to mantissa
wire [3:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {3'b0, w_round_up};

// Check for mantissa overflow from rounding
wire w_mant_round_overflow = w_mant_rounded[3];

// Final mantissa (3 bits)
wire [2:0] w_mant_final = w_mant_round_overflow ?
    3'h0 : w_mant_rounded[2:0];  // Overflow means 1.0 -> needs exp adjust

// Exponent adjustment for rounding overflow
wire [3:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 4'd1) : w_exp_sum;

// Check for exponent overflow after rounding adjustment
// E4M3: exp=15 with mant=111 is NaN, so max normal is exp=15, mant=110
// Also detect overflow when mantissa rounding pushes exp=15 to exp=16 (wraps to 0)
wire w_round_causes_overflow = w_mant_round_overflow & (w_exp_sum == 4'hF);
wire w_final_overflow = w_exp_overflow | w_round_causes_overflow |
                        (w_exp_final == 4'hF & w_mant_final == 3'h7);

// Special case result handling

// NaN propagation: any NaN input produces NaN output
wire w_any_nan = w_a_is_nan | w_b_is_nan;

// Zero result: either input is (effective) zero
wire w_result_zero = w_a_eff_zero | w_b_eff_zero;

// Final result assembly

always_comb begin
    // Default: normal multiplication result
    ow_result = {w_sign_result, w_exp_final, w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    // Special case priority (highest to lowest)
    if (w_any_nan) begin
        // NaN result: canonical NaN (exp=15, mant=111)
        ow_result = {w_sign_result, 4'hF, 3'h7};
        ow_invalid = 1'b1;
    end else if (w_final_overflow) begin
        // Saturate to max normal (E4M3 has no infinity)
        ow_result = {w_sign_result, 4'hF, 3'h6};  // Max normal value
        ow_overflow = 1'b1;
    end else if (w_result_zero | w_exp_underflow) begin
        // Zero result
        ow_result = {w_sign_result, 4'h0, 3'h0};
        ow_underflow = w_exp_underflow & ~w_result_zero;
    end
end

endmodule
