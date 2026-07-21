// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_multiplier
// Purpose: Complete IEEE 754-2008 FP32 multiplier with special case handling and RNE rounding
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_multiplier.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp32_multiplier(
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid
);

// IEEE 754-2008 FP32 field extraction
// Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa

wire        w_sign_a = i_a[31];
wire [7:0]  w_exp_a  = i_a[30:23];
wire [22:0] w_mant_a = i_a[22:0];

wire        w_sign_b = i_b[31];
wire [7:0]  w_exp_b  = i_b[30:23];
wire [22:0] w_mant_b = i_b[22:0];

// Special value detection

// Zero: exp=0, mant=0
wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);
wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h000000);

// Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)
wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);
wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h000000);

// Infinity: exp=FF, mant=0
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);
wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h000000);

// NaN: exp=FF, mant!=0
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h000000);

// Effective zero (includes subnormals in FTZ mode)
wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;

// Normal number (has implied leading 1)
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Result sign: XOR of input signs
wire w_sign_result = w_sign_a ^ w_sign_b;

// Mantissa multiplication (24x24 with Dadda 4:2 tree)
wire [47:0] w_mant_product;
wire        w_needs_norm;
wire [22:0] w_mant_mult_out;
wire        w_round_bit;
wire        w_sticky_bit;

math_ieee754_2008_fp32_mantissa_mult u_mant_mult (
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
wire [7:0] w_exp_sum;
wire       w_exp_overflow;
wire       w_exp_underflow;
wire       w_exp_a_zero, w_exp_b_zero;
wire       w_exp_a_inf, w_exp_b_inf;
wire       w_exp_a_nan, w_exp_b_nan;

math_ieee754_2008_fp32_exponent_adder u_exp_add (
    .i_exp_a(w_exp_a),
    .i_exp_b(w_exp_b),
    .i_norm_adjust(w_needs_norm),
    .ow_exp_out(w_exp_sum),
    .ow_overflow(w_exp_overflow),
    .ow_underflow(w_exp_underflow),
    .ow_a_is_zero(w_exp_a_zero),
    .ow_b_is_zero(w_exp_b_zero),
    .ow_a_is_inf(w_exp_a_inf),
    .ow_b_is_inf(w_exp_b_inf),
    .ow_a_is_nan(w_exp_a_nan),
    .ow_b_is_nan(w_exp_b_nan)
);

// Round-to-Nearest-Even (RNE) rounding
// Round up if:
//   - round_bit=1 AND (sticky_bit=1 OR LSB=1)
// This implements RNE: ties round to even

wire w_lsb = w_mant_mult_out[0];
wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);

// Apply rounding to mantissa
wire [23:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {23'b0, w_round_up};

// Check for mantissa overflow from rounding (rare)
wire w_mant_round_overflow = w_mant_rounded[23];

// Final mantissa (23 bits)
wire [22:0] w_mant_final = w_mant_round_overflow ? 
    23'h000000 : w_mant_rounded[22:0];  // Overflow means 1.0 -> needs exp adjust

// Exponent adjustment for rounding overflow
wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 8'd1) : w_exp_sum;

// Check for exponent overflow after rounding adjustment
wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);

// Special case result handling

// NaN propagation: any NaN input produces NaN output
wire w_any_nan = w_a_is_nan | w_b_is_nan;

// Invalid operation: 0 * inf = NaN
wire w_invalid_op = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);

// Zero result: either input is (effective) zero
wire w_result_zero = w_a_eff_zero | w_b_eff_zero;

// Infinity result: either input is infinity (and not invalid)
wire w_result_inf = (w_a_is_inf | w_b_is_inf) & ~w_invalid_op;

// Final result assembly

always_comb begin
    // Default: normal multiplication result
    ow_result = {w_sign_result, w_exp_final, w_mant_final};
    ow_overflow = 1'b0;
    ow_underflow = 1'b0;
    ow_invalid = 1'b0;

    // Special case priority (highest to lowest)
    if (w_any_nan | w_invalid_op) begin
        // NaN result: quiet NaN with sign preserved
        ow_result = {w_sign_result, 8'hFF, 23'h400000};  // Canonical qNaN
        ow_invalid = w_invalid_op;
    end else if (w_result_inf | w_final_overflow) begin
        // Infinity result
        ow_result = {w_sign_result, 8'hFF, 23'h000000};
        ow_overflow = w_final_overflow & ~w_result_inf;
    end else if (w_result_zero | w_exp_underflow) begin
        // Zero result
        ow_result = {w_sign_result, 8'h00, 23'h000000};
        ow_underflow = w_exp_underflow & ~w_result_zero;
    end
end

endmodule
