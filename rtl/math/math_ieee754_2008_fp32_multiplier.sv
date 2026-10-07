// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_multiplier
// Purpose: Complete IEEE 754-2008 FP32 multiplier with special case handling and RNE rounding
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-07
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_multiplier.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/math
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp32_multiplier #(
    parameter bit SUBNORMAL_SUPPORT = 1'b0  // 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow
) (
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

// Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1
// only true zeros are effective zero
wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);
wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);

// Normal number (has implied leading 1)
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Hidden-bit feeds for the mantissa multiplier: 0 for subnormals when
// SUBNORMAL_SUPPORT=1 (they decode as 0.mantissa at effective exponent
// 1-bias). Identical to *_is_normal when SUBNORMAL_SUPPORT=0.
wire w_a_h1 = w_a_is_normal & (~SUBNORMAL_SUPPORT | ~w_a_is_subnormal);
wire w_b_h1 = w_b_is_normal & (~SUBNORMAL_SUPPORT | ~w_b_is_subnormal);

// Exponents adjusted for subnormal decode: a subnormal operates at effective
// biased exponent 1. Identical to the raw exponent when SUBNORMAL_SUPPORT=0.
wire [7:0] w_exp_a_adj = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ? 8'd1 : w_exp_a;
wire [7:0] w_exp_b_adj = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ? 8'd1 : w_exp_b;

// Result sign: XOR of input signs
wire w_sign_result = w_sign_a ^ w_sign_b;

// Mantissa multiplication (24x24 with Dadda 4:2 tree)
wire [47:0] w_mant_product;
wire        w_needs_norm;
wire [22:0] w_mant_mult_out;
wire        w_guard_bit;
wire        w_round_bit;
wire        w_sticky_bit;

math_ieee754_2008_fp32_mantissa_mult u_mant_mult (
    .i_mant_a(w_mant_a),
    .i_mant_b(w_mant_b),
    .i_a_is_normal(w_a_h1),
    .i_b_is_normal(w_b_h1),
    .ow_product(w_mant_product),
    .ow_needs_norm(w_needs_norm),
    .ow_mant_out(w_mant_mult_out),
    .ow_guard_bit(w_guard_bit),
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
    .i_exp_a(w_exp_a_adj),
    .i_exp_b(w_exp_b_adj),
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

// -------------------------------------------------------------------------
// Gradual-underflow datapath (SUBNORMAL_SUPPORT=1 only)
// 
// With a subnormal operand the 48-bit product can fall below 1.0,
// which the legacy needs_norm normalization never sees: left-shift
// the product back into [1,2) and debit the exponent by the same
// amount. When the true product exponent is below 1 the exact
// result lies in the subnormal range: right-shift the normalized
// {hidden, mant, GRS} vector onto the subnormal grid (exponent
// 1-bias), folding EVERY shifted-out bit into the sticky (TRUE
// unfolded sticky, math ISSUE-001), then round RNE exactly as on
// the normal path. A rounding carry out of pre-round exponent 0
// produces min-normal, not a flush (math BUG-004 ruling). With
// SUBNORMAL_SUPPORT=0 w_left_shift, w_norm_rescue and
// w_subnorm_path are constant 0 and this block folds away.
// -------------------------------------------------------------------------

// Left normalization for products below 1.0 (only possible with a
// subnormal operand at SUBNORMAL_SUPPORT=1; the loop keeps the
// highest set bit, last assignment wins)
logic [5:0] r_left_shift;
always_comb begin
    r_left_shift = 6'd0;
    for (int i = 0; i < 47; i++) begin
        if (w_mant_product[i]) r_left_shift = 6'd46 - 6'(i);
    end
end

wire w_prod_lt1 = ~w_mant_product[47] & ~w_mant_product[46];
wire [5:0] w_left_shift = (SUBNORMAL_SUPPORT & w_prod_lt1 &
    (|w_mant_product[45:0])) ? r_left_shift : 6'd0;

// Normalized significand in [1,2) with the hidden bit at [46];
// identical to the legacy product view (w_mant_product[47:1] /
// w_mant_product[46:0]) whenever no left normalization applies
wire [46:0] w_mant_norm = w_needs_norm ? w_mant_product[47:1] :
    ((w_left_shift != 6'd0) ? ({1'b0, w_mant_product[45:0]} << w_left_shift)
        : w_mant_product[46:0]);

// True product exponent on the subnormal-adjusted exponents
wire signed [10:0] w_exp_true = $signed({3'b000, w_exp_a_adj}) +
    $signed({3'b000, w_exp_b_adj}) - 11'sd127 +
    $signed({10'b0000000000, w_needs_norm}) - $signed({5'b00000, w_left_shift});

// Subnormal output path: shift the normalized vector onto the grid
wire w_subnorm_path = SUBNORMAL_SUPPORT & (w_exp_true < 11'sd1);
// Shift amount 1-exp_true, clamped so the mask still captures the
// whole vector (a clamped shift leaves guard=0, so nothing rounds)
wire signed [10:0] w_sub_shift_s = 11'sd1 - w_exp_true;  // >= 1 when active
wire w_shift_all = (w_sub_shift_s > 11'sd47);
wire [5:0] w_sub_shift = w_shift_all ? 6'd47 : w_sub_shift_s[5:0];
wire [47:0] w_sig_v = {1'b0, w_mant_norm};
wire [47:0] w_sub_mask = (48'h000000000001 << w_sub_shift) - 48'h000000000001;
wire [47:0] w_v_shifted = w_sig_v >> w_sub_shift;
wire [22:0] w_sub_mant = w_v_shifted[45:23];
wire w_sub_g = w_v_shifted[22];
wire w_sub_r = w_v_shifted[21];
wire w_sub_sticky = (|w_v_shifted[20:0]) | (|(w_sig_v & w_sub_mask));

// Effective rounding inputs: the =1 corrections override the
// mantissa_mult outputs only on the subnormal / left-rescue paths;
// every select folds to the legacy signal when SUBNORMAL_SUPPORT=0
wire w_norm_rescue = SUBNORMAL_SUPPORT & (w_left_shift != 6'd0) & ~w_subnorm_path;
wire w_path_apply = w_subnorm_path | w_norm_rescue;
wire [22:0] w_path_mant = w_subnorm_path ? w_sub_mant : w_mant_norm[45:23];
wire w_path_g = w_subnorm_path ? w_sub_g : w_mant_norm[22];
wire w_path_r = w_subnorm_path ? w_sub_r : w_mant_norm[21];
wire w_path_sticky = w_subnorm_path ? w_sub_sticky : (|w_mant_norm[20:0]);
wire [22:0] w_mant_eff = w_path_apply ? w_path_mant : w_mant_mult_out;
wire w_guard_eff = w_path_apply ? w_path_g : w_guard_bit;
wire w_round_eff = w_path_apply ? w_path_r : w_round_bit;
wire w_sticky_eff = w_path_apply ? w_path_sticky : w_sticky_bit;

// Round-to-Nearest-Even (RNE) rounding
// Textbook RNE: round up iff guard=1 AND (round | sticky | LSB).
// Guard is the first bit below the kept mantissa; sticky arrives TRUE
// (unfolded) from mantissa_mult (or the subnormal shifter above).

wire w_lsb = w_mant_eff[0];
wire w_round_up = w_guard_eff & (w_round_eff | w_sticky_eff | w_lsb);  // true RNE (math ISSUE-001 (was MATH-001) family)

// Apply rounding to mantissa
wire [23:0] w_mant_rounded = {1'b0, w_mant_eff} + {23'b0, w_round_up};

// Check for mantissa overflow from rounding (rare)
wire w_mant_round_overflow = w_mant_rounded[23];

// Final mantissa (23 bits)
wire [22:0] w_mant_final = w_mant_round_overflow ? 
    23'h000000 : w_mant_rounded[22:0];  // Overflow means 1.0 -> needs exp adjust

// Exponent base: 0 on the subnormal path (a rounding carry out of
// pre-round exponent 0 yields min-normal, not a flush -- math BUG-004
// ruling), the debit-corrected exponent when left normalization
// applied, otherwise the adder sum
wire [7:0] w_exp_base = w_subnorm_path ? 8'd0 :
    (w_norm_rescue ? w_exp_true[7:0] : w_exp_sum);
wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_base + 8'd1) : w_exp_base;

// Check for exponent overflow after rounding adjustment
wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);

// IEEE 754 detects underflow AFTER rounding (math BUG-004, was MATH-008): when the
// pre-round exponent sum is exactly 0 (one below the normal range) and
// mantissa rounding carries out, the result is exactly the minimum
// normal (exp 1, mant 0) and must not be flushed. The exponent adder
// saturates its output on underflow, so recompute "sum was exactly 0"
// from the raw exponents here.
wire w_exp_sum_was_zero = ({1'b0, w_exp_a} + {1'b0, w_exp_b} + {8'b0, w_needs_norm}) == 9'd127;
wire w_uf_rescued = w_exp_sum_was_zero & w_mant_round_overflow;

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
    end else if (SUBNORMAL_SUPPORT) begin
        // Gradual underflow: the tiny result (subnormal, or zero when
        // the rounded product vanishes) comes straight from the
        // shifted vector; a true-zero operand flushes through the
        // all-zero product path. Anything not tiny keeps the default
        // normal result assigned above.
        if (w_subnorm_path) begin
            ow_result = {w_sign_result, w_exp_final, w_mant_final};
            // IEEE underflow: tiny AFTER rounding AND inexact. The
            // multiplier, unlike the adder, rounds inexact at the
            // subnormal boundary, so this flag can assert; a carry
            // into min-normal (exp 1) is not tiny and stays silent.
            ow_underflow = (w_exp_final == 8'h00) &
                (w_guard_eff | w_round_eff | w_sticky_eff);
        end
    end else if (w_result_zero | (w_exp_underflow & ~w_uf_rescued)) begin
        // Zero result
        ow_result = {w_sign_result, 8'h00, 23'h000000};
        ow_underflow = w_exp_underflow & ~w_result_zero & ~w_uf_rescued;
    end
end

endmodule
