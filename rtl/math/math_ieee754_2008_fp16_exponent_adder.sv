// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp16_exponent_adder
// Purpose: IEEE 754-2008 FP16 exponent adder with bias handling and overflow/underflow detection
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp16_exponent_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp16_exponent_adder(
    input  logic [4:0] i_exp_a,
    input  logic [4:0] i_exp_b,
    input  logic       i_norm_adjust,
    output logic [4:0] ow_exp_out,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_a_is_zero,
    output logic       ow_b_is_zero,
    output logic       ow_a_is_inf,
    output logic       ow_b_is_inf
);

// Special case detection
// exp = 0: Zero (if mantissa = 0) or subnormal
// exp = 31: Inf (if mantissa = 0) or NaN (if mantissa != 0)

assign ow_a_is_zero = (i_exp_a == 5'h00);
assign ow_b_is_zero = (i_exp_b == 5'h00);
assign ow_a_is_inf  = (i_exp_a == 5'h1F);
assign ow_b_is_inf  = (i_exp_b == 5'h1F);

// Exponent addition with bias handling
// result_exp = exp_a + exp_b - bias + norm_adjust
// 
// Use 7-bit intermediate to detect overflow/underflow
// Bias = 15 (5'h0F) per IEEE 754-2008 FP16

// Extended precision for overflow/underflow detection
wire [6:0] w_exp_sum_raw;

// Calculate: exp_a + exp_b - bias + norm_adjust
// Rearranged as: (exp_a + exp_b + norm_adjust) - 7'd15
assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} + 
                       {6'b0, i_norm_adjust} - 7'd15;

// Underflow detection: result <= 0 (signed comparison)
// If MSB of 7-bit result is set, it's negative (underflow)
wire w_underflow_raw = w_exp_sum_raw[6] | (w_exp_sum_raw == 7'd0);

// Overflow detection: result > 30 (31 reserved for inf/nan)
// Only check overflow if not underflow
wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 7'd30);

// Special cases override normal overflow/underflow
wire w_either_special = ow_a_is_inf | ow_b_is_inf | ow_a_is_zero | ow_b_is_zero;

assign ow_overflow  = w_overflow_raw & ~w_either_special;
assign ow_underflow = w_underflow_raw & ~w_either_special;

// Result exponent with saturation
// - Zero/subnormal input: result is zero (exp=0)
// - Inf/NaN input: result is inf (exp=31)
// - Overflow: saturate to 31 (inf)
// - Underflow: saturate to 0 (zero)
// - Normal: use computed value

always_comb begin
    if (ow_a_is_zero | ow_b_is_zero) begin
        ow_exp_out = 5'h00;  // Zero result (or handled as special case)
    end else if (ow_a_is_inf | ow_b_is_inf) begin
        ow_exp_out = 5'h1F;  // Infinity/NaN result
    end else if (ow_overflow) begin
        ow_exp_out = 5'h1F;  // Overflow to infinity
    end else if (ow_underflow) begin
        ow_exp_out = 5'h00;  // Underflow to zero
    end else begin
        ow_exp_out = w_exp_sum_raw[4:0];
    end
end

endmodule
