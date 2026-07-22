// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp16_mantissa_mult
// Purpose: IEEE 754-2008 FP16 mantissa multiplier using 11x11 Dadda tree
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp16_mantissa_mult.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp16_mantissa_mult(
    input  logic [9:0]  i_mant_a,
    input  logic [9:0]  i_mant_b,
    input  logic        i_a_is_normal,
    input  logic        i_b_is_normal,
    output logic [21:0] ow_product,
    output logic        ow_needs_norm,
    output logic [9:0]  ow_mant_out,
    output logic        ow_round_bit,
    output logic        ow_sticky_bit
);

// Extended mantissas with implied leading 1
// For normal numbers: 1.mantissa (11 bits total)
// For zero/subnormal: 0.mantissa (FTZ mode)

wire [10:0] w_mant_a_ext = i_a_is_normal ? {1'b1, i_mant_a} : 11'h0;
wire [10:0] w_mant_b_ext = i_b_is_normal ? {1'b1, i_mant_b} : 11'h0;

// 11x11 Dadda tree multiplication
// Product range: 1.0 * 1.0 = 1.0 to 1.999... * 1.999... = 3.999...
// Format: xx.xxxx_xxxx_xxxx_xxxx_xxxx (2 integer + 20 fraction bits)
math_multiplier_dadda_4to2_011 u_dadda_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(ow_product)
);

// Normalization detection
// If bit[21] = 1, product >= 2.0, need to shift right by 1
assign ow_needs_norm = ow_product[21];

// Extract 10-bit mantissa based on normalization
// If needs_norm: take bits [20:11] (shift right)
// If not: take bits [19:10] (no shift)
assign ow_mant_out = ow_needs_norm ? ow_product[20:11] : ow_product[19:10];

// Round bit (first bit after mantissa)
assign ow_round_bit = ow_needs_norm ? ow_product[10] : ow_product[9];

// Sticky bit (OR of all bits after round bit)
assign ow_sticky_bit = ow_needs_norm ? |ow_product[9:0] : |ow_product[8:0];

endmodule
