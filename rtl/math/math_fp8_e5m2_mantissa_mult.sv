// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_fp8_e5m2_mantissa_mult
// Purpose: FP8 E5M2 3x3 mantissa multiplier with normalization
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp8_e5m2_mantissa_mult.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_fp8_e5m2_mantissa_mult(
    input  logic [1:0] i_mant_a,
    input  logic [1:0] i_mant_b,
    input  logic       i_a_is_normal,
    input  logic       i_b_is_normal,
    output logic [5:0] ow_product,
    output logic       ow_needs_norm,
    output logic [1:0] ow_mant_out,
    output logic       ow_round_bit,
    output logic       ow_sticky_bit
);

// Extend mantissas with implied 1 for normal numbers
// Format: 1.mm (3 bits total)

wire [2:0] w_mant_a_ext = i_a_is_normal ? {1'b1, i_mant_a} : 3'h0;
wire [2:0] w_mant_b_ext = i_b_is_normal ? {1'b1, i_mant_b} : 3'h0;

// Direct 3x3 multiplication -> 6-bit product
// Product format: xx.xxxx (2 integer bits, 4 fraction bits)
wire [5:0] w_product = w_mant_a_ext * w_mant_b_ext;

// Normalization detection
// If bit 5 is set, product is in range [2.0, 4.0)
// Need to shift right by 1 and increment exponent
wire w_needs_norm = w_product[5];

// Extract normalized mantissa
// If needs_norm: use bits [4:3] (shift right by 1)
// Else: use bits [3:2]
wire [1:0] w_mant_normalized = w_needs_norm ? w_product[4:3] : w_product[3:2];

// Round bit (next bit after mantissa)
wire w_round = w_needs_norm ? w_product[2] : w_product[1];

// Sticky bit (OR of remaining bits)
wire w_sticky = w_needs_norm ? |w_product[1:0] : w_product[0];

// Output assignments
assign ow_product = w_product;
assign ow_needs_norm = w_needs_norm;
assign ow_mant_out = w_mant_normalized;
assign ow_round_bit = w_round;
assign ow_sticky_bit = w_sticky;

endmodule
