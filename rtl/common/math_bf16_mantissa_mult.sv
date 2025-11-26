// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_mantissa_mult
// Purpose: BF16 mantissa multiplier (8x8 with normalization and rounding)
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-11-25
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/bf16/bf16_mantissa_mult.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_bf16_mantissa_mult(
    input  logic [6:0]  i_mant_a,
    input  logic [6:0]  i_mant_b,
    input  logic        i_a_is_normal,
    input  logic        i_b_is_normal,
    output logic [15:0] ow_product,
    output logic        ow_needs_norm,
    output logic [6:0]  ow_mant_out,
    output logic        ow_round_bit,
    output logic        ow_sticky_bit
);

// Extend mantissa with implied leading 1 for normalized numbers
wire [7:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};
wire [7:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};

// 8x8 unsigned multiply using Dadda tree with 4:2 compressors
math_multiplier_dadda_4to2_008 u_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(ow_product)
);

// Normalization detection
// Product is in range [0, 4) before normalization
// If MSB (bit 15) is set: product >= 2.0, needs right shift
assign ow_needs_norm = ow_product[15];

// Extract result mantissa
// If needs_norm: take bits [14:8] (after implied 1)
// If not: take bits [13:7] (no shift needed)

// Normalized case: 1x.xxxxxx_xxxxxxxx -> take [14:8]
// Non-normalized: 01.xxxxxx_xxxxxxxx -> take [13:7]
assign ow_mant_out = ow_needs_norm ? ow_product[14:8] : ow_product[13:7];

// Rounding support (Round-to-Nearest-Even)
// 
// For RNE, we need:
//   - Guard bit (G): first bit after mantissa
//   - Round bit (R): second bit after mantissa
//   - Sticky bit (S): OR of all remaining bits
// 
// If needs_norm (product >= 2):
//   mantissa = [14:8], G = [7], R = [6], S = |[5:0]
// If not needs_norm (product < 2):
//   mantissa = [13:7], G = [6], R = [5], S = |[4:0]

wire w_guard_norm    = ow_product[7];
wire w_guard_nonorm  = ow_product[6];

wire w_round_norm    = ow_product[6];
wire w_round_nonorm  = ow_product[5];

wire w_sticky_norm   = |ow_product[5:0];
wire w_sticky_nonorm = |ow_product[4:0];

assign ow_round_bit  = ow_needs_norm ? w_round_norm  : w_round_nonorm;
assign ow_sticky_bit = ow_needs_norm ? 
    (w_guard_norm | w_sticky_norm) : (w_guard_nonorm | w_sticky_nonorm);

endmodule
