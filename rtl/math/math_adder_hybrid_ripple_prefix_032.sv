// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_hybrid_ripple_prefix_032
// Purpose: 32-bit wrapper for math_adder_hybrid_ripple_prefix
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

module math_adder_hybrid_ripple_prefix_032 #(
    parameter int N = 32,
    parameter int RIPPLE_BITS = 8
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    math_adder_hybrid_ripple_prefix #(
        .N          (N),
        .RIPPLE_BITS(RIPPLE_BITS)
    ) u_core (
        .i_a     (i_a),
        .i_b     (i_b),
        .i_c     (i_c),
        .ow_sum  (ow_sum),
        .ow_carry(ow_carry)
    );

endmodule : math_adder_hybrid_ripple_prefix_032
