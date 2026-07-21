// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_compressor_4to2
// Purpose: 2x Math Adder Full module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// 4:2 Compressor
module math_compressor_4to2 (
    input  logic i_x1, i_x2, i_x3, i_x4,
    input  logic i_cin,
    output logic ow_sum,
    output logic ow_carry,
    output logic ow_cout
);
    logic w_int_sum, w_int_carry;

    // First 3:2: X1, X2, X3
    math_adder_full u_fa1 (
        .i_a     (i_x1),
        .i_b     (i_x2),
        .i_c     (i_x3),
        .ow_sum  (w_int_sum),
        .ow_carry(ow_cout)       // Cout independent of Cin!
    );

    // Second 3:2: int_sum, X4, Cin
    math_adder_full u_fa2 (
        .i_a     (w_int_sum),
        .i_b     (i_x4),
        .i_c     (i_cin),
        .ow_sum  (ow_sum),
        .ow_carry(ow_carry)
    );

endmodule : math_compressor_4to2

