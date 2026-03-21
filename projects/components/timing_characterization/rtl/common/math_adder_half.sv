// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_half
// Purpose: Math Adder Half module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_half #(parameter int N=1)(
    input  logic i_a,
    input  logic i_b,
    output logic ow_sum,
    output logic ow_carry
);

    assign ow_sum   = i_a ^ i_b;
    assign ow_carry = i_a & i_b;

endmodule : math_adder_half
