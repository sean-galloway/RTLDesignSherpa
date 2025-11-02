// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_subtractor_half
// Purpose: Math Subtractor Half module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_subtractor_half (
    input  i_a,
    i_b,
    output o_d,
    o_b
);

    assign o_d = i_a ^ i_b;
    assign o_b = ~i_a & i_b;

endmodule : math_subtractor_half
