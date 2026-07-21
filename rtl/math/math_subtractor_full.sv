// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_subtractor_full
// Purpose: Math Subtractor Full module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_subtractor_full (
    input  logic i_a,
    i_b,
    i_b_in,
    output logic ow_d,
    ow_b
);

    assign ow_d = i_a ^ i_b ^ i_b_in;
    assign ow_b = (~i_a & i_b) | (~(i_a ^ i_b) & i_b_in);

endmodule : math_subtractor_full
