// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_prefix_cell
// Purpose: Prefix Cell for the Han-Carlson structure
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_prefix_cell (
    input  logic i_g_hi, i_p_hi,   // From higher bit position
    input  logic i_g_lo, i_p_lo,   // From lower bit position
    output logic ow_g, ow_p
);
    assign ow_g = i_g_hi | (i_p_hi & i_g_lo);
    assign ow_p = i_p_hi & i_p_lo;

endmodule : math_prefix_cell
