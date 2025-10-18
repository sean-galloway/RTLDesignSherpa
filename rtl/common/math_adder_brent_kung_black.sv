// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_black
// Purpose: Math Adder Brent Kung Black module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_black (
    input  logic i_g,
    input  logic i_p,
    input  logic i_g_km1,
    input  logic i_p_km1,
    output logic ow_g,
    output logic ow_p
);

    assign ow_g = i_g | (i_p & i_g_km1);
    assign ow_p = i_p & i_p_km1;
endmodule
