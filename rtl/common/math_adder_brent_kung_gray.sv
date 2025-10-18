// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_gray
// Purpose: Math Adder Brent Kung Gray module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_gray (
    input  logic i_g,
    input  logic i_p,
    input  logic i_g_km1,
    output logic ow_g
);

    assign ow_g = i_g | (i_p & i_g_km1);
endmodule
