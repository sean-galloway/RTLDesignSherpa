// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_pg
// Purpose: Math Adder Brent Kung Pg module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_pg (
    input  logic i_a,
    input  logic i_b,
    output logic ow_g,
    output logic ow_p
);

    assign ow_g = i_a & i_b;
    assign ow_p = i_a ^ i_b;
endmodule
