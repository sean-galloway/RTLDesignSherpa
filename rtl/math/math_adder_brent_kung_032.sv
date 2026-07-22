// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_032
// Purpose: Math Adder Brent Kung 032 module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_032 #(
    parameter int N = 32
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    logic [N:0] ow_g;
    logic [N:0] ow_p;
    logic [N:0] ow_gg;
    math_adder_brent_kung_bitwisepg #(
        .N(N)
    ) BitwisePGLogic_inst (
        .i_a (i_a),
        .i_b (i_b),
        .i_c (i_c),
        .ow_g(ow_g),
        .ow_p(ow_p)
    );
    math_adder_brent_kung_grouppg_032 #(
        .N(N)
    ) GroupPGLogic_inst (
        .i_g  (ow_g),
        .i_p  (ow_p),
        .ow_gg(ow_gg),
        .ow_pp()
    );
    math_adder_brent_kung_sum #(
        .N(N)
    ) SumLogic_inst (
        .i_p(ow_p),
        .i_gg(ow_gg),
        .ow_sum(ow_sum),
        .ow_carry(ow_carry)
    );

endmodule
