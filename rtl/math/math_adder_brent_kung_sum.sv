// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_sum
// Purpose: Math Adder Brent Kung Sum module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_sum #(
    parameter int N = 8
) (
    input  logic [  N:0] i_p,
    input  logic [  N:0] i_gg,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    // Loop over bits
    genvar k;
    generate
        for (k = 0; k < N; k++) begin : gen_loop
            assign ow_sum[k] = i_gg[k] ^ i_p[k+1];
        end
    endgenerate

    assign ow_carry = i_gg[N];
endmodule
