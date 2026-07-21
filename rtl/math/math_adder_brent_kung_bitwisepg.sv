// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_bitwisepg
// Purpose: Math Adder Brent Kung Bitwisepg module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_bitwisepg #(
    parameter int N = 8
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [  N:0] ow_g,
    output logic [  N:0] ow_p
);

    // Loop over bits
    genvar k;
    generate
        for (k = 0; k < N; k++) begin : gen_loop
            math_adder_brent_kung_pg PG_Bit (
                .i_a (i_a[k]),
                .i_b (i_b[k]),
                .ow_p(ow_p[k+1]),
                .ow_g(ow_g[k+1])
            );
        end
    endgenerate

    assign ow_p[0] = 'b0;
    assign ow_g[0] = i_c;
endmodule
