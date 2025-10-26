// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_subtractor_carry_lookahead
// Purpose: Math Subtractor Carry Lookahead module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_subtractor_carry_lookahead #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_borrow_in,
    output logic [N-1:0] ow_difference,
    output logic [N-1:0] ow_d,
    output logic         ow_borrow_out,
    output logic         ow_b
);

    logic [N-1:0] w_g, w_p;
    logic         w_lookahead_borrow [N+1];

    // Generate and propagate
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_gp
            assign w_g[i] = ~i_a[i] & i_b[i];
            assign w_p[i] = ~i_a[i] | i_b[i];
        end
    endgenerate

    // Borrow lookahead chain (explicit loop, not generate)
    always_comb begin
        w_lookahead_borrow[0] = i_borrow_in;
        for (int i = 1; i <= N; i++) begin
            w_lookahead_borrow[i] = w_g[i-1] | (w_p[i-1] & w_lookahead_borrow[i-1]);
        end
    end

    // Difference
    generate
        for (i = 0; i < N; i++) begin : gen_diff
            assign ow_difference[i] = i_a[i] ^ i_b[i] ^ w_lookahead_borrow[i];
        end
    endgenerate

    assign ow_borrow_out = w_lookahead_borrow[N];
    assign ow_d = ow_difference;
    assign ow_b = ow_borrow_out;

endmodule : math_subtractor_carry_lookahead
