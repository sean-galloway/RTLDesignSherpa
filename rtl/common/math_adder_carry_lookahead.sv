// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_carry_lookahead
// Purpose: Math Adder Carry Lookahead module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
// Parameterized CLA with Verilator pragma to silence the warning
/* verilator lint_off UNOPTFLAT */
module math_adder_carry_lookahead #(
    parameter int N = 4
) (
    input logic [N-1:0] i_a,
    input logic [N-1:0] i_b,
    input logic i_c,
    output logic [N-1:0] ow_sum,
    output logic ow_carry
);
    // Generate and propagate signals
    logic [N-1:0] w_p, w_g;
    logic [N:0] w_c;

    // Generate the generate and propagate signals
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_g_p
            assign w_g[i] = i_a[i] & i_b[i];        // Generate: G = A AND B
            assign w_p[i] = i_a[i] ^ i_b[i];        // Propagate: P = A XOR B
        end
    endgenerate

    // Calculate carry bits
    assign w_c[0] = i_c;

    generate
        for (i = 1; i <= N; i++) begin : gen_carry
            assign w_c[i] = w_g[i-1] | (w_p[i-1] & w_c[i-1]);
        end
    endgenerate

    // Calculate sum bits
    generate
        for (i = 0; i < N; i++) begin : gen_sum
            assign ow_sum[i] = w_p[i] ^ w_c[i];
        end
    endgenerate

    // Assign carry-out
    assign ow_carry = w_c[N];

endmodule : math_adder_carry_lookahead
/* verilator lint_on UNOPTFLAT */
