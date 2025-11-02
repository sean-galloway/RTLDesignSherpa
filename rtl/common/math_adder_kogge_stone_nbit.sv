// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_kogge_stone_nbit
// Purpose: Math Adder Kogge Stone Nbit module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_kogge_stone_nbit #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    ////////////////////////////////////////////////////////////////////////////
    // Step 1: Generate and Propagate terms
    logic [N-1:0] w_G, w_P;
    genvar i;
    for (i = 0; i < N; i++) begin : gen_g_p
        assign w_G[i] = i_a[i] & i_b[i];
        assign w_P[i] = i_a[i] | i_b[i];
    end

    ////////////////////////////////////////////////////////////////////////////
    // Step 2: Parallel Prefix Computation using Kogge-Stone
    logic [N-1:0] w_C;
    always_comb begin
        logic carry;          // local scratch
        carry   = w_G[0];
        w_C[0]  = carry;
        for (int j = 1; j < N; ++j) begin
            carry  = w_G[j] | (w_P[j] & carry);
            w_C[j] = carry;
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Step 3: Sum Calculation
    generate
        for (i = 0; i < N; i++) begin : gen_sum
            if (i == 0) begin : gen_sum_no_carry
                assign ow_sum[i] = i_a[i] ^ i_b[i];
            end else begin : gen_sum
                assign ow_sum[i] = i_a[i] ^ i_b[i] ^ w_C[i-1];
            end
        end
    endgenerate


    ////////////////////////////////////////////////////////////////////////////
    // The final carry out
    assign ow_carry = w_C[N-1];

    // Debug purposes


endmodule : math_adder_kogge_stone_nbit
