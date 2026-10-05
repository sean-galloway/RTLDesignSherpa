// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_round_robin_simple
// Purpose: Arbiter Round Robin Simple module
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Generic rotating-priority arbiter with masking (no if/case ladders in priority path)
// - Parameterizable number of agents N (N >= 1)
// - Remembers last granted index in a flop (r_last_grant)
// - Masks off agents 0..last_grant (same win-mask LUT as arbiter_round_robin);
//   if no masked request remains, falls back to the unmasked requests (wrap)
// - Lowest-set-bit isolate: x & (~x + 1)
// - Prefixes: w_* = wires, r_* = flops

`include "reset_defs.svh"
module arbiter_round_robin_simple #(
    parameter int unsigned N = 4,
    parameter int unsigned W = $clog2(N)
) (
    input  logic          clk,
    input  logic          rst_n,         // active-low reset
    input  logic [N-1:0]  request,       // request bits [N-1:0]
    output logic          grant_valid,   // any grant
    output logic [N-1:0]  grant,         // one-hot grant
    output logic [W-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
    // ------------------------------
    // State: last granted index
    // ------------------------------
    logic [W-1:0] r_last_grant;

    // ------------------------------
    // Win-mask LUT: after agent i wins, only agents above i stay eligible
    // (elaboration-time constants, same decode as arbiter_round_robin)
    // ------------------------------
    logic [N-1:0] w_win_mask_decode [N];

    for (genvar i = 0; i < N; i++) begin : gen_mask_lut
        assign w_win_mask_decode[i] = ~((N'(1) << (i + 1)) - N'(1));
    end

    // ------------------------------
    // Combinational priority logic
    // ------------------------------
    logic [W-1:0] w_grant_id;
    logic [N-1:0] w_req_masked;
    logic         w_any_masked;
    logic [N-1:0] w_req_sel;
    logic [N-1:0] w_nxt_grant;
    logic         w_grant_valid;

    // Agents above the last winner first; if none of them is requesting, wrap to
    // the full request vector. After agent N-1 wins the mask is all-zero, so the
    // scan restarts from agent 0.
    assign w_req_masked = request & w_win_mask_decode[r_last_grant];
    assign w_any_masked = |w_req_masked;
    assign w_req_sel    = w_any_masked ? w_req_masked : request;

    // Isolate lowest set bit (one-hot). Works for zero too (yields zero).
    assign w_nxt_grant  = w_req_sel & ((~w_req_sel) + {{(N-1){1'b0}}, 1'b1});

    assign grant = w_nxt_grant;
    assign w_grant_valid = |w_nxt_grant;
    assign grant_valid = w_grant_valid;

    // One-hot to index encoder (compact & synth-friendly)
    always_comb begin
        w_grant_id = r_last_grant; // don't-care if no grant; default to last
        for (int i = 0; i < N; i++) begin
            if (w_nxt_grant[i]) w_grant_id = i[W-1:0];
        end
    end
    assign grant_id = w_grant_id;

    // ------------------------------
    // State update
    // ------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_last_grant <= (W)'(N-1); // first pass starts at agent 0
        end else if (w_grant_valid) begin
            r_last_grant <= w_grant_id;
        end
    )


endmodule : arbiter_round_robin_simple
