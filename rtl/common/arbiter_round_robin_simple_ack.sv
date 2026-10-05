// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_round_robin_simple_ack
// Purpose: Arbiter Round Robin Simple module with grant/ack handshake
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

// Rotating-priority arbiter with a req/gnt/ack handshake.
// Same priority datapath as arbiter_round_robin_simple (win-mask above the last
// winner, fall back to unmasked requests, lowest-set-bit isolate); the difference
// is that the grant is REGISTERED and HELD until the granted agent returns grant_ack.
//
// - Parameterizable number of agents N (N >= 1)
// - grant appears the cycle after the winning request is seen, then stays
//   asserted (one-hot) until grant_ack[grant_id] is sampled high
// - grant_ack bits for agents that are not currently granted are ignored
// - On the ack cycle the arbiter re-arbitrates among the OTHER requesters, so a
//   waiting agent is granted on the very next cycle (back-to-back, no bubble).
//   If no other agent is requesting, the grant CLEARS for one cycle even when the
//   acked agent still requests -- the same contract as arbiter_round_robin Rule 3:
//   the ack completes the transfer, after which the requester may legally drop
//   its request, and re-granting it in the ack cycle would hold a grant it no
//   longer wants (the monbus_arbiter formal proof fails without this bubble).
// - Agents must hold request until they see grant; a request dropped in the
//   cycle before the grant registers is still granted and must still be acked.
// - Prefixes: w_* = wires, r_* = flops

`include "reset_defs.svh"
module arbiter_round_robin_simple_ack #(
    parameter int unsigned N = 4,
    // Guarded so N=1 elaborates: $clog2(1) is 0, which makes [W-1:0] a [-1:0] vector.
    parameter int unsigned W = (N > 1) ? $clog2(N) : 1
) (
    input  logic          clk,
    input  logic          rst_n,         // active-low reset
    input  logic [N-1:0]  request,       // request bits [N-1:0]
    input  logic [N-1:0]  grant_ack,     // per-agent ack; only the granted agent's bit counts
    output logic          grant_valid,   // a grant is outstanding
    output logic [N-1:0]  grant,         // one-hot grant, held until acked
    output logic [W-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
    // ------------------------------
    // State
    // ------------------------------
    logic [W-1:0] r_last_grant;         // index of current/most recent grant
    logic [N-1:0] r_grant;              // held one-hot grant
    logic         r_grant_valid;        // grant outstanding, waiting on ack

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
    logic [W-1:0] w_nxt_grant_id;
    logic [N-1:0] w_req_masked;
    logic         w_any_masked;
    logic [N-1:0] w_req_sel;
    logic [N-1:0] w_nxt_grant;
    logic         w_nxt_grant_valid;
    logic         w_ack;                // the granted agent acked this cycle
    logic         w_other_req;          // someone other than the granted agent requests

    // Agents above the last winner first; if none of them is requesting, wrap to
    // the full request vector. After agent N-1 wins the mask is all-zero, so the
    // scan restarts from agent 0.
    assign w_req_masked = request & w_win_mask_decode[r_last_grant];
    assign w_any_masked = |w_req_masked;
    assign w_req_sel    = w_any_masked ? w_req_masked : request;

    // Isolate lowest set bit (one-hot). Works for zero too (yields zero).
    assign w_nxt_grant  = w_req_sel & ((~w_req_sel) + {{(N-1){1'b0}}, 1'b1});

    assign w_nxt_grant_valid = |w_nxt_grant;

    // One-hot to index encoder (compact & synth-friendly)
    always_comb begin
        w_nxt_grant_id = r_last_grant; // don't-care if no grant; default to last
        for (int i = 0; i < N; i++) begin
            if (w_nxt_grant[i]) w_nxt_grant_id = i[W-1:0];
        end
    end

    // ------------------------------
    // Handshake
    // ------------------------------
    assign w_ack       = r_grant_valid && |(grant_ack & r_grant);
    assign w_other_req = |(request & ~r_grant);

    assign grant       = r_grant;
    assign grant_valid = r_grant_valid;
    assign grant_id    = r_last_grant;   // tracks the held grant while grant_valid

    // ------------------------------
    // State update
    // ------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_last_grant  <= (W)'(N-1); // first pass starts at agent 0
            r_grant       <= '0;
            r_grant_valid <= 1'b0;
        end else if (!r_grant_valid) begin
            // Idle: load the next winner (or stay idle if nobody requests).
            r_grant       <= w_nxt_grant;
            r_grant_valid <= w_nxt_grant_valid;
            if (w_nxt_grant_valid) begin
                r_last_grant <= w_nxt_grant_id;
            end
        end else if (w_ack) begin
            if (w_other_req) begin
                // Rule 4: hand off back-to-back. The acked agent is masked out
                // (it is the last winner), so the winner is one of the others.
                r_grant       <= w_nxt_grant;
                r_grant_valid <= w_nxt_grant_valid;
                r_last_grant  <= w_nxt_grant_id;
            end else begin
                // Rule 3: only the acked agent (or nobody) requests -> clear.
                r_grant       <= '0;
                r_grant_valid <= 1'b0;
            end
        end
        // else: hold r_grant until the granted agent acks
    )


endmodule : arbiter_round_robin_simple_ack
