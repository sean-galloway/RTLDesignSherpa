// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_round_robin_simple
// Purpose: Arbiter Round Robin Simple module
//
// Documentation: docs/markdown/RTLCommon/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Generic rotating-priority arbiter with masking/rotation (no if/case ladders in priority path)
// - Parameterizable number of agents N (N >= 1)
// - Remembers last granted index in a flop (r_last_grant)
// - Uses rotation and lowest-set-bit isolate: x & (~x + 1)
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
    // Combinational priority logic
    // ------------------------------
    logic [W-1:0] w_grant_id;
    logic [N-1:0] w_rot_req;
    logic [N-1:0] w_rot_sel;
    logic [N-1:0] w_nxt_grant;
    logic         w_grant_valid;

    // Shift amount = last_grant + 1 (mod N), renamed per your request.
    logic [W-1:0] w_shift_amount;       // 0..N-1
    assign w_shift_amount = (r_last_grant == (W)'(N-1)) ? '0 : (r_last_grant + 1);

    // Rotate the request window so that agent (last_grant+1) lands at bit 0, then
    // take the lowest set bit, then rotate back.
    //
    // The direction matters and used to be backwards. Rotating the request LEFT by
    // s maps rotated bit j to original agent (j - s) mod N, so the scan started at
    // agent (N - s) = (N - last - 1) instead of (last + 1). That is a REFLECTION of
    // the priority pointer, not a rotation, and a reflection composed with itself is
    // the identity -- so the pointer oscillated between two positions forever.
    // With N=4 and all four agents requesting it granted 0,3,0,3,... and agents 1
    // and 2 were NEVER served. Rotating RIGHT first maps rotated bit j to agent
    // (j + s) mod N, so the scan starts at (last + 1) and advances, which is what
    // round-robin means.
    always_comb begin
        if (w_shift_amount == '0) begin
            w_rot_req = request;
        end else begin
            w_rot_req = (request >> w_shift_amount) | (request << ((W)'(N) - w_shift_amount));
        end
        // Isolate lowest set bit (one-hot). Works for zero too (yields zero).
        w_rot_sel = w_rot_req & ((~w_rot_req) + {{(N-1){1'b0}}, 1'b1});

        // Rotate back by the same amount to restore original bit positions
        if (w_shift_amount == '0) begin
            w_nxt_grant = w_rot_sel;
        end else begin
            w_nxt_grant = (w_rot_sel << w_shift_amount) | (w_rot_sel >> ((W)'(N) - w_shift_amount));
        end
    end

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
