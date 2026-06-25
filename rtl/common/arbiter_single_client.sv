// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_single_client
// Purpose: Degenerate one-client arbiter with the SAME grant/ack timing as
//          arbiter_round_robin (WAIT_GNT_ACK mode), for NUM_CHANNELS==1 builds.
//
// Description:
//   arbiter_round_robin underflows at CLIENTS==1 ($clog2(1)=0 -> grant_id[-1:0]),
//   so single-channel datapaths historically substituted a *combinational*
//   passthrough (grant = request). That passthrough does NOT reproduce the
//   round-robin arbiter's registered, ack-held grant lifecycle, which the AXI
//   read/write engines rely on for correct burst sequencing -- the mismatch
//   injects a bubble beat at every burst boundary. This module is the
//   "req/grant then hold for ack" single-client equivalent: it mirrors the
//   arbiter's WAIT_GNT_ACK always_ff rules exactly for one client (registered
//   grant, hold until ack, clear-then-regrant), so a 1-channel build behaves
//   identically to the >1-channel arbiter path.
//
// Notes:
//   - grant is one-hot of width 1 (== grant_valid); grant_id is always 0.
//   - WAIT_GNT_ACK=0 falls back to a registered request->grant (no ack hold).

`timescale 1ns / 1ps

module arbiter_single_client #(
    parameter int WAIT_GNT_ACK = 1
) (
    input  logic clk,
    input  logic rst_n,
    input  logic block_arb,
    input  logic request,      // single client's request
    input  logic grant_ack,    // single client's grant acknowledgment
    output logic grant_valid,
    output logic grant,        // one-hot, width 1 (== grant_valid)
    output logic grant_id      // always 0 (single client)
);

    logic r_pending_ack;
    logic w_req;
    logic w_ack_received;
    logic w_can_grant;
    logic w_should_grant;

    assign w_req          = request && !block_arb;
    assign w_ack_received = (WAIT_GNT_ACK == 1) ? (r_pending_ack && grant_ack) : 1'b0;
    assign w_can_grant    = (WAIT_GNT_ACK == 1) ? (!r_pending_ack || w_ack_received) : 1'b1;
    assign w_should_grant = w_req && w_can_grant;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant_valid   <= 1'b0;
            r_pending_ack <= 1'b0;
        end else if (WAIT_GNT_ACK == 0) begin
            // No-ACK: registered request -> grant
            grant_valid   <= w_should_grant;
            r_pending_ack <= 1'b0;
        end else begin
            // ACK mode -- single-client reduction of arbiter_round_robin rules.
            // (w_other_requests is always 0 with one client, so Rule 4 never
            // applies and Rule 3 simply clears.)
            if (grant_valid == 1'b0) begin
                // Rule 1: not granted -> grant if requesting
                grant_valid   <= w_should_grant;
                r_pending_ack <= w_should_grant;
            end else if (!w_ack_received) begin
                // Rule 2: granted, no ack -> hold
                grant_valid   <= 1'b1;
                r_pending_ack <= 1'b1;
            end else begin
                // Rule 3: granted, ack received -> clear (re-grant next cycle)
                grant_valid   <= 1'b0;
                r_pending_ack <= 1'b0;
            end
        end
    end

    assign grant    = grant_valid;
    assign grant_id = 1'b0;

endmodule
