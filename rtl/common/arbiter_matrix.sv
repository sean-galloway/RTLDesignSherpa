// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_matrix
// Purpose: Matrix (rotation-in-distributed-state) fair arbiter.
//   Priority is stored as an N×N bit matrix M where M[i][j]=1 means requester i
//   outranks requester j. Only the N(N-1)/2 upper-triangle bits are stored;
//   the lower triangle is combinational: M[j][i] = ~M[i][j].
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module arbiter_matrix #(
    parameter int CLIENTS      = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Guarded so CLIENTS==1 elaborates cleanly: $clog2(1)=0 creates [-1:0]
    // vectors that break Verilator (ASCRANGE).
    parameter int N = (CLIENTS > 1) ? $clog2(CLIENTS) : 1
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                block_arb,
    input  logic [CLIENTS-1:0]  request,
    input  logic [CLIENTS-1:0]  grant_ack,
    output logic                grant_valid,
    output logic [CLIENTS-1:0]  grant,
    output logic [N-1:0]        grant_id,
    output logic [CLIENTS-1:0]  last_grant
);

    // =======================================================================
    // Single-client degenerate case
    // =======================================================================
    if (CLIENTS == 1) begin : gen_single_client
        logic r_pending_ack;
        logic w_req;
        logic w_ack_received;
        logic w_can_grant;
        logic w_should_grant;

        assign w_req          = request[0] && !block_arb;
        assign w_ack_received = (WAIT_GNT_ACK == 1) ? (r_pending_ack && grant_ack[0]) : 1'b0;
        assign w_can_grant    = (WAIT_GNT_ACK == 1) ? (!r_pending_ack || w_ack_received) : 1'b1;
        assign w_should_grant = w_req && w_can_grant;

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                grant_valid   <= 1'b0;
                last_grant    <= '0;
                r_pending_ack <= 1'b0;
            end else if (WAIT_GNT_ACK == 0) begin
                // No-ACK: registered request -> grant
                grant_valid   <= w_should_grant;
                grant         <= w_should_grant;
                grant_id      <= '0;
                last_grant    <= grant;
                r_pending_ack <= 1'b0;
            end else begin
                // ACK mode: single-client reduction of arbiter_round_robin rules
                if (grant_valid == 1'b0) begin
                    grant_valid   <= w_should_grant;
                    grant         <= w_should_grant;
                    grant_id      <= '0;
                    last_grant    <= grant;
                    r_pending_ack <= w_should_grant;
                end else if (!w_ack_received) begin
                    // hold current grant until ACK
                end else begin
                    // ACK received: clear, allow re-grant next cycle
                    grant_valid   <= 1'b0;
                    grant         <= 1'b0;
                    grant_id      <= '0;
                    last_grant    <= grant;
                    r_pending_ack <= 1'b0;
                end
            end
        )
    end else begin : gen_multi_client

    // =======================================================================
    // Upper-triangle matrix state
    // =======================================================================
    // r_matrix stores M[i][j] for i < j.  M[i][j]=1 => i outranks j.
    // Reset sets M[i][j]=1 for all i<j, giving requester 0 the highest
    // priority and requester CLIENTS-1 the lowest.
    localparam int MATRIX_BITS = (CLIENTS * (CLIENTS - 1)) / 2;

    logic [MATRIX_BITS-1:0] r_matrix;

    // Linear index of (row, col) in the packed upper-triangle vector.
    // Sum of bits in rows above 'row' = row*CLIENTS - row*(row+1)/2.
    function automatic int matrix_idx(int row, int col);
        return (row * CLIENTS) - (row * (row + 1)) / 2 + (col - row - 1);
    endfunction

    // Combinational read of the conceptual full matrix.
    // Returns 1 iff a outranks b.  For a==b the value is a don't-care; return 0.
    function automatic logic matrix_get(
        logic [MATRIX_BITS-1:0] m,
        int a,
        int b
    );
        if (a == b) return 1'b0;
        if (a < b)  return m[matrix_idx(a, b)];
        else        return ~m[matrix_idx(b, a)];
    endfunction

    // Update matrix for a grant to winner k (Dally & Towles ch17 §18.5):
    //   row k cleared  -> for all j>k, M[k][j] = 0  (k loses to higher indices)
    //   column k set   -> for all i<k, M[i][k] = 1  (lower indices outrank k)
    // Result: winner k drops to the lowest priority.
    function automatic logic [MATRIX_BITS-1:0] matrix_update(
        logic [MATRIX_BITS-1:0] m,
        int winner
    );
        logic [MATRIX_BITS-1:0] nxt;
        int i, j;
        nxt = m;
        for (j = winner + 1; j < CLIENTS; j++) begin
            nxt[matrix_idx(winner, j)] = 1'b0;
        end
        for (i = 0; i < winner; i++) begin
            nxt[matrix_idx(i, winner)] = 1'b1;
        end
        return nxt;
    endfunction

    // =======================================================================
    // Request gating
    // =======================================================================
    logic [CLIENTS-1:0] w_requests_gated;
    logic               w_any_requests;

    assign w_requests_gated = block_arb ? '0 : request;
    assign w_any_requests   = |w_requests_gated;

    // =======================================================================
    // Combinational grant computation
    // =======================================================================
    // g[i] = req[i] AND (for all j!=i: NOT(req[j] AND M[j][i]))
    // A valid tournament matrix guarantees exactly one one-hot winner whenever
    // at least one request is present.
    logic [CLIENTS-1:0] w_grant_raw;
    logic [CLIENTS-1:0] w_outranked_by;

    always_comb begin
        for (int i = 0; i < CLIENTS; i++) begin
            w_outranked_by[i] = 1'b0;
            for (int j = 0; j < CLIENTS; j++) begin
                if (i != j) begin
                    if (w_requests_gated[j] && matrix_get(r_matrix, j, i))
                        w_outranked_by[i] = 1'b1;
                end
            end
            w_grant_raw[i] = w_requests_gated[i] && !w_outranked_by[i];
        end
    end

    logic               w_winner_valid;
    logic [N-1:0]       w_winner_id;
    logic [CLIENTS-1:0] w_next_grant;

    assign w_winner_valid = |w_grant_raw;
    assign w_next_grant   = w_grant_raw;

    always_comb begin
        w_winner_id = '0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (w_grant_raw[i]) w_winner_id = i[N-1:0];
        end
    end

    // =======================================================================
    // ACK-mode detection
    // =======================================================================
    logic [N-1:0] r_grant_id;
    logic         w_ack_received;

    assign grant_id = r_grant_id;

    if (WAIT_GNT_ACK == 1) begin : gen_ack
        assign w_ack_received = grant_valid && grant_ack[r_grant_id];
    end else begin : gen_no_ack
        assign w_ack_received = 1'b0;
    end

    // =======================================================================
    // Registered outputs and matrix state update
    // =======================================================================
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            grant       <= '0;
            grant_valid <= 1'b0;
            last_grant  <= '0;
            r_grant_id  <= '0;
            r_matrix    <= '1;   // M[i][j]=1 for all i<j
        end else begin
            last_grant <= grant;

            if (WAIT_GNT_ACK == 0) begin
                // No-ACK: issue a one-cycle grant every cycle a winner exists.
                grant       <= w_next_grant;
                grant_valid <= w_winner_valid;
                r_grant_id  <= w_winner_id;

                if (w_winner_valid) begin
                    r_matrix <= matrix_update(r_matrix, int'(w_winner_id));
                end
            end else begin
                // ACK mode: hold grant until the granted client acknowledges.
                if (grant_valid == 1'b0) begin
                    if (w_winner_valid && w_any_requests) begin
                        grant       <= w_next_grant;
                        grant_valid <= 1'b1;
                        r_grant_id  <= w_winner_id;
                    end else begin
                        grant       <= '0;
                        grant_valid <= 1'b0;
                        r_grant_id  <= '0;
                    end
                end else if (!w_ack_received) begin
                    // Hold current grant until ACK arrives.
                end else begin
                    // ACK received: retire the current grant and rotate the
                    // winner to the lowest priority.
                    grant       <= '0;
                    grant_valid <= 1'b0;
                    r_grant_id  <= '0;
                    r_matrix    <= matrix_update(r_matrix, int'(r_grant_id));
                end
            end
        end
    )

    end // gen_multi_client

endmodule : arbiter_matrix
