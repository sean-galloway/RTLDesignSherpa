// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_matrix
// Purpose: Matrix (rotation-in-distributed-state) fair arbiter.
//   Priority is stored as a CLIENTS×CLIENTS bit matrix M where M[i][j]=1 means
//   requester i currently outranks requester j. Only the CLIENTS*(CLIENTS-1)/2
//   upper-triangle bits are stored; the lower triangle is combinational:
//   M[j][i] = ~M[i][j].
//
// Documentation: docs/markdown/rtl-common/arbiter_matrix.md
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
    // Parameters
    // =======================================================================
    // CLIENTS:
    //   Description: Number of requesting clients
    //   Type: int
    //   Range: 1 to 1024 (practical limit)
    //   Default: 4
    //   Constraints: Must be >= 1
    //
    // WAIT_GNT_ACK:
    //   Description: ACK protocol mode selection
    //   Type: int
    //   Range: 0 or 1
    //   Default: 0
    //   Values:
    //     0 = No-ACK mode (grants are single-cycle pulses)
    //     1 = ACK mode (grant held until the granted client acknowledges)
    //
    // N:
    //   Description: Derived parameter for grant_id width
    //   Type: int
    //   Default: $clog2(CLIENTS), guarded to 1 for CLIENTS==1
    //   Constraints: Automatically calculated, do not override

    // =======================================================================
    // Ports
    // =======================================================================
    // Inputs:
    //   clk:            Clock input (rising edge active)
    //   rst_n:          Asynchronous active-low reset
    //   block_arb:      Block arbitration (active-high, immediate effect)
    //   request[CLIENTS-1:0]:  Request vector (one bit per client)
    //   grant_ack[CLIENTS-1:0]: Grant acknowledgment vector (ACK mode only)
    //
    // Outputs:
    //   grant_valid:    Grant outputs are valid (high when grant asserted)
    //   grant[CLIENTS-1:0]:  One-hot grant vector (exactly one bit set when valid)
    //   grant_id[N-1:0]:     Binary-encoded winner client ID
    //   last_grant[CLIENTS-1:0]: Previous cycle's grant (for debugging)

    // =======================================================================
    // Timing and Behavior
    // =======================================================================
    // No-ACK Mode (WAIT_GNT_ACK = 0):
    //   Latency: 1 cycle from request to registered grant
    //   Throughput: Up to 100% (one grant every cycle if requests present)
    //   Grant Duration: Exactly 1 cycle
    //   Matrix Update: On every grant, the winner drops to lowest priority
    //
    // ACK Mode (WAIT_GNT_ACK = 1):
    //   Latency: 1 cycle to issue grant + variable ACK delay
    //   Throughput: Limited by ACK latency
    //   Grant Duration: Held until the granted client asserts grant_ack
    //   Same-cycle ACK handoff: When the current grant is acknowledged, the next
    //     waiting requester is granted in the same cycle if any other client is
    //     requesting. The matrix is updated for the retiring winner before the
    //     next winner is computed.
    //   Foreign-ack immunity: Only the grant_ack bit belonging to the currently
    //     granted client can retire the grant.
    //
    // Reset:
    //   M[i][j] = 1 for all i < j, so requester 0 has the highest priority and
    //   requester CLIENTS-1 the lowest. The first grant after reset with all
    //   clients requesting goes to client 0.
    //
    // Fairness Guarantee:
    //   Any persistently requesting client is served within CLIENTS consecutive
    //   grants (strong fairness).

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
                // ACK mode: single-client reduction. Same-cycle re-grant on ACK
                // if the lone client is still requesting.
                if (grant_valid == 1'b0) begin
                    grant_valid   <= w_should_grant;
                    grant         <= w_should_grant;
                    grant_id      <= '0;
                    last_grant    <= grant;
                    r_pending_ack <= w_should_grant;
                end else if (!w_ack_received) begin
                    // hold current grant until ACK arrives
                end else begin
                    // ACK received: re-grant immediately if still requesting,
                    // otherwise clear.
                    grant_valid   <= w_req;
                    grant         <= w_req;
                    grant_id      <= '0;
                    last_grant    <= grant;
                    r_pending_ack <= w_req;
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

    // Compute the one-hot grant vector from a matrix and a request vector.
    // g[i] = req[i] AND (for all j!=i: NOT(req[j] AND M[j][i]))
    function automatic logic [CLIENTS-1:0] compute_grant_vec(
        logic [MATRIX_BITS-1:0] m,
        logic [CLIENTS-1:0] req
    );
        logic [CLIENTS-1:0] g;
        logic outranked;
        for (int i = 0; i < CLIENTS; i++) begin
            outranked = 1'b0;
            for (int j = 0; j < CLIENTS; j++) begin
                if (i != j) begin
                    if (req[j] && matrix_get(m, j, i))
                        outranked = 1'b1;
                end
            end
            g[i] = req[i] && !outranked;
        end
        return g;
    endfunction

    // Convert a one-hot grant vector to a binary ID.
    function automatic logic [N-1:0] onehot_to_id(logic [CLIENTS-1:0] g);
        logic [N-1:0] id;
        id = '0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (g[i]) id = i[N-1:0];
        end
        return id;
    endfunction

    // =======================================================================
    // Request gating
    // =======================================================================
    logic [CLIENTS-1:0] w_requests_gated;
    logic               w_any_requests;

    assign w_requests_gated = block_arb ? '0 : request;
    assign w_any_requests   = |w_requests_gated;

    // Registered grant ID (declared early because the post-ACK matrix update
    // needs it for same-cycle handoff computation).
    logic [N-1:0] r_grant_id;

    // =======================================================================
    // Combinational grant computation
    // =======================================================================
    // Two grant computations are performed so that ACK-mode same-cycle handoff
    // can pick the next winner from the post-ACK matrix in the same clock cycle.
    logic [CLIENTS-1:0] w_grant_current_vec;
    logic               w_grant_current_valid;
    logic [N-1:0]       w_grant_current_id;

    logic [MATRIX_BITS-1:0] w_matrix_after_ack;
    logic [CLIENTS-1:0]     w_grant_next_vec;
    logic                   w_grant_next_valid;
    logic [N-1:0]           w_grant_next_id;

    assign w_grant_current_vec   = compute_grant_vec(r_matrix, w_requests_gated);
    assign w_grant_current_valid = |w_grant_current_vec;
    assign w_grant_current_id    = onehot_to_id(w_grant_current_vec);

    assign w_matrix_after_ack    = matrix_update(r_matrix, int'(r_grant_id));
    assign w_grant_next_vec      = compute_grant_vec(w_matrix_after_ack, w_requests_gated);
    assign w_grant_next_valid    = |w_grant_next_vec;
    assign w_grant_next_id       = onehot_to_id(w_grant_next_vec);

    // =======================================================================
    // ACK-mode detection
    // =======================================================================
    logic w_ack_received;

    assign grant_id = r_grant_id;

    if (WAIT_GNT_ACK == 1) begin : gen_ack
        // Foreign-ack immunity: only the currently granted client's ack bit can
        // retire the held grant.
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
                grant       <= w_grant_current_vec;
                grant_valid <= w_grant_current_valid;
                r_grant_id  <= w_grant_current_id;

                if (w_grant_current_valid) begin
                    r_matrix <= matrix_update(r_matrix, int'(w_grant_current_id));
                end
            end else begin
                // ACK mode: hold grant until the granted client acknowledges.
                if (grant_valid == 1'b0) begin
                    if (w_grant_current_valid && w_any_requests) begin
                        grant       <= w_grant_current_vec;
                        grant_valid <= 1'b1;
                        r_grant_id  <= w_grant_current_id;
                    end else begin
                        grant       <= '0;
                        grant_valid <= 1'b0;
                        r_grant_id  <= '0;
                    end
                end else if (!w_ack_received) begin
                    // Hold current grant until ACK arrives.
                end else begin
                    // ACK received: update the matrix for the retiring winner
                    // and, if any other client is requesting, hand off to the
                    // next winner in the same cycle.
                    r_matrix <= w_matrix_after_ack;
                    if (w_grant_next_valid && w_any_requests) begin
                        grant       <= w_grant_next_vec;
                        grant_valid <= 1'b1;
                        r_grant_id  <= w_grant_next_id;
                    end else begin
                        grant       <= '0;
                        grant_valid <= 1'b0;
                        r_grant_id  <= '0;
                    end
                end
            end
        end
    )

    end // gen_multi_client

endmodule : arbiter_matrix
