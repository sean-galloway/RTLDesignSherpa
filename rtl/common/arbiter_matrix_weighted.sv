// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_matrix_weighted
// Purpose: Weighted matrix arbiter.  Combines the strong-fairness matrix
//   arbiter with per-client credit counters so a winner receives up to its
//   weight in consecutive grants before the priority matrix rotates.
//
// Documentation: docs/markdown/rtl-common/arbiter_matrix_weighted.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module arbiter_matrix_weighted #(
    parameter int MAX_LEVELS = 16,
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Derived - do not override (declared here so the port declarations
    // can use them; strict front ends reject body localparams in port ranges)
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    parameter int N = (CLIENTS > 1) ? $clog2(CLIENTS) : 1,
    parameter int C = CLIENTS,
    parameter int MTW = MAX_LEVELS_WIDTH,
    parameter int CXMTW = CLIENTS * MAX_LEVELS_WIDTH
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              block_arb,
    input  logic [CXMTW-1:0]  max_thresh,

    input  logic [C-1:0]      request,
    input  logic [C-1:0]      grant_ack,

    output logic              grant_valid,
    output logic [C-1:0]      grant,
    output logic [N-1:0]      grant_id,
    output logic [C-1:0]      last_grant
);

    // =======================================================================
    // Parameters
    // =======================================================================
    // MAX_LEVELS:
    //   Description: Maximum weight value per client
    //   Type: int
    //   Range: 1 to 256
    //   Default: 16
    //   Constraints: Higher values = finer QoS granularity, more credit bits.
    //                Credit counter width = $clog2(MAX_LEVELS).
    //
    // CLIENTS:
    //   Description: Number of requesting clients
    //   Type: int
    //   Range: 1 to 1024 (practical limit)
    //   Default: 4
    //   Constraints: Determines arbitration width and credit counter array size
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
    // MAX_LEVELS_WIDTH:
    //   Description: Width in bits for credit counters ($clog2(MAX_LEVELS))
    //   Type: int
    //   Default: $clog2(MAX_LEVELS)
    //   Constraints: Derived, do not override
    //
    // N:
    //   Description: Derived bit width of grant_id
    //   Type: int
    //   Default: $clog2(CLIENTS), guarded to 1 for CLIENTS==1
    //   Constraints: Derived, do not override
    //
    // C / MTW / CXMTW:
    //   Description: Convenience aliases used in port and local signal widths
    //   Type: int
    //   Constraints: Derived, do not override

    // =======================================================================
    // Ports
    // =======================================================================
    // Inputs:
    //   clk:            Clock input (rising edge active)
    //   rst_n:          Asynchronous active-low reset
    //   block_arb:      Block arbitration (active-high, immediate effect)
    //   max_thresh[CXMTW-1:0]:  Packed weight values for all clients
    //                            Format: {weight[N-1], ..., weight[1], weight[0]}
    //                            Each weight: MAX_LEVELS_WIDTH bits
    //   request[C-1:0]:         Request vector (one bit per client)
    //   grant_ack[C-1:0]:       Grant acknowledgment vector (ACK mode only)
    //
    // Outputs:
    //   grant_valid:    Grant outputs are valid (high when grant asserted)
    //   grant[C-1:0]:   One-hot grant vector (exactly one bit set when valid)
    //   grant_id[N-1:0]:     Binary-encoded winner client ID
    //   last_grant[C-1:0]:   Previous cycle's grant (for debugging)

    // =======================================================================
    // Timing and Behavior
    // =======================================================================
    // No-ACK Mode (WAIT_GNT_ACK = 0):
    //   Latency: 1 cycle from request to registered grant, plus a 1-cycle
    //            credit-load bubble immediately after reset.
    //   Throughput: Up to 100% (one grant every cycle if requests present)
    //   Grant Duration: Exactly 1 cycle
    //   Matrix Update: Deferred until the winner's credit counter reaches 0.
    //                  A client with weight W can win up to W consecutive
    //                  grants before dropping to lowest priority.
    //
    // ACK Mode (WAIT_GNT_ACK = 1):
    //   Latency: 1 cycle to issue grant + variable ACK delay
    //   Throughput: Limited by ACK latency
    //   Grant Duration: Held until the granted client asserts grant_ack
    //   Same-cycle ACK handoff: When the current grant is acknowledged, the next
    //     waiting requester is granted in the same cycle if any other client is
    //     eligible.  The matrix is updated only when the acknowledged grant
    //     exhausts the winner's credits; otherwise the same winner re-wins.
    //   Foreign-ack immunity: Only the grant_ack bit belonging to the currently
    //     granted client can retire the held grant.
    //
    // Reset:
    //   M[i][j] = 1 for all i < j, so requester 0 has the highest priority and
    //   requester CLIENTS-1 the lowest.  Credit counters reset to 0 and are
    //   loaded from max_thresh on the first cycle after reset, so the first
    //   round is weighted.
    //
    // Weight Semantics:
    //   - Each client has a down-counter loaded from its max_thresh field.
    //   - A grant completion decrements the winner's counter.
    //   - No-ACK mode: completion is the grant cycle itself.
    //   - ACK mode: completion is the cycle grant_ack for the winner arrives.
    //   - When a counter reaches 0 it is reloaded from max_thresh and the
    //     matrix is rotated for that client.
    //   - A weight of 0 disables the client immediately (its counter is forced
    //     to 0 and it is never eligible).
    //     NOTE: This differs from arbiter_round_robin_weighted, which uses a
    //     multi-cycle WEIGHT_BLOCK/DRAIN/UPDATE/STABILIZE FSM to avoid pointer
    //     masking hazards.  In this matrix design eligibility is simply
    //     (request && credit>0), and rotation only occurs on a grant, so an
    //     immediate credit clear cannot corrupt an in-flight arbitration or
    //     leave a stale pointer masked.  The deviation is intentional and safe.
    //   - Weight changes take effect at the next reload for that client.
    //
    // Fairness Guarantee:
    //   Any persistently requesting client with non-zero weight is served within
    //   CLIENTS consecutive rotation events (strong fairness), and each
    //   rotation event delivers up to weight consecutive grants to its winner.

    // =======================================================================
    // Weight unpacking
    // =======================================================================
    logic [MTW-1:0] w_client_weight [C];
    logic [C-1:0]   w_valid_clients;

    for (genvar j = 0; j < CLIENTS; j++) begin : gen_unpack_weights
        assign w_client_weight[j] = max_thresh[(j+1)*MTW-1 -: MTW];
        assign w_valid_clients[j] = (w_client_weight[j] > 0);
    end

    // =======================================================================
    // Single-client degenerate case
    // =======================================================================
    if (CLIENTS == 1) begin : gen_single_client
        logic [MTW-1:0] r_credit_counter;
        logic           w_has_credit;
        logic           w_req;
        logic           w_ack_received;
        logic           w_can_grant;
        logic           w_should_grant;
        logic [MTW-1:0] w_credit_next;

        assign w_has_credit    = (r_credit_counter > 0) && w_valid_clients[0];
        assign w_req           = request[0] && !block_arb && w_has_credit;
        assign w_ack_received  = (WAIT_GNT_ACK == 1) ? (grant_valid && grant_ack[0]) : 1'b0;
        assign w_can_grant     = (WAIT_GNT_ACK == 1) ? (!grant_valid || w_ack_received) : 1'b1;
        assign w_should_grant  = w_req && w_can_grant;

        always_comb begin
            if (w_client_weight[0] == 0)
                w_credit_next = MTW'(0);
            else if (r_credit_counter == 0)
                w_credit_next = w_client_weight[0];
            else if (grant_valid && ((WAIT_GNT_ACK == 0) || grant_ack[0]))
                w_credit_next = (r_credit_counter == 1) ? w_client_weight[0]
                                                        : r_credit_counter - 1;
            else
                w_credit_next = r_credit_counter;
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                grant_valid       <= 1'b0;
                grant             <= '0;
                grant_id          <= '0;
                last_grant        <= '0;
                r_credit_counter  <= MTW'(0);
            end else begin
                last_grant <= grant;
                r_credit_counter <= w_credit_next;

                if (WAIT_GNT_ACK == 0) begin
                    grant       <= w_should_grant;
                    grant_valid <= w_should_grant;
                    grant_id    <= '0;
                end else begin
                    if (grant_valid == 1'b0) begin
                        grant       <= w_should_grant;
                        grant_valid <= w_should_grant;
                        grant_id    <= '0;
                    end else if (!w_ack_received) begin
                        // hold current grant until ACK arrives
                    end else begin
                        grant       <= w_req;
                        grant_valid <= w_req;
                        grant_id    <= '0;
                    end
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

    // Update matrix for a grant to winner k (Dally & Towles ch17):
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
    // Credit counters and eligibility
    // =======================================================================
    logic [MTW-1:0] r_credit_counter [C];
    logic [C-1:0]   w_has_credit;
    logic [C-1:0]   w_requests_gated;
    logic [C-1:0]   w_requests_eligible;
    logic           w_any_requests_eligible;

    for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_eligible
        assign w_has_credit[i]        = (r_credit_counter[i] > 0) && w_valid_clients[i];
        assign w_requests_gated[i]    = block_arb ? 1'b0 : request[i];
        assign w_requests_eligible[i] = w_requests_gated[i] && w_has_credit[i];
    end

    assign w_any_requests_eligible = |w_requests_eligible;

    // =======================================================================
    // Registered grant state
    // =======================================================================
    logic [N-1:0] r_grant_id;

    // =======================================================================
    // Grant completion detection
    // =======================================================================
    // No-ACK: completion is the grant cycle itself.
    // ACK:    completion is when the owner's grant_ack bit is asserted.
    logic [C-1:0] w_grant_completed;

    for (genvar i = 0; i < CLIENTS; i++) begin : gen_grant_completed
        assign w_grant_completed[i] = (WAIT_GNT_ACK == 0) ?
            (grant[i] && grant_valid) :
            (grant[i] && grant_valid && grant_ack[i]);
    end

    // =======================================================================
    // Next credit values
    // =======================================================================
    logic [MTW-1:0] w_credit_next [C];

    for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_next
        always_comb begin
            // Weight=0 disables the client and purges any stale credits.
            if (w_client_weight[i] == 0) begin
                w_credit_next[i] = MTW'(0);
            end else if (r_credit_counter[i] == 0) begin
                // Idle (or freshly-enabled) client loads its weight.
                w_credit_next[i] = w_client_weight[i];
            end else if (w_grant_completed[i]) begin
                if (r_credit_counter[i] == 1)
                    w_credit_next[i] = w_client_weight[i];  // reload on exhaustion
                else
                    w_credit_next[i] = r_credit_counter[i] - 1;
            end else begin
                w_credit_next[i] = r_credit_counter[i];
            end
        end
    end

    // =======================================================================
    // Combinational grant computation
    // =======================================================================
    // Two grant computations are performed so that same-cycle handoff can pick
    // the next winner from the post-rotation matrix.  The registered outputs
    // must be driven from the *next* matrix state, otherwise the combinational
    // priority re-evaluates after the register update but the registered grant
    // captures the pre-update value and the winner gets one extra cycle.
    logic [CLIENTS-1:0] w_grant_current_vec;
    logic               w_grant_current_valid;
    logic [N-1:0]       w_grant_current_id;

    logic [MATRIX_BITS-1:0] w_matrix_next_no_ack;
    logic                   w_credit_exhausted_no_ack;

    logic [MATRIX_BITS-1:0] w_matrix_after_ack;
    logic                   w_ack_received;
    logic                   w_credit_exhausted_on_ack;

    logic [MATRIX_BITS-1:0] w_matrix_next;
    logic [CLIENTS-1:0]     w_grant_next_vec;
    logic                   w_grant_next_valid;
    logic [N-1:0]           w_grant_next_id;

    assign w_grant_current_vec   = compute_grant_vec(r_matrix, w_requests_eligible);
    assign w_grant_current_valid = |w_grant_current_vec;
    assign w_grant_current_id    = onehot_to_id(w_grant_current_vec);

    // No-ACK: rotate when the current grant exhausts the winner's credits.
    assign w_credit_exhausted_no_ack = grant_valid &&
                                       (r_credit_counter[r_grant_id] == MTW'(1));
    assign w_matrix_next_no_ack      = w_credit_exhausted_no_ack ?
                                       matrix_update(r_matrix, int'(r_grant_id)) :
                                       r_matrix;

    // =======================================================================
    // ACK-mode detection
    // =======================================================================
    assign grant_id = r_grant_id;

    if (WAIT_GNT_ACK == 1) begin : gen_ack
        // Foreign-ack immunity: only the currently granted client's ack bit can
        // retire the held grant.
        assign w_ack_received          = grant_valid && grant_ack[r_grant_id];
        assign w_credit_exhausted_on_ack = w_ack_received &&
                                           (r_credit_counter[r_grant_id] == MTW'(1));
    end else begin : gen_no_ack
        assign w_ack_received          = 1'b0;
        assign w_credit_exhausted_on_ack = 1'b0;
    end

    assign w_matrix_after_ack = w_credit_exhausted_on_ack ?
                                matrix_update(r_matrix, int'(r_grant_id)) :
                                r_matrix;

    // Select the matrix that will be committed this cycle and compute the
    // registered grant from that matrix so the priority rotation is visible
    // immediately on the following cycle.
    assign w_matrix_next      = (WAIT_GNT_ACK == 0) ? w_matrix_next_no_ack :
                                                   w_matrix_after_ack;
    assign w_grant_next_vec   = compute_grant_vec(w_matrix_next, w_requests_eligible);
    assign w_grant_next_valid = |w_grant_next_vec;
    assign w_grant_next_id    = onehot_to_id(w_grant_next_vec);

    // =======================================================================
    // Registered outputs and matrix/credit state update
    // =======================================================================
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            grant       <= '0;
            grant_valid <= 1'b0;
            last_grant  <= '0;
            r_grant_id  <= '0;
            r_matrix    <= '1;   // M[i][j]=1 for all i<j
            for (int i = 0; i < CLIENTS; i++) begin
                r_credit_counter[i] <= MTW'(0);
            end
        end else begin
            last_grant <= grant;

            // Credit counters update every cycle.
            for (int i = 0; i < CLIENTS; i++) begin
                r_credit_counter[i] <= w_credit_next[i];
            end

            if (WAIT_GNT_ACK == 0) begin
                // No-ACK: issue a one-cycle grant every cycle an eligible winner
                // exists.  Use the post-rotation matrix so the next grant
                // reflects the new priority immediately.
                grant       <= w_grant_next_vec;
                grant_valid <= w_grant_next_valid;
                r_grant_id  <= w_grant_next_id;
                r_matrix    <= w_matrix_next_no_ack;
            end else begin
                // ACK mode: hold grant until the granted client acknowledges.
                if (grant_valid == 1'b0) begin
                    if (w_grant_current_valid && w_any_requests_eligible) begin
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
                    // ACK received: rotate only if this ACK exhausted the
                    // winner's credits.  If the winner still has credits and
                    // keeps requesting, it re-wins in the same cycle.
                    r_matrix <= w_matrix_after_ack;
                    if (w_grant_next_valid && w_any_requests_eligible) begin
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

endmodule : arbiter_matrix_weighted
