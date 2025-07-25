`timescale 1ns / 1ps

/*
================================================================================
Round Robin Arbiter Complete Arbitration Rules
================================================================================

This module implements a parameterizable round-robin arbiter with optional ACK
protocol support. The arbiter ensures fairness by rotating priority among clients
after each grant, preventing starvation while maintaining high throughput.

Core Round Robin Algorithm:
---------------------------
1. Uses dual-priority scheme with masked and unmasked request processing
2. Priority mask rotates after each successful grant to ensure fairness
3. Lower-indexed clients have tie-breaking priority within the same priority level
4. Supports both immediate grants (no-ACK) and transaction-based grants (ACK mode)

Parameter Configuration:
-----------------------
- CLIENTS: Number of requesting clients (2 to N)
- WAIT_GNT_ACK: 0 = No-ACK mode, 1 = ACK mode

No Ack Mode Rules (WAIT_GNT_ACK = 0):
====================================

Grant Generation:
- Grant issued immediately when client wins arbitration
- Grant valid for exactly one cycle
- No handshake required - grant implies acceptance

Priority Rotation:
- Round-robin mask updates immediately when grant is issued
- Next cycle, priority rotates to next client in sequence
- Rotation order: 0 → 1 → 2 → ... → (CLIENTS-1) → 0

Arbitration Logic:
1. First check masked requests (clients above last granted client)
2. If no masked winners, check all requests (wrap-around)
3. Winner selection uses find-first-set on processed requests
4. Grant and grant_id output immediately when winner found

Timing:
- Grant appears same cycle as arbitration decision
- No waiting for acknowledgment
- Continuous operation - can grant every cycle if requests present

FAIRNESS GUARANTEE:
- Each requesting client guaranteed service within CLIENTS cycles
- No starvation possible if client continuously requests
- Statistical fairness maintained over time

ACK MODE RULES (WAIT_GNT_ACK = 1):
==================================

GRANT GENERATION:
- Grant issued when client wins arbitration AND no ACK pending
- Grant remains asserted until corresponding ACK received
- Only one grant can be pending at a time (no overlapping grants)

ACK PROTOCOL:
- Testbench must assert grant_ack with matching grant vector
- ACK can be asserted same cycle as grant (same-cycle ACK)
- ACK can be delayed multiple cycles after grant
- ACK must be deasserted after one cycle (pulse protocol)

Priority Rotation:
- Round-robin mask updates when ACK is received (not when grant issued)
- Rotation happens on ACK completion, maintaining fairness
- Prevents priority advancement during pending transactions

Arbitration Logic:
1. If ACK pending: maintain current grant, wait for ACK
2. If no ACK pending and requests present: perform normal arbitration
3. Winner gets grant, enters pending state until ACK received
4. ACK completion triggers priority rotation and enables next arbitration

Dead Cycle Handling:
- Single request + ACK completion = mandatory dead cycle
- Prevents phantom grants when request deasserts after ACK
- Multiple requests + ACK completion = immediate next grant (no dead cycle)
- Optimizes throughput while maintaining protocol correctness

Ack Timing Scenarios:
Same-cycle ACK:  GRANT ←→ ACK (same cycle, optimal throughput)
Delayed ACK:     GRANT → ... → ACK (multi-cycle transaction)
Back-to-back:    ACK1 → GRANT2 → ACK2 (rapid succession)

Fairness Guarantee:
- Each requesting client guaranteed service within CLIENTS transactions
- No starvation even with varying ACK delays
- ACK delays don't affect fairness order, only overall throughput

Common Rules Both Modes:
=========================

Block Arbitration:
- block_arb signal immediately stops all grant generation
- Pending ACK transactions continue normally during block
- Block has priority over all arbitration logic

Request Handling:
- Requests can assert/deassert at any time
- Requests must be stable during grant cycle for proper operation
- No minimum assertion time required

Grant Properties:
- grant vector is always one-hot (exactly one bit set)
- grant_id indicates binary-encoded winner client
- grant_valid indicates when grant/grant_id are meaningful
- last_grant provides previous cycle's grant for debugging

Reset Behavior:
- All state cleared on reset (masks, pending ACK, grants)
- First post-reset arbitration starts with client 0 having highest priority
- Deterministic startup behavior for consistent testing

Mask Update Algorithm:
- After client N wins: mask = ~((1 << N) - 1)
- This masks clients 0 through N, giving priority to N+1 and above
- Wrap-around handled by unmasked arbiter when no masked winners

Starvation Prevention:
- Round-robin rotation guarantees bounded waiting time
- Maximum wait: (CLIENTS - 1) grants for any continuously requesting client
- Independent of request patterns or system load

Throughput Optimization:
- No-ACK mode: Up to 100% throughput (grant every cycle)
- ACK mode: Throughput limited by ACK latency and protocol
- Same-cycle ACKs enable near-optimal throughput in ACK mode
- Back-to-back transactions supported for maximum efficiency

Error Conditions:
- Multiple simultaneous grants: Design prevents this (one-hot guarantee)
- ACK timeout: External monitor responsibility
- Invalid grant_id: Protected by parameter bounds checking
- Request during block: Ignored until block released

Verification Considerations:
- Monitor grant fairness over rolling windows
- Verify round-robin order compliance with competition
- Check ACK protocol timing in ACK mode
- Validate no grants during block_arb assertion
- Confirm one-hot grant vector property
- Test boundary conditions (1 client, max clients)

================================================================================
*/

module arbiter_round_robin #(
    parameter int CLIENTS      = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter int N = $clog2(CLIENTS)
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
    // Pre computed mask lookup table
    // =======================================================================

    logic [CLIENTS-1:0] w_mask_decode [CLIENTS];
    logic [CLIENTS-1:0] w_win_mask_decode [CLIENTS];

    // Generate mask lookup at elaboration time (no logic cost)
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_mask_lut
            // Proper mask generation for round-robin fairness
            // After client i wins, mask clients 0 through i (give priority to i+1 and above)
            assign w_mask_decode[i] = (CLIENTS'(1) << (i)) - CLIENTS'(1);
            assign w_win_mask_decode[i] = ~((CLIENTS'(1) << (i + 1)) - CLIENTS'(1));
        end
    endgenerate

    // =======================================================================
    // Streamlined state registers
    // =======================================================================

    logic [N-1:0]       r_last_winner;        // Track last winner (smaller than full mask)
    logic               r_mask_valid;         // Is there a valid mask state?
    logic               r_pending_ack;        // ACK mode state
    logic [N-1:0]       r_pending_client;     // Which client has pending ACK

    // =======================================================================
    // Fast request preprocessing
    // =======================================================================

    logic [CLIENTS-1:0] w_requests_gated;
    logic [CLIENTS-1:0] w_requests_masked;
    logic [CLIENTS-1:0] w_requests_unmasked;
    logic               w_any_requests;
    logic               w_any_masked_requests;

    // Single LUT level for request gating
    assign w_requests_gated = block_arb ? '0 : request;
    assign w_any_requests = |w_requests_gated;

    // Fast mask application using LUT
    assign w_requests_masked = r_mask_valid ?
                            (w_requests_gated & w_win_mask_decode[r_last_winner]) : '0;
    assign w_requests_unmasked = w_requests_gated;
    assign w_any_masked_requests = |w_requests_masked;

    // =======================================================================
    // Single stage priority encoder
    // Use external optimized priority encoder module
    // =======================================================================

    logic [N-1:0] w_winner;
    logic         w_winner_valid;

    arbiter_priority_encoder #(
        .CLIENTS            (CLIENTS),
        .N                  (N)
    ) u_priority_encoder (
        .requests_masked    (w_requests_masked),
        .requests_unmasked  (w_requests_unmasked),
        .any_masked_requests(w_any_masked_requests),
        .winner             (w_winner),
        .winner_valid       (w_winner_valid)
    );

    // =======================================================================
    // Ack detection
    // =======================================================================
    logic w_ack_received;
    logic w_can_grant;

    generate
        if (WAIT_GNT_ACK == 1) begin : gen_ack_optimized

            // Fast ACK detection (single LUT)
            assign w_ack_received = r_pending_ack && grant_ack[r_pending_client];

            // Grant permission logic
            assign w_can_grant = !r_pending_ack || w_ack_received;

            // ACK state management
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    r_pending_ack <= 1'b0;
                    r_pending_client <= '0;
                end else begin
                    if (!r_pending_ack && w_winner_valid && w_any_requests && w_can_grant) begin
                        // New grant issued
                        r_pending_ack <= 1'b1;
                        r_pending_client <= w_winner;
                    end else if (w_ack_received) begin
                        // ACK received, clear pending
                        r_pending_ack <= 1'b0;
                        r_pending_client <= '0;
                    end
                end
            end

        end else begin : gen_no_ack_optimized
            assign w_ack_received = 1'b0;
            assign w_can_grant = 1'b1;
        end
    endgenerate

    // =======================================================================
    // Mask update
    // Use LUT instead of arithmetic for mask generation
    // =======================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_last_winner <= '0;
            r_mask_valid <= 1'b0;
        end else begin
            if (WAIT_GNT_ACK == 0) begin
                // No-ACK: update when grant issued
                if (w_winner_valid && w_any_requests && w_can_grant) begin
                    r_last_winner <= w_winner;
                    r_mask_valid <= 1'b1;
                end
            end else begin
                // ACK mode: update on ACK completion
                if (w_ack_received) begin
                    r_last_winner <= r_pending_client;
                    r_mask_valid <= 1'b1;
                end else if (!r_pending_ack && w_winner_valid && w_any_requests) begin
                    // First grant
                    r_last_winner <= w_winner;
                    r_mask_valid <= 1'b1;
                end
            end
        end
    end

    // =======================================================================
    // Output generation
    // Minimize final output stage logic depth
    // =======================================================================
    logic w_should_grant;
    logic [CLIENTS-1:0] w_next_grant;
    logic [N-1:0] w_next_grant_id;
    logic w_next_grant_valid;

    // Grant decision logic (minimal depth)
    assign w_should_grant = w_winner_valid && w_any_requests && w_can_grant;

    // Grant vector generation (direct decode)
    always_comb begin
        w_next_grant = '0;
        if (w_should_grant) begin
            w_next_grant[w_winner] = 1'b1;
        end
    end

    assign w_next_grant_id = w_should_grant ? w_winner : '0;
    assign w_next_grant_valid = w_should_grant;

    // Final output registers
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant <= '0;
            grant_id <= '0;
            grant_valid <= 1'b0;
            last_grant <= '0;
        end else begin
            last_grant <= grant;

            if (WAIT_GNT_ACK == 0) begin
                // No-ACK mode: direct assignment
                grant <= w_next_grant;
                grant_id <= w_next_grant_id;
                grant_valid <= w_next_grant_valid;

            end else begin
                // ACK mode: handle pending grants
                if (r_pending_ack && !w_ack_received) begin
                    // Maintain current grant until ACK
                    // grant, grant_id, grant_valid unchanged
                end else if (w_ack_received) begin
                    // ACK received: handle dead cycle for single request
                    if (w_any_requests && $countones(w_requests_gated) > 1) begin
                        // Multiple requests: immediate next grant
                        grant <= w_next_grant;
                        grant_id <= w_next_grant_id;
                        grant_valid <= w_next_grant_valid;
                    end else begin
                        // Single/no request: dead cycle
                        grant <= '0;
                        grant_id <= '0;
                        grant_valid <= 1'b0;
                    end
                end else begin
                    // Normal grant issuance
                    grant <= w_next_grant;
                    grant_id <= w_next_grant_id;
                    grant_valid <= w_next_grant_valid;
                end
            end
        end
    end

endmodule : arbiter_round_robin
