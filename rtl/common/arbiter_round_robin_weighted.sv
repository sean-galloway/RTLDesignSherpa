`timescale 1ns / 1ps
/*
================================================================================
Weighted Round Robin Arbiter Complete Arbitration Rules
================================================================================

This module implements a parameterizable weighted round-robin arbiter with 
dynamic weight change support and optional ACK protocol. The arbiter combines
credit-based weighting with fair round-robin arbitration, ensuring each client
receives grants proportional to its assigned weight while preventing starvation.

Arbitration Rules:
------------------
Follow the arbitration rules for the round-robin arbiter for ACK and no-ACK modes.
This logic handles the weight management layer on top of the base round-robin arbiter.

Parameter Configuration:
-----------------------
- CLIENTS: Number of requesting clients (2 to N)
- WAIT_GNT_ACK: 0 = No-ACK mode, 1 = ACK mode (passed to base arbiter)
- MAX_LEVELS: Maximum weight value per client (1 to N)
- max_thresh: Packed weight values for all clients

Dynamic Weight Changes:
======================
Weights can be changed dynamically during operation. The arbiter will internally
block all new grants except the current pending grant until it is ACK'd, then
the weight updates can proceed safely.

Weight Change Protocol:
- WEIGHT_IDLE: Normal operation with current weights
- WEIGHT_BLOCK: Block new grants, wait for pending ACK completion
- WEIGHT_DRAIN: Brief settling period after ACK completion
- WEIGHT_UPDATE: Atomic weight update and credit replenishment
- WEIGHT_STABILIZE: Allow system to stabilize before resuming

Credit Based Weighting:
======================

Credit Management:
- Each client gets credits equal to its weight value
- Credits consumed when grants are issued (No-ACK) or ACK'd (ACK mode)
- Global replenish occurs when no requesting clients have credits
- Higher weight = more consecutive grants before yielding to others

Fairness Rules:
1. Clients with credits participate in round-robin arbitration
2. When multiple clients have credits: strict round-robin fairness enforced
3. When single client has credits: gets all grants (no masking needed)
4. Credit exhaustion triggers global replenish for all clients

No Ack Mode Weighting (WAIT_GNT_ACK = 0):
========================================

Grant Completion:
- Credits decremented immediately when grant issued
- Fast credit consumption enables rapid weight-based patterns
- Credit replenish happens when all requesting clients exhausted

Timing:
- Grant patterns follow weight ratios closely
- Example: weights [4,1,1,1] → pattern 4-1-1-1, replenish, repeat
- Maximum throughput maintained

Ack Mode Weighting (WAIT_GNT_ACK = 1):
=====================================

Grant Completion:
- Credits decremented only when ACK received for grant
- Slower credit consumption due to ACK latency
- Pending grants block weight updates until ACK completion

Ack Safe Weight Updates:
- Weight changes wait for pending ACK completion
- Prevents race conditions during weight transitions
- Ensures clean state for new weight configuration

Timing:
- Grant patterns depend on ACK timing
- Same-cycle ACKs enable optimal weight-based throughput
- Delayed ACKs stretch patterns but maintain weight ratios

Underlying Arbitration:
======================

Base Round Robin Arbiter:
- Uses standard arbiter_round_robin module for core arbitration
- Inherits all timing and protocol behaviors from base arbiter
- Weight layer filters requests and manages credit-based eligibility

Request Filtering:
- Only clients with credits (or during replenish) sent to base arbiter
- Round-robin fairness maintained among eligible clients
- Last-grant masking prevents consecutive grants when multiple eligible

Starvation Prevention:
=====================

Weight Based Fairness:
- Each client guaranteed service proportional to its weight
- Global replenish ensures no client starved indefinitely
- Round-robin fairness within each weight level

Bounded Waiting:
- Maximum wait time: sum of all other clients' weights
- Independent of weight change frequency or timing
- Credit system provides deterministic service guarantees

Throughput Optimization:
=======================

Efficient Patterns:
- No-ACK mode: Optimal weight-based grant sequences
- ACK mode: Weight ratios maintained despite ACK latency
- Single-client optimization: No masking when only one eligible

Weight Update Efficiency:
- Minimal disruption during weight changes
- Clean state transitions preserve fairness
- Fast resumption after weight updates

Error Conditions:
================
- Invalid weights: Handled by credit system (zero weight = no grants)
- Weight update timeout: FSM includes timeout protection
- Base arbiter errors: Inherited from underlying round-robin arbiter
- Credit underflow: Protected by comparison logic

Verification Considerations:
===========================
- Monitor weight ratio compliance over long sequences
- Verify clean weight transitions without grant loss
- Check base arbiter rule compliance (inherited)
- Validate credit accounting accuracy
- Test boundary conditions (all weights zero, single client, etc.)
- Confirm no grants during weight update states

================================================================================
*/

module arbiter_round_robin_weighted #(
    parameter int MAX_LEVELS = 16,
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    // short/computed parameters
    parameter int N = $clog2(CLIENTS),
    parameter int C = CLIENTS,
    parameter int MTW = MAX_LEVELS_WIDTH,
    parameter int CXMTW = CLIENTS*MAX_LEVELS_WIDTH
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              block_arb,
    input  logic [CXMTW-1:0]  max_thresh,

    input  logic [C-1:0]      request,
    input  logic [C-1:0]      grant_ack,

    output logic              grant_valid,
    output logic [C-1:0]      grant,
    output logic [N-1:0]      grant_id
);

    // =======================================================================
    // Weight Management FSM (Same as before)
    // =======================================================================

    typedef enum logic [2:0] {
        WEIGHT_IDLE        = 3'b000,  // Normal operation
        WEIGHT_BLOCK       = 3'b001,  // Block new grants
        WEIGHT_DRAIN       = 3'b010,  // Wait for pending grants to complete
        WEIGHT_UPDATE      = 3'b011,  // Atomic weight update
        WEIGHT_STABILIZE   = 3'b100   // Allow system to stabilize
    } weight_fsm_t;

    weight_fsm_t r_weight_state;
    logic [3:0] r_weight_timer;  // Timer for state transitions

    // =======================================================================
    // Weight Management with Shadow Registers (Same as before)
    // =======================================================================

    logic [CXMTW-1:0] r_safe_max_thresh;    // Active weights (shadow register)
    logic             w_weight_change_req;   // Weight change requested
    logic             w_pending_grants;      // Any grants pending completion

    // Detect weight change request
    assign w_weight_change_req = (max_thresh != r_safe_max_thresh);

    // Detect pending grants (for ACK mode)
    assign w_pending_grants = (WAIT_GNT_ACK == 1) ? (grant_valid && (grant_ack & grant) == '0) : 1'b0;

    // weight change FSM (same as before)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_weight_state <= WEIGHT_IDLE;
            r_safe_max_thresh <= {CXMTW{1'b1}};  // Default to weight=1 for all clients
            r_weight_timer <= 4'h0;
        end else begin
            case (r_weight_state)
                WEIGHT_IDLE: begin
                    if (w_weight_change_req) begin
                        r_weight_state <= WEIGHT_BLOCK;
                        r_weight_timer <= 4'h0;
                    end
                end

                WEIGHT_BLOCK: begin
                    // Block new grants, wait for current grants to complete
                    if (!w_pending_grants) begin
                        r_weight_state <= WEIGHT_DRAIN;
                        r_weight_timer <= 4'h2;  // Short drain period
                    end else if (r_weight_timer < 4'hF) begin
                        r_weight_timer <= r_weight_timer + 4'h1;
                    end else begin
                        // Timeout - force transition
                        r_weight_state <= WEIGHT_DRAIN;
                        r_weight_timer <= 4'h0;
                    end
                end

                WEIGHT_DRAIN: begin
                    // Wait for system to settle
                    if (r_weight_timer == 4'h0) begin
                        r_weight_state <= WEIGHT_UPDATE;
                    end else begin
                        r_weight_timer <= r_weight_timer - 4'h1;
                    end
                end

                WEIGHT_UPDATE: begin
                    // Atomic weight update
                    r_safe_max_thresh <= max_thresh;
                    r_weight_state <= WEIGHT_STABILIZE;
                    r_weight_timer <= 4'h3;  // Stabilization period
                end

                WEIGHT_STABILIZE: begin
                    // Allow system to stabilize after weight change
                    if (r_weight_timer == 4'h0) begin
                        r_weight_state <= WEIGHT_IDLE;
                    end else begin
                        r_weight_timer <= r_weight_timer - 4'h1;
                    end
                end

                default: begin
                    r_weight_state <= WEIGHT_IDLE;
                    r_weight_timer <= 4'h0;
                end
            endcase
        end
    end

    // =======================================================================
    // Proper Credit Management System
    // =======================================================================

    logic [MTW-1:0] r_credit_counter [C];        // Credit counters
    logic [C-1:0]   w_has_crd;                   // Credit availability
    logic [C-1:0]   w_req_post;                  // Post-block requests
    logic           w_weight_change_active;      // Weight change in progress

    // Global replenish logic - centralized decision making
    logic [C-1:0]   w_requesting_with_credits;   // Clients that are requesting AND have credits
    logic           w_global_replenish;          // Trigger global credit replenish
    logic [MTW-1:0] client_weight [C];           // Per-client weights (for easier access)

    assign w_req_post = block_arb ? '0 : request;
    assign w_weight_change_active = (r_weight_state != WEIGHT_IDLE);

    // Extract client weights for easier access
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_weight_extract
            assign client_weight[j] = r_safe_max_thresh[(j+1)*MTW-1 -: MTW];
        end
    endgenerate

    // Global replenish decision (centralized)
    always_comb begin
        w_requesting_with_credits = '0;
        for (int j = 0; j < CLIENTS; j++) begin
            // Client has credits AND is requesting AND has non-zero weight
            w_requesting_with_credits[j] = (r_credit_counter[j] > 0) &&
                                        w_req_post[j] &&
                                        (client_weight[j] > 0);
        end
    end

    // Global replenish: No requesting clients have credits, but some are requesting
    assign w_global_replenish = (w_requesting_with_credits == '0) &&
                            (w_req_post != '0) &&
                            (r_weight_state == WEIGHT_IDLE);

    // Credit availability and management
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_logic

            // Credit availability - has remaining credits AND weight > 0 AND normal operation
            assign w_has_crd[i] = (r_credit_counter[i] > 0) &&
                                    (client_weight[i] > 0) &&
                                    (r_weight_state == WEIGHT_IDLE);

            // Simplified and correct credit counter management
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    r_credit_counter[i] <= MTW'(1);  // Start with 1 credit (will be corrected on first replenish)
                end else begin
                    case (r_weight_state)
                        WEIGHT_IDLE: begin
                            if (w_global_replenish) begin
                                // Global replenish - reload all clients with their weights
                                r_credit_counter[i] <= client_weight[i];
                            end else if (grant[i] && grant_valid) begin
                                // Grant issued to this client
                                logic grant_completed;

                                if (WAIT_GNT_ACK == 0) begin
                                    grant_completed = 1'b1;  // Immediate completion
                                end else begin
                                    grant_completed = grant_ack[i];  // Wait for ACK
                                end

                                if (grant_completed && r_credit_counter[i] > 0) begin
                                    // Simple decrement - can reach zero
                                    r_credit_counter[i] <= r_credit_counter[i] - MTW'(1);
                                end
                            end
                        end

                        WEIGHT_UPDATE: begin
                            // Reset credits to new weights during weight update
                            if (client_weight[i] > 0) begin
                                r_credit_counter[i] <= client_weight[i];  // Set to new weight
                            end else begin
                                r_credit_counter[i] <= MTW'(0);  // Disable client
                            end
                        end

                        default: begin
                            // During weight change states, preserve credits
                            // No changes to credit counters
                        end
                    endcase
                end
            end
        end
    endgenerate

    // =======================================================================
    // Request Masking (Proper Grant Logic with Fairness)
    // =======================================================================

    logic [C-1:0]   w_mask_req;               // Filtered requests to sub-arbiter
    logic [C-1:0]   w_requesting_eligible;    // Clients eligible for grants
    logic [C-1:0]   r_last_grant;             // Last grant from sub-arbiter

    // masking to prevent consecutive grants
    logic [C-1:0]   r_actual_last_grant;      // Track what was actually granted
    logic [C-1:0]   w_clients_with_credits_count;
    logic           w_multiple_eligible;      // Multiple clients eligible (need fairness)

    // Count how many clients have credits AND are requesting
    always_comb begin
        w_clients_with_credits_count = '0;
        for (int k = 0; k < CLIENTS; k++) begin
            if (w_requesting_eligible[k]) begin
                w_clients_with_credits_count[k] = 1'b1;
            end
        end
    end

    // Check if multiple clients are eligible (need fairness enforcement)
    assign w_multiple_eligible = ($countones(w_clients_with_credits_count) > 1);

    // Track the actual last grant (what was actually granted, not sub-arbiter's pointer)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_actual_last_grant <= '0;
        end else if (r_weight_state == WEIGHT_IDLE) begin
            if (grant_valid && |grant) begin
                if (WAIT_GNT_ACK == 0) begin
                    // No-ACK mode: Update masking immediately for next request evaluation
                    // But only if multiple clients are eligible for fairness
                    if (w_multiple_eligible) begin
                        r_actual_last_grant <= grant;
                    end else begin
                        // If only one client eligible, don't mask (let it keep getting grants)
                        r_actual_last_grant <= '0;
                    end
                end else begin
                    // ACK mode: Use normal update timing
                    r_actual_last_grant <= grant;
                end
            end else if (w_global_replenish) begin
                r_actual_last_grant <= '0;   // Clear on replenish for fresh start
            end
        end else begin
            // During weight changes, clear the last grant to avoid stale masking
            r_actual_last_grant <= '0;
        end
    end

    // Request masking logic with proper fairness
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_request_logic

            // Clients eligible for grants: requesting AND (has credits OR global replenish)
            assign w_requesting_eligible[j] = w_req_post[j] &&
                                            ((w_has_crd[j]) ||
                                                (w_global_replenish && client_weight[j] > 0));

            // Request masking for sub-arbiter:
            // 1. Client must be requesting and eligible
            // 2. If multiple clients eligible, exclude last granted for fairness
            // 3. If only one client eligible, ignore masking (let it have all grants)
            // 4. Only apply during normal operation
            assign w_mask_req[j] = w_requesting_eligible[j] &&
                                    (r_weight_state == WEIGHT_IDLE) &&
                                    (!w_multiple_eligible || !r_actual_last_grant[j]);
        end
    endgenerate

    // =======================================================================
    // FIXED: Sub-Arbiter Instance - instantiate the base round-robin arbiter
    // =======================================================================

    logic w_sub_block_arb;  // Block signal for sub-arbiter

    // Block sub-arbiter during weight changes
    assign w_sub_block_arb = (r_weight_state != WEIGHT_IDLE);

    // CORRECTED: Use the actual arbiter_round_robin module instead of non-existent subinst
    arbiter_round_robin #(
        .CLIENTS         (CLIENTS),
        .WAIT_GNT_ACK    (WAIT_GNT_ACK)
    ) u_base_arbiter (
        .clk             (clk),
        .rst_n           (rst_n),
        .block_arb       (w_sub_block_arb),
        .request         (w_mask_req),
        .grant_ack       (grant_ack),
        .grant_valid     (grant_valid),
        .grant           (grant),
        .grant_id        (grant_id),
        .last_grant      (r_last_grant)
    );

    // =======================================================================
    // Debug and Monitoring
    // =======================================================================

    // synthesis translate_off

    // grant and replenish monitoring
    always @(posedge clk) begin
        if (r_weight_state == WEIGHT_IDLE) begin
            // Monitor global replenish events
            if (w_global_replenish) begin
                $display("GLOBAL_REPLENISH at %0t: All clients reloaded", $time);
                $display("  request=0x%h, requesting_with_credits=0x%h",
                        w_req_post, w_requesting_with_credits);
                for (int i = 0; i < CLIENTS; i++) begin
                    $display("    Client %0d: weight=%0d, credit_before=%0d, credit_after=%0d",
                            i, client_weight[i], r_credit_counter[i], client_weight[i]);
                end
            end

            // grant monitoring with masking debug
            if (grant_valid && |grant) begin
                $display("MAIN_ARBITER GRANT at %0t: client=%0d, grant=0x%h", $time, grant_id, grant);
                $display("  eligible=0x%h, mask_req=0x%h, actual_last=0x%h",
                        w_requesting_eligible, w_mask_req, r_actual_last_grant);
                $display("  multiple_eligible=%0b, has_crd=0x%h",
                        w_multiple_eligible, w_has_crd);

                // Check for potential consecutive grants
                if (|(r_actual_last_grant & grant)) begin
                    $warning("POTENTIAL CONSECUTIVE GRANT: client %0d granted again, last=0x%h, current=0x%h",
                            grant_id, r_actual_last_grant, grant);
                end
            end

            // Monitor grant stalls
            if ((request != '0) && (grant == '0) && !block_arb) begin
                $warning("Grant stall detected: request=0x%h, mask_req=0x%h at %0t",
                        request, w_mask_req, $time);
                $display("  has_crd=0x%h, eligible=0x%h, global_replenish=%0b",
                        w_has_crd, w_requesting_eligible, w_global_replenish);
                $display("  actual_last_grant=0x%h, multiple_eligible=%0b, weight_state=%s",
                        r_actual_last_grant, w_multiple_eligible, r_weight_state.name());

                // Show per-client debug info
                for (int i = 0; i < CLIENTS; i++) begin
                    $display("    Client %0d: request=%0b, weight=%0d, credit=%0d, has_crd=%0b, eligible=%0b, masked=%0b",
                            i, request[i], client_weight[i], r_credit_counter[i], w_has_crd[i],
                            w_requesting_eligible[i], !w_mask_req[i]);
                end
            end
        end
    end

    // weight change monitoring (same as before)
    always @(posedge clk) begin
        if (r_weight_state != WEIGHT_IDLE) begin
            $display("WEIGHT_FSM at %0t: state=%s, timer=%0d, pending=%0b",
                    $time, r_weight_state.name(), r_weight_timer, w_pending_grants);

            if (r_weight_state == WEIGHT_UPDATE) begin
                $display("  Weight Update:");
                $display("    Old: 0x%h", r_safe_max_thresh);
                $display("    New: 0x%h", max_thresh);
                for (int i = 0; i < CLIENTS; i++) begin
                    logic [MTW-1:0] old_weight = r_safe_max_thresh[(i+1)*MTW-1 -: MTW];
                    logic [MTW-1:0] new_weight = max_thresh[(i+1)*MTW-1 -: MTW];
                    if (old_weight != new_weight) begin
                        $display("      Client %0d: %0d -> %0d (credit was %0d)",
                                i, old_weight, new_weight, r_credit_counter[i]);
                    end
                end
            end
        end
    end

    // synthesis translate_on

endmodule : arbiter_round_robin_weighted
