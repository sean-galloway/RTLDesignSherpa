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
    // Local Parameters for Magic Numbers
    // =======================================================================
    localparam int WEIGHT_STABILIZE_CYCLES = 3;  // Stabilization period after weight change
    localparam int WEIGHT_DRAIN_CYCLES = 2;      // Drain period before weight update
    localparam int WEIGHT_TIMEOUT_CYCLES = 15;   // Timeout for weight change operations

    // =======================================================================
    // Weight Management FSM
    // =======================================================================

    typedef enum logic [4:0] {
        WEIGHT_IDLE        = 5'b00001,  // Normal operation
        WEIGHT_BLOCK       = 5'b00010,  // Block new grants
        WEIGHT_DRAIN       = 5'b00100,  // Wait for pending grants to complete
        WEIGHT_UPDATE      = 5'b01000,  // Atomic weight update
        WEIGHT_STABILIZE   = 5'b10000   // Allow system to stabilize
    } weight_fsm_t;

    weight_fsm_t r_weight_state;
    logic [3:0]  r_weight_timer;  // Timer for state transitions

    // =======================================================================
    // Weight Management with Shadow Registers
    // =======================================================================

    logic [CXMTW-1:0] r_safe_max_thresh;     // Active weights (shadow register)
    logic             w_weight_change_req;   // Weight change requested
    logic             w_pending_grants;      // Any grants pending completion

    // Detect weight change request
    assign w_weight_change_req = (max_thresh != r_safe_max_thresh);

    // Detect pending grants (for ACK mode)
    assign w_pending_grants = (WAIT_GNT_ACK == 1) ? (grant_valid && (grant_ack & grant) == '0) : 1'b0;

    // Weight change FSM with local parameters
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_weight_state <= WEIGHT_IDLE;
            r_safe_max_thresh <= {CXMTW{1'b1}};  // Default to weight=1 for all clients
            r_weight_timer <= 4'h0;
        end else begin
            casez (r_weight_state)
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
                        r_weight_timer <= WEIGHT_DRAIN_CYCLES[3:0];
                    end else if (r_weight_timer < WEIGHT_TIMEOUT_CYCLES[3:0]) begin
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
                    r_weight_timer <= WEIGHT_STABILIZE_CYCLES[3:0];  // Use local parameter
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
    // Pre-computed Helper Signals (Optimizations)
    // =======================================================================

    logic [MTW-1:0] client_weight [C];           // Per-client weights (for easier access)
    logic           w_normal_operation;          // Normal operation state
    logic [C-1:0]   w_valid_clients;             // Clients with non-zero weights
    logic [C-1:0]   w_invalid_clients;           // Clients with zero weights
    logic [C-1:0]   w_req_post;                  // Post-block requests

    // Extract client weights for easier access
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_weights
            assign client_weight[j] = r_safe_max_thresh[(j+1)*MTW-1 -: MTW];
            assign w_valid_clients[j] = (client_weight[j] > 0);
            assign w_invalid_clients[j] = (client_weight[j] == 0);
        end
    endgenerate

    // commonly used conditions
    assign w_normal_operation = (r_weight_state == WEIGHT_IDLE);
    assign w_req_post = block_arb ? '0 : request;

    // =======================================================================
    // Credit Management System
    // =======================================================================

    logic [MTW-1:0] r_credit_counter [C];        // Credit counters
    logic [C-1:0]   w_has_crd;                   // Credit availability
    logic           w_global_replenish;

    // =======================================================================
    // Credit Counter Combinational Logic
    // =======================================================================

    logic [MTW-1:0] w_credit_counter [C];        // Next credit counter values
    logic [C-1:0]   w_grant_completed;           // Grant completion per client
    
    // Pre-compute grant completion for all clients
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_grant_completion
            assign w_grant_completed[i] = (WAIT_GNT_ACK == 0) ? 
                                         (grant[i] && grant_valid) :                    // No-ACK: immediate completion
                                         (grant[i] && grant_valid && grant_ack[i]);     // ACK mode: wait for ACK
        end
    endgenerate
    
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_combo_logic
            
            always_comb begin
                // Default: hold current value
                w_credit_counter[i] = r_credit_counter[i];
                
                case (r_weight_state)
                    WEIGHT_IDLE: begin
                        if (w_global_replenish) begin
                            // Global replenish - reload all clients with their weights
                            w_credit_counter[i] = client_weight[i];
                        end else if (w_grant_completed[i] && r_credit_counter[i] > 0) begin
                            // Grant completed for this client - decrement credit
                            w_credit_counter[i] = r_credit_counter[i] - MTW'(1);
                        end
                    end

                    WEIGHT_STABILIZE: begin
                        // Reset credits to new weights during weight update
                        if (client_weight[i] > 0) begin
                            w_credit_counter[i] = client_weight[i];  // Set to new weight
                        end else begin
                            w_credit_counter[i] = MTW'(0);  // Disable client
                        end
                    end

                    default: begin
                        // During weight change states, preserve credits
                        w_credit_counter[i] = r_credit_counter[i];
                    end
                endcase
            end
        end
    endgenerate

    // =======================================================================
    // Credit Counter Registers
    // =======================================================================

    // Pre-declare the signals outside the generate block
    logic [C-1:0] w_has_one_credit;      // Which clients have exactly 1 credit
    logic [C-1:0] w_has_any_credits;     // Which clients have any credits (> 0)
    logic         w_last_credit;         // Only ONE client has exactly 1 credit left

    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_registers

            // Credit availability - has remaining credits AND weight > 0 AND normal operation
            assign w_has_crd[i] = (r_credit_counter[i] > 0) &&
                                    (client_weight[i] > 0) &&
                                    (w_normal_operation);
            
            // Per-client credit state detection
            assign w_has_one_credit[i] = (r_credit_counter[i] == MTW'(1)) && (client_weight[i] > 0);
            assign w_has_any_credits[i] = (r_credit_counter[i] > MTW'(0)) && (client_weight[i] > 0);

            // Simple register - just assigns the combinational value
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    r_credit_counter[i] <= MTW'(1);  // Start with 1 credit (will be corrected on first replenish)
                end else begin
                    r_credit_counter[i] <= w_credit_counter[i];  // Simple assignment from combo logic
                end
            end
        end
    endgenerate

    // Global last credit detection (outside generate block)
    // w_last_credit = 1 when exactly ONE client has exactly 1 credit left
    assign w_last_credit = ($countones(w_has_any_credits) == 1) &&     // Only 1 client has any credits
                            ($countones(w_has_one_credit) == 1) &&     // Only 1 client has exactly 1 credit  
                            (w_has_any_credits == w_has_one_credit);   // Same client for both conditions
    // replenish the counters on a grant for the last credit or when idle
    assign w_global_replenish = (w_normal_operation && !w_pending_grants && (w_last_credit && grant_valid));

    // =======================================================================
    // Request Masking (Proper Grant Logic with Fairness)
    // =======================================================================

    logic [C-1:0]   w_mask_req;               // Filtered requests to sub-arbiter
    logic [C-1:0]   w_mask_multi_req;
    logic [C-1:0]   w_mask_last_client;
    logic [C-1:0]   w_requesting_eligible;    // Clients eligible for grants
    logic [C-1:0]   r_last_grant;             // Last grant from sub-arbiter

    // masking to prevent consecutive grants
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

    // Request masking logic with proper fairness
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_request_logic

            // Clients eligible for grants: requesting AND (has credits OR global replenish)
            // assign w_requesting_eligible[j] = w_req_post[j] &&
            //                                 ((w_has_crd[j]) ||
            //                                     (r_global_replenish && client_weight[j] > 0));
            assign w_requesting_eligible[j] = w_req_post[j] &&
                                                ((w_has_crd[j]) ||
                                                    (w_global_replenish && w_valid_clients[j]));
            // Request masking for sub-arbiter:
            // 1. Client must be requesting and eligible
            // 2. If multiple clients eligible, exclude last granted for fairness
            // 3. If only one client eligible, ignore masking (let it have all grants)
            // 4. Only apply during normal operation
            assign w_mask_multi_req[j] = w_requesting_eligible[j] && !grant[j];
            assign w_mask_last_client[j] = (!w_multiple_eligible && w_requesting_eligible[j] && (r_credit_counter[j] > MTW'(1)));
            assign w_mask_req[j] = w_mask_multi_req[j] || w_mask_last_client[j];
        end
    endgenerate

    // =======================================================================
    // Sub-Arbiter Instance - instantiate the base round-robin arbiter
    // =======================================================================

    logic w_sub_block_arb;  // Block signal for sub-arbiter

    // Block sub-arbiter during weight changes
    assign w_sub_block_arb = (r_weight_state != WEIGHT_IDLE);

    // Use the actual arbiter_round_robin module
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

endmodule : arbiter_round_robin_weighted
