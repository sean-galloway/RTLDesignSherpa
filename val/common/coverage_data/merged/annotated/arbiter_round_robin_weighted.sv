//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: arbiter_round_robin_weighted
        // Purpose: //   Weighted round-robin arbiter with credit-based QoS (Quality of Service) support.
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: arbiter_round_robin_weighted
        //==============================================================================
        // Description:
        //   Weighted round-robin arbiter with credit-based QoS (Quality of Service) support.
        //   Combines fair round-robin arbitration with configurable per-client weights to
        //   provide proportional bandwidth allocation. Each client receives grants proportional
        //   to its assigned weight while maintaining starvation-free operation. Supports optional
        //   ACK protocol and dynamic weight changes with atomic update semantics.
        //
        // Features:
        //   - Credit-based weighted arbitration (higher weight = more consecutive grants)
        //   - Fair round-robin among clients with equal credits
        //   - Starvation prevention (global credit replenishment)
        //   - Dynamic weight changes with atomic updates
        //   - Optional ACK protocol (WAIT_GNT_ACK=0/1)
        //   - No-ACK mode: Immediate grant completion
        //   - ACK mode: Grant held until acknowledged
        //   - Weight change FSM for race-free updates
        //   - Parameterized client count and weight range
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   CLIENTS:
        //     Description: Number of requesting clients
        //     Type: int
        //     Range: 2 to 32
        //     Default: 4
        //     Constraints: Determines arbitration width and credit counter array size
        //
        //   MAX_LEVELS:
        //     Description: Maximum weight value per client
        //     Type: int
        //     Range: 1 to 256
        //     Default: 16
        //     Constraints: Higher values = finer QoS granularity, more credit bits
        //                  Credit counter width = $clog2(MAX_LEVELS)
        //
        //   WAIT_GNT_ACK:
        //     Description: Enable ACK protocol for grant completion
        //     Type: int
        //     Range: 0 or 1
        //     Default: 0
        //     Constraints: 0 = No-ACK (immediate), 1 = ACK required
        //                  ACK mode adds latency but enables pipelined masters
        //
        //   Derived Parameters (localparam - computed automatically):
        //     MAX_LEVELS_WIDTH: Width in bits for credit counters ($clog2(MAX_LEVELS))
        //     N: Client ID width in bits ($clog2(CLIENTS))
        //     C: Convenience alias for CLIENTS (used in port widths)
        //     MTW: Convenience alias for MAX_LEVELS_WIDTH (used in port widths)
        //     CXMTW: Total width of packed weight array (CLIENTS * MAX_LEVELS_WIDTH)
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     clk:                            Clock input
        //     rst_n:                          Asynchronous active-low reset
        //     block_arb:                      Block all arbitration (external gate)
        //     max_thresh[CXMTW-1:0]:          Packed weight values for all clients
        //                                      Format: {weight[N-1], ..., weight[1], weight[0]}
        //                                      Each weight: MAX_LEVELS_WIDTH bits
        //     request[C-1:0]:                 Request vector (one-hot or multiple)
        //     grant_ack[C-1:0]:               Grant acknowledgment (ACK mode only)
        //
        //   Outputs:
        //     grant_valid:                    Grant output valid
        //     grant[C-1:0]:                   Grant vector (one-hot)
        //     grant_id[N-1:0]:                Grant client ID (binary encoded)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency:        2 cycles (credit calculation + round-robin arbitration)
        //   Throughput:     1 grant per cycle (max)
        //   Grant Hold:     No-ACK: 1 cycle, ACK: Until grant_ack asserted
        //   Weight Update:  3-15 cycles (FSM: BLOCK → DRAIN → UPDATE → STABILIZE)
        //   Reset:          Asynchronous (all credits → 1, weights → default)
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Credit-Based Weighting:
        //   - Each client has credit counter initialized to its weight value
        //   - Grant completion decrements credit counter:
        //     - No-ACK mode: Decrement when grant issued (same cycle)
        //     - ACK mode: Decrement when grant_ack received (delayed)
        //   - Clients with non-zero credits eligible for round-robin arbitration
        //   - Global replenish: When no requesting clients have credits, reload all
        //
        //   Arbitration Stages:
        //   1. **Credit Eligibility:** Only clients with credits > 0 can be granted
        //   2. **Round-Robin Selection:** Base arbiter selects among eligible clients
        //   3. **Grant Output:** Winning client receives grant (one-hot)
        //   4. **Credit Update:** Winner's credit decremented on completion
        //
        //   Weight Ratio Example (weights [4, 2, 1, 1]):
        //   - Client 0: 4 credits → gets 4 consecutive grants
        //   - Client 1: 2 credits → gets 2 consecutive grants
        //   - Client 2: 1 credit  → gets 1 grant
        //   - Client 3: 1 credit  → gets 1 grant
        //   - Pattern: 0,0,0,0, 1,1, 2, 3, [replenish], repeat
        //   - Bandwidth: Client 0 gets 50%, Client 1 gets 25%, Clients 2&3 get 12.5% each
        //
        //   Global Replenishment:
        //   - Triggered when: No requesting clients have remaining credits
        //   - Action: Reload all credit counters to their weight values
        //   - Effect: Restart weighted grant sequence
        //   - Prevents: Starvation (all clients eventually get replenished)
        //
        //   Dynamic Weight Changes:
        //   FSM ensures atomic weight updates without race conditions:
        //   1. **WEIGHT_IDLE** - Normal operation
        //   2. **WEIGHT_BLOCK** - Detect weight change, block new grants
        //   3. **WEIGHT_DRAIN** - Wait for pending ACK completion (2 cycles)
        //   4. **WEIGHT_UPDATE** - Atomic weight update, reset credits
        //   5. **WEIGHT_STABILIZE** - System stabilization (3 cycles)
        //   Total latency: ~5-8 cycles per weight change
        //
        //   Weight Change Safety (ACK Mode):
        //   - FSM waits for pending grant_ack before updating weights
        //   - Timeout protection (15 cycles) prevents FSM lockup
        //   - New weights activate only after clean state transition
        //
        //------------------------------------------------------------------------------
        // Wavedrom Timing Diagram:
        //------------------------------------------------------------------------------
        //   Weighted Arbitration (No-ACK, weights [4,2,1,1]):
        //
        //   {signal: [
        //     {name: 'clk',              wave: 'p...................'},
        //     {name: 'request[3:0]',     wave: 'x4..................', data: ['All']},
        //     {},
        //     {name: 'r_credit[0]',      wave: 'x.4.3.2.1.05.4.3.2.1', data: ['4','3','2','1','0','4','3','2','1']},
        //     {name: 'r_credit[1]',      wave: 'x.2.....1.03.2.....1', data: ['2','1','0','2','1']},
        //     {name: 'r_credit[2]',      wave: 'x.1.......01........', data: ['1','0','1']},
        //     {name: 'r_credit[3]',      wave: 'x.1.......01........', data: ['1','0','1']},
        //     {},
        //     {name: 'grant[3:0]',       wave: 'x.1.1.1.1.2.3.4.1.1.', data: ['C0','C0','C0','C0','C1','C2','C3','C0','C0']},
        //     {name: 'grant_valid',      wave: '0.1.................'},
        //     {},
        //     {name: 'w_global_replenish', wave: '0.........10........'},
        //     {name: 'Event',            wave: 'x.2.3...4.5.6.......', data: ['C0×4','C1×2','C2,C3×1','Replenish','Restart']}
        //   ],
        //   config: {skin: 'narrow'}}
        //
        //   Dynamic Weight Change (ACK mode, weights [2,2] → [3,1]):
        //
        //   {signal: [
        //     {name: 'clk',              wave: 'p....................'},
        //     {name: 'max_thresh',       wave: 'x2.........3.........', data: ['[2,2]','[3,1]']},
        //     {},
        //     {name: 'r_weight_state',   wave: 'x2.........3.4.5.6.2.', data: ['IDLE','BLOCK','DRAIN','UPDATE','STBL','IDLE']},
        //     {name: 'request[1:0]',     wave: 'x3...................', data: ['11']},
        //     {name: 'grant[1:0]',       wave: 'x1.2.1.2...........1.', data: ['C0','C1','C0','C1','C0']},
        //     {name: 'grant_ack[1:0]',   wave: '0.1.2.1.2...........1', data: ['A0','A1','A0','A1','A0']},
        //     {},
        //     {name: 'r_credit[0]',      wave: 'x.2.1.........3.2.1..', data: ['2','1','3','2','1']},
        //     {name: 'r_credit[1]',      wave: 'x.2.1.........1......', data: ['2','1','1']},
        //     {},
        //     {name: 'Event',            wave: 'x.2.......3...4.5.6..', data: ['Old [2,2]','Detect Δ','Update','Stabilize','Resume']}
        //   ],
        //   config: {skin: 'narrow'}}
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // 4-client arbiter with QoS weights: 8:4:2:1 (No-ACK mode)
        //   localparam int NUM_CLIENTS = 4;
        //   localparam int MAX_WEIGHT = 16;
        //   localparam int WEIGHT_W = $clog2(MAX_WEIGHT);
        //
        //   logic [NUM_CLIENTS-1:0] client_req, client_grant, client_ack;
        //   logic grant_vld;
        //   logic [$clog2(NUM_CLIENTS)-1:0] grant_idx;
        //   logic [NUM_CLIENTS*WEIGHT_W-1:0] qos_weights;
        //
        //   // Assign QoS weights (high priority = higher weight)
        //   assign qos_weights = {4'd1, 4'd2, 4'd4, 4'd8};  // {C3, C2, C1, C0}
        //
        //   arbiter_round_robin_weighted #(
        //       .CLIENTS(NUM_CLIENTS),
        //       .MAX_LEVELS(MAX_WEIGHT),
        //       .WAIT_GNT_ACK(0)           // No-ACK mode
        //   ) u_qos_arbiter (
        //       .clk        (clk),
        //       .rst_n      (rst_n),
        //       .block_arb  (1'b0),
        //       .max_thresh (qos_weights),
        //       .request    (client_req),
        //       .grant_ack  ('0),           // Unused in No-ACK mode
        //       .grant_valid(grant_vld),
        //       .grant      (client_grant),
        //       .grant_id   (grant_idx)
        //   );
        //
        //   // Dynamic weight adjustment example
        //   always_ff @(posedge clk) begin
        //       if (high_priority_event) begin
        //           qos_weights[7:0] <= 4'd15;  // Boost Client 0 weight
        //       end
        //   end
        //
        //   // ACK mode arbiter for pipelined masters
        //   arbiter_round_robin_weighted #(
        //       .CLIENTS(2),
        //       .MAX_LEVELS(8),
        //       .WAIT_GNT_ACK(1)            // ACK required
        //   ) u_ack_arbiter (
        //       .clk        (clk),
        //       .rst_n      (rst_n),
        //       .block_arb  (bus_busy),
        //       .max_thresh ({4'd3, 4'd5}),  // Weights [5, 3]
        //       .request    (m_req),
        //       .grant_ack  (m_done),        // Master completion signal
        //       .grant_valid(m_grant_vld),
        //       .grant      (m_grant),
        //       .grant_id   (m_id)
        //   );
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **Weight = 0:** Client effectively disabled (never granted)
        //   - **All weights = 0:** No grants issued (deadlock prevention via replenish)
        //   - Credit counters reset to weights during WEIGHT_STABILIZE state
        //   - No-ACK mode: Optimal for simple masters (no pipeline)
        //   - ACK mode: Required for pipelined/posted transaction masters
        //   - **Fairness guarantee:** All non-zero weight clients eventually served
        //   - Maximum starvation time: Sum of all other clients' weights
        //   - Weight update latency: 5-15 cycles depending on pending ACKs
        //   - **DO NOT** change weights every cycle (causes thrashing)
        //   - Recommended: Change weights only on policy updates (ms timescale)
        //   - Credit underflow protection: Comparison logic prevents negative credits
        //   - Base arbiter: Uses arbiter_round_robin internally
        //   - Synthesis: Credit counters map to registers, comparators to LUTs
        //   - **Critical path:** Credit comparison → request filtering → base arbiter
        //   - For high-speed designs, consider pipelining weight calculation
        //   - Weight change FSM timeout: 15 cycles (configurable via localparam)
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - arbiter_round_robin.sv - Base round-robin arbiter (used internally)
        //   - arbiter_round_robin_simple.sv - Lightweight RR arbiter (no weights)
        //   - arbiter_priority_encoder.sv - Fixed priority arbiter
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_arbiter_round_robin_weighted.py
        //   Run: pytest val/common/test_arbiter_round_robin_weighted.py -v
        //   Coverage: 94%
        //   Key Test Scenarios:
        //     - Weight ratio verification ([4,2,1,1] patterns)
        //     - Global credit replenishment
        //     - Dynamic weight changes (atomic updates)
        //     - ACK mode timing and weight updates
        //     - Zero weight handling (client disable)
        //     - Single client optimization
        //     - FSM timeout protection
        //     - Starvation prevention (all clients eventually served)
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        
        module arbiter_round_robin_weighted #(
            parameter int MAX_LEVELS = 16,
            parameter int CLIENTS = 4,
            parameter int WAIT_GNT_ACK = 0
        ) (
 590883     input  logic              clk,
%000007     input  logic              rst_n,
 000014     input  logic              block_arb,
%000002     input  logic [CXMTW-1:0]  max_thresh,
        
 003696     input  logic [C-1:0]      request,
%000000     input  logic [C-1:0]      grant_ack,
        
 074759     output logic              grant_valid,
 002898     output logic [C-1:0]      grant,
 021759     output logic [N-1:0]      grant_id
        );
        
            // =======================================================================
            // Derived Parameters (computed from parameters)
            // =======================================================================
            localparam int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS);  // Credit counter width
            localparam int N = $clog2(CLIENTS);                     // Client ID width
            localparam int C = CLIENTS;                             // Convenience alias for port widths
            localparam int MTW = MAX_LEVELS_WIDTH;                  // Convenience alias for weight width
            localparam int CXMTW = CLIENTS * MAX_LEVELS_WIDTH;      // Total packed weight array width
        
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
        
 000376     weight_fsm_t r_weight_state;
 000010     logic [3:0]  r_weight_timer;  // Timer for state transitions
        
            // =======================================================================
            // Weight Management with Shadow Registers
            // =======================================================================
        
%000004     logic [CXMTW-1:0] r_safe_max_thresh;     // Active weights (shadow register)
 000376     logic             w_weight_change_req;   // Weight change requested
 169473     logic             w_pending_grants;      // Any grants pending completion
        
            // Detect weight change request
            assign w_weight_change_req = (max_thresh != r_safe_max_thresh);
        
            // Detect pending grants (for ACK mode)
            assign w_pending_grants = (WAIT_GNT_ACK == 1) ? (grant_valid && (grant_ack & grant) == '0) : 1'b0;
        
            // Weight change FSM with local parameters
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
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
        
                        // verilator coverage_off
                        // DEFENSIVE: Illegal FSM state recovery
                        default: begin
                            r_weight_state <= WEIGHT_IDLE;
                            r_weight_timer <= 4'h0;
                        end
%000000                 // verilator coverage_on
                    endcase
                end
%000001     )
        
        
            // =======================================================================
%000002     // Pre-computed Helper Signals (Optimizations)
 000273     // =======================================================================
%000005 
%000006     logic [MTW-1:0] client_weight [C];           // Per-client weights (for easier access)
 000110     logic           w_normal_operation;          // Normal operation state
%000002     logic [C-1:0]   w_valid_clients;             // Clients with non-zero weights
%000004     logic [C-1:0]   w_invalid_clients;           // Clients with zero weights
 004224     logic [C-1:0]   w_req_post;                  // Post-block requests
        
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
%000000     // Credit Management System
 001669     // =======================================================================
 037364 
 000126     logic [MTW-1:0] r_credit_counter [C];        // Credit counters
 007733     logic [C-1:0]   w_has_crd;                   // Credit availability
 017346     logic           w_global_replenish;
        
            // =======================================================================
%000000     // Credit Counter Combinational Logic
 002898     // =======================================================================
        
 000126     logic [MTW-1:0] w_credit_counter [C];        // Next credit counter values
 012894     logic [C-1:0]   w_grant_completed;           // Grant completion per client
        
            // Pre-compute grant completion for all clients
            generate
                for (genvar i = 0; i < CLIENTS; i++) begin : gen_grant_completion
                    assign w_grant_completed[i] = (WAIT_GNT_ACK == 0) ?
                                                 (grant[i] && grant_valid) :                    // No-ACK: immediate completion
                                                 (grant[i] && grant_valid && grant_ack[i]);     // ACK mode: wait for ACK
                end
 001344     endgenerate
        
 6487988     generate
 000384         for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_combo_logic
 6487988 
 2197088             always_comb begin
 6487988                 // Default: hold current value
 2197088                 w_credit_counter[i] = r_credit_counter[i];
 568250 
 2197088                 case (r_weight_state)
 568250                     WEIGHT_IDLE: begin
 198960                         if (w_global_replenish) begin
                                    // Global replenish - reload all clients with their weights
 198960                             w_credit_counter[i] = client_weight[i];
 215763                         end else if (w_grant_completed[i] && r_credit_counter[i] > 0) begin
                                    // Grant completed for this client - decrement credit
 215763                             w_credit_counter[i] = r_credit_counter[i] - MTW'(1);
 017840                         end
                            end
 001344 
 005152                     WEIGHT_STABILIZE: begin
 001344                         // Reset credits to new weights during weight update
 000384                         if (client_weight[i] > 0) begin
 004768                             w_credit_counter[i] = client_weight[i];  // Set to new weight
 000384                         end else begin
 000384                             w_credit_counter[i] = MTW'(0);  // Disable client
 024884                         end
                            end
 024884 
 007216                     default: begin
                                // During weight change states, preserve credits
 007216                         w_credit_counter[i] = r_credit_counter[i];
                            end
                        endcase
                    end
                end
            endgenerate
        
            // =======================================================================
            // Credit Counter Registers
 001769     // =======================================================================
 001641 
 031856     // Pre-declare the signals outside the generate block
 007739     logic [C-1:0] w_has_one_credit;      // Which clients have exactly 1 credit
 007679     logic [C-1:0] w_has_any_credits;     // Which clients have any credits (> 0)
 000336     logic         w_last_credit;         // Only ONE client has exactly 1 credit left
        
            generate
 000096         for (genvar i = 0; i < CLIENTS; i++) begin : gen_credit_registers
        
                    // Credit availability - has remaining credits AND weight > 0 AND normal operation
                    assign w_has_crd[i] = (r_credit_counter[i] > 0) &&
                                            (client_weight[i] > 0) &&
                                            (w_normal_operation);
        
                    // Per-client credit state detection
                    assign w_has_one_credit[i] = (r_credit_counter[i] == MTW'(1)) && (client_weight[i] > 0);
                    assign w_has_any_credits[i] = (r_credit_counter[i] > MTW'(0)) && (client_weight[i] > 0);
        
                    // Simple register - just assigns the combinational value
                    `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                            r_credit_counter[i] <= MTW'(1);  // Start with 1 credit (will be corrected on first replenish)
 000336                 end else begin
                            r_credit_counter[i] <= w_credit_counter[i];  // Simple assignment from combo logic
                        end
 000096             )
        
                end
            endgenerate
        
            // Global last credit detection (outside generate block)
            // w_last_credit = 1 when exactly ONE client has exactly 1 credit left
            assign w_last_credit = ($countones(w_has_any_credits) == 1) &&     // Only 1 client has any credits
                                    ($countones(w_has_one_credit) == 1) &&     // Only 1 client has exactly 1 credit
 041082                             (w_has_any_credits == w_has_one_credit);   // Same client for both conditions
        
 673194     // Where w_requesting_clients_with_credits is computed as:
 019151     logic w_requesting_clients_with_credits;
 673194 
%000000     always_comb begin
%000000         w_requesting_clients_with_credits = 1'b0;
%000000         for (int i = 0; i < CLIENTS; i++) begin
%000000             if (w_req_post[i] && w_has_crd[i]) begin
%000000                 w_requesting_clients_with_credits = 1'b1;
                    end
                end
            end
        
            // replenish when no requesting clients have credits
            assign w_global_replenish = (w_normal_operation && !w_pending_grants &&
                                    (|w_req_post) && !w_requesting_clients_with_credits);
        
            // =======================================================================
 004468     // Request Masking (Proper Grant Logic with Fairness)
 004460     // =======================================================================
 000196 
 003572     logic [C-1:0]   w_mask_req;               // Filtered requests to sub-arbiter
 002898     logic [C-1:0]   w_mask_multi_req;
 000684     logic [C-1:0]   w_mask_last_client;
 007496     logic [C-1:0]   w_requesting_eligible;    // Clients eligible for grants
 003572     logic [C-1:0]   r_last_grant;             // Last grant from sub-arbiter
 026266 
            // masking to prevent consecutive grants
 007496     logic [C-1:0]   w_clients_with_credits_count;
 012260     logic           w_multiple_eligible;      // Multiple clients eligible (need fairness)
 1222466 
 1222466     // Count how many clients have credits AND are requesting
 549272     always_comb begin
 549272         w_clients_with_credits_count = '0;
 549272         for (int k = 0; k < CLIENTS; k++) begin
 1043487             if (w_requesting_eligible[k]) begin
 1043487                 w_clients_with_credits_count[k] = 1'b1;
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
 000278     // Sub-Arbiter Instance - instantiate the base round-robin arbiter
            // =======================================================================
        
 000112     logic w_sub_block_arb;  // Block signal for sub-arbiter
        
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
        
