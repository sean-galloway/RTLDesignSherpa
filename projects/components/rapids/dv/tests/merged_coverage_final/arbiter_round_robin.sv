//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: arbiter_round_robin
        // Purpose: //   Parameterizable round-robin arbiter with optional ACK protocol support.
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: arbiter_round_robin
        //==============================================================================
        // Description:
        //   Parameterizable round-robin arbiter with optional ACK protocol support.
        //   Ensures fairness by rotating priority among clients after each grant,
        //   preventing starvation while maintaining high throughput. Supports both
        //   immediate grants (no-ACK mode) and transaction-based grants (ACK mode).
        //
        // Features:
        //   - Configurable number of clients (2 to N)
        //   - Dual-priority scheme (masked and unmasked requests)
        //   - Two operation modes: No-ACK (fire-and-forget) and ACK (handshake)
        //   - Guaranteed fairness: each client served within CLIENTS cycles
        //   - One-hot grant vector with binary-encoded grant_id
        //   - Block arbitration support
        //   - Starvation prevention with bounded waiting time
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   CLIENTS:
        //     Description: Number of requesting clients
        //     Type: int
        //     Range: 2 to 1024 (practical limit)
        //     Default: 4
        //     Constraints: Must be ≥ 2 for meaningful arbitration
        //
        //   WAIT_GNT_ACK:
        //     Description: ACK protocol mode selection
        //     Type: int
        //     Range: 0 or 1
        //     Default: 0
        //     Values:
        //       0 = No-ACK mode (grants are immediate, no handshake)
        //       1 = ACK mode (grants require acknowledgment before next grant)
        //
        //   N:
        //     Description: Derived parameter for grant_id width
        //     Type: int
        //     Default: $clog2(CLIENTS)
        //     Constraints: Automatically calculated, do not override
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     clk:            Clock input (rising edge active)
        //     rst_n:          Asynchronous active-low reset
        //     block_arb:      Block arbitration (active-high, immediate effect)
        //     request[CLIENTS-1:0]:  Request vector (one bit per client)
        //     grant_ack[CLIENTS-1:0]: Grant acknowledgment vector (ACK mode only)
        //
        //   Outputs:
        //     grant_valid:    Grant outputs are valid (high when grant asserted)
        //     grant[CLIENTS-1:0]:  One-hot grant vector (exactly one bit set when valid)
        //     grant_id[N-1:0]:     Binary-encoded winner client ID
        //     last_grant[CLIENTS-1:0]: Previous cycle's grant (for debugging)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   No-ACK Mode:
        //     Latency: 1 cycle (grant issued immediately after arbitration)
        //     Throughput: Up to 100% (grant every cycle if requests present)
        //     Grant Duration: Exactly 1 cycle
        //
        //   ACK Mode:
        //     Latency: 1 cycle to issue grant + variable ACK delay
        //     Throughput: Limited by ACK latency
        //     Grant Duration: Held until ACK received
        //     Same-cycle ACK: Enables near-optimal throughput
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   NO-ACK MODE (WAIT_GNT_ACK = 0):
        //   -------------------------------
        //   1. Grant Generation:
        //      - Grant issued immediately when client wins arbitration
        //      - Grant valid for exactly one cycle (fire-and-forget)
        //      - No handshake required - grant implies acceptance
        //
        //   2. Priority Rotation:
        //      - Round-robin mask updates immediately when grant is issued
        //      - Next cycle, priority rotates to next client in sequence
        //      - Rotation order: 0 → 1 → 2 → ... → (CLIENTS-1) → 0
        //
        //   3. Arbitration Logic:
        //      a. First check masked requests (clients above last granted client)
        //      b. If no masked winners, check all requests (wrap-around)
        //      c. Winner selection uses priority encoder on processed requests
        //      d. Grant and grant_id output immediately when winner found
        //
        //   4. Timing:
        //      - Grant appears same cycle as arbitration decision
        //      - Continuous operation - can grant every cycle if requests present
        //
        //   ACK MODE (WAIT_GNT_ACK = 1):
        //   ----------------------------
        //   1. Grant Generation:
        //      - Grant issued when client wins AND no ACK pending
        //      - Grant remains asserted until corresponding ACK received
        //      - Only one grant can be pending at a time
        //
        //   2. ACK Protocol:
        //      - Testbench must assert grant_ack with matching grant vector
        //      - ACK can be asserted same cycle as grant (optimal)
        //      - ACK can be delayed multiple cycles after grant
        //      - ACK must be deasserted after one cycle (pulse protocol)
        //
        //   3. Priority Rotation:
        //      - Mask updates when ACK is received (not when grant issued)
        //      - Prevents priority advancement during pending transactions
        //
        //   4. Dead Cycle Handling:
        //      - Single request + ACK completion = mandatory dead cycle
        //      - Multiple requests + ACK completion = immediate next grant
        //      - Optimizes throughput while maintaining correctness
        //
        //   COMMON BEHAVIOR (BOTH MODES):
        //   -----------------------------
        //   - Block Arbitration: block_arb immediately stops all grant generation
        //   - Request Handling: Requests can assert/deassert at any time
        //   - Grant Properties: grant vector is always one-hot when valid
        //   - Reset: All state cleared, first arbitration gives client 0 priority
        //
        //   FAIRNESS GUARANTEE:
        //   - Each requesting client guaranteed service within CLIENTS cycles/transactions
        //   - No starvation possible if client continuously requests
        //   - Maximum wait: (CLIENTS - 1) grants for any continuously requesting client
        //
        //   Timing Diagram (No-ACK Mode, CLIENTS=4):
        //
        //   {signal: [
        //     {name: 'clk',         wave: 'p..........'},
        //     {name: 'rst_n',       wave: '01.........'},
        //     {name: 'request[3:0]', wave: 'x.3.4.5.6..', data: ['0001', '0011', '0111', '1111']},
        //     {},
        //     {name: 'grant[3:0]',  wave: 'x..2.4.8.2.', data: ['0001', '0010', '1000', '0001']},
        //     {name: 'grant_id',    wave: 'x..=.=.=.=.', data: ['0', '1', '3', '0']},
        //     {name: 'grant_valid', wave: '0..1.1.1.1.'},
        //     {},
        //     {name: 'Priority',    wave: 'x..2.4.6.2.', data: ['Cli 0', 'Cli 1', 'Cli 3', 'Cli 0 (wrap)']},
        //     {},
        //     {name: 'Note',        wave: 'x..2.......', data: ['Round-robin rotation']}
        //   ]}
        //
        //   Timing Diagram (ACK Mode, CLIENTS=4, Same-Cycle ACK):
        //
        //   {signal: [
        //     {name: 'clk',          wave: 'p..........'},
        //     {name: 'rst_n',        wave: '01.........'},
        //     {name: 'request[3:0]', wave: 'x.3.4.5....', data: ['0001', '0011', '0111']},
        //     {},
        //     {name: 'grant[3:0]',   wave: 'x..2.4.8...', data: ['0001', '0010', '1000']},
        //     {name: 'grant_valid',  wave: '0..1.1.1.0.'},
        //     {name: 'grant_ack[3:0]', wave: 'x..2.4.8...', data: ['0001', '0010', '1000']},
        //     {},
        //     {name: 'ACK Status',   wave: 'x..2.4.6.x.', data: ['ACK0', 'ACK1', 'ACK3']}
        //   ]}
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // No-ACK mode (simple arbitration)
        //   arbiter_round_robin #(
        //       .CLIENTS(4),
        //       .WAIT_GNT_ACK(0)
        //   ) u_arbiter_simple (
        //       .clk         (clk),
        //       .rst_n       (rst_n),
        //       .block_arb   (1'b0),
        //       .request     (req_vector),
        //       .grant_ack   (4'b0),              // Unused in No-ACK mode
        //       .grant_valid (grant_valid),
        //       .grant       (grant_vector),
        //       .grant_id    (winner_id),
        //       .last_grant  (prev_grant)
        //   );
        //
        //   // ACK mode (transaction-based arbitration)
        //   arbiter_round_robin #(
        //       .CLIENTS(8),
        //       .WAIT_GNT_ACK(1)
        //   ) u_arbiter_ack (
        //       .clk         (clk),
        //       .rst_n       (rst_n),
        //       .block_arb   (pause_arb),
        //       .request     (master_req),
        //       .grant_ack   (master_ack),        // Required in ACK mode
        //       .grant_valid (grant_valid),
        //       .grant       (grant_vector),
        //       .grant_id    (winner_id),
        //       .last_grant  (prev_grant)
        //   );
        //
        //   // Extract grant for specific client
        //   assign client_2_granted = grant[2] & grant_valid;
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **Use No-ACK mode when:** Grants are immediately serviced (e.g., mux selection)
        //   - **Use ACK mode when:** Grants initiate transactions requiring completion feedback
        //   - Grant vector is ALWAYS one-hot (exactly one bit set) when grant_valid=1
        //   - In ACK mode, testbench MUST provide timely ACK or arbiter will stall
        //   - block_arb has immediate effect - use for flow control or debugging
        //   - Priority encoder uses "find-first-set" - lower indices win ties
        //   - Mask algorithm: After client N wins, mask = ~((1 << N) - 1)
        //   - **Synthesis:** Infers efficient priority encoder and minimal state registers
        //   - **Area:** O(CLIENTS) for priority logic, O(log2(CLIENTS)) for state
        //   - **Timing:** Single-cycle grant path, critical path through priority encoder
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - arbiter_round_robin_simple.sv - Simplified version without ACK protocol
        //   - arbiter_round_robin_weighted.sv - Weighted round-robin for QoS
        //   - arbiter_priority_encoder.sv - Fixed priority arbiter (used internally)
        //   - counter_bin.sv - Alternative round-robin implementation using counters
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_arbiter_round_robin.py
        //   Run: pytest val/common/test_arbiter_round_robin.py -v
        //   Coverage: 95%
        //   Key Test Scenarios:
        //     - Round-robin fairness verification
        //     - ACK protocol timing (same-cycle, delayed)
        //     - Block arbitration behavior
        //     - Back-to-back transactions
        //     - Single client operation
        //     - Maximum client scaling (CLIENTS=16)
        //
        //------------------------------------------------------------------------------
        // References:
        //------------------------------------------------------------------------------
        //   - "Arbiters: Design Ideas and Coding Styles" - Matt Weber, SNUG 2001
        //   - "Synthesis and Scripting Techniques for Designing Multi-Asynchronous
        //     Clock Designs" - Cliff Cummings, SNUG 2001
        //   - Round-robin scheduling algorithms - Operating Systems literature
        //
        //------------------------------------------------------------------------------
        // Version History:
        //------------------------------------------------------------------------------
        //   2025-09-15: Optimized ACK mode with unified state management
        //   2025-09-01: Added ACK protocol support
        //   2025-08-15: Initial implementation
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        
        module arbiter_round_robin #(
            parameter int CLIENTS      = 4,
            parameter int WAIT_GNT_ACK = 0,
            parameter int N = $clog2(CLIENTS)
        ) (
 003696     input  logic                clk,
 000012     input  logic                rst_n,
%000000     input  logic                block_arb,
%000000     input  logic [CLIENTS-1:0]  request,
%000000     input  logic [CLIENTS-1:0]  grant_ack,
 000054     output logic                grant_valid,
%000000     output logic [CLIENTS-1:0]  grant,
%000000     output logic [N-1:0]        grant_id,
%000000     output logic [CLIENTS-1:0]  last_grant
        );
        
            // =======================================================================
            // Pre computed mask lookup table
            // =======================================================================
        
%000000     logic [CLIENTS-1:0] w_mask_decode [CLIENTS];
%000000     logic [CLIENTS-1:0] w_win_mask_decode [CLIENTS];
        
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
            // Streamlined state registers (pending ACK now unified with grant)
            // =======================================================================
        
%000000     logic [N-1:0]       r_last_grant_id;        // Track last winner (smaller than full mask)
 000054     logic               r_last_valid;         // Indiactor if the last winner should be used
 000054     logic               r_pending_ack;        // ACK mode state (managed with grant)
%000000     logic [N-1:0]       r_pending_client;     // Which client has pending ACK (managed with grant)
        
            // =======================================================================
            // Fast request preprocessing
            // =======================================================================
        
%000000     logic [CLIENTS-1:0] w_requests_gated;
%000000     logic [CLIENTS-1:0] w_requests_masked;
%000000     logic [CLIENTS-1:0] w_requests_unmasked;
 000036     logic               w_any_requests;
 000032     logic               w_any_masked_requests;
 000018     logic [CLIENTS-1:0] w_curr_mask_decode;
        
            // Single LUT level for request gating
            assign w_requests_gated = block_arb ? '0 : request;
            assign w_any_requests = |w_requests_gated;
        
            // Fast mask application using LUT
            assign w_curr_mask_decode = grant_valid ? w_win_mask_decode[grant_id] :
                                        r_last_valid ? w_win_mask_decode[r_last_grant_id] : CLIENTS'(1);
            assign w_requests_masked = (w_requests_gated & w_curr_mask_decode);
            assign w_requests_unmasked = w_requests_gated;
            assign w_any_masked_requests = |w_requests_masked;
        
            // =======================================================================
            // Single stage priority encoder
            // =======================================================================
        
%000000     logic [N-1:0] w_winner;
 000036     logic         w_winner_valid;
        
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
            // ACK detection (simplified - no separate state management)
            // =======================================================================
 000054     logic w_ack_received;
 000012     logic w_can_grant;
%000000     logic [CLIENTS-1:0] w_other_requests;  // Requests excluding ACK'd client
        
            generate
                if (WAIT_GNT_ACK == 1) begin : gen_ack_optimized
        
                    // Fast ACK detection (single LUT)
                    assign w_ack_received = r_pending_ack && grant_ack[r_pending_client];
        
                    // Calculate other requests (excluding ACK'd client)
                    assign w_other_requests = w_requests_gated & ~(CLIENTS'(1) << r_pending_client);
        
                    // Grant permission logic - allow arbitration when no ACK pending or during ACK cycle
                    assign w_can_grant = !r_pending_ack || w_ack_received;
        
                end else begin : gen_no_ack_optimized
                    assign w_ack_received = 1'b0;
                    assign w_can_grant = 1'b1;
                    assign w_other_requests = '0;
                end
            endgenerate
        
            // =======================================================================
            // Output generation with atomic updates
            // =======================================================================
 000036     logic w_should_grant;
%000000     logic [CLIENTS-1:0] w_next_grant;
%000000     logic [N-1:0] w_next_grant_id;
 000036     logic w_next_grant_valid;
        
            // Grant decision logic (minimal depth)
            assign w_should_grant = w_winner_valid && w_any_requests && w_can_grant;
        
            // Grant vector generation with atomic assignment
 011253     always_comb begin
 011253         w_next_grant = '0;
 011253         w_next_grant_id = '0;  // Always initialize to prevent X propagation
        
 000324         if (w_should_grant) begin
 000324             w_next_grant[w_winner] = 1'b1;
 000324             w_next_grant_id = w_winner;  // Atomic: Both grant and grant_id from same source
                end
                // If not granting, both remain 0 (no partial updates)
            end
        
            assign w_next_grant_valid = w_should_grant;
        
            // =======================================================================
            // Grant outputs and pending ACK state in single always_ff
            // =======================================================================
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    grant            <= '0;
                    grant_id         <= '0;
                    grant_valid      <= 1'b0;
                    last_grant       <= '0;
                    r_last_grant_id  <= '0;
                    r_last_valid     <= '0;
                    r_pending_ack    <= 1'b0;
                    r_pending_client <= '0;
                end else begin
                    r_last_valid <= grant_valid;
        
                    if (WAIT_GNT_ACK == 0) begin
                        // No-ACK mode: direct atomic assignment
                        grant           <= w_next_grant;
                        grant_id        <= w_next_grant_id;
                        grant_valid     <= w_next_grant_valid;
                        last_grant      <= grant;
                        r_last_grant_id <= grant_id;
        
                    end else begin
                        // ACK mode: follow the four rules AND manage pending ACK state unified
                        if (grant_valid == 1'b0) begin
                            // Rule 1: grant_valid = 0 → allow new values
                            grant           <= w_next_grant;
                            grant_id        <= w_next_grant_id;
                            grant_valid     <= w_next_grant_valid;
                            last_grant      <= grant;
                            r_last_grant_id <= grant_id;
        
                            // UNIFIED: Update pending ACK state when issuing new grant
                            if (w_next_grant_valid) begin
                                r_pending_ack    <= 1'b1;
                                r_pending_client <= w_next_grant_id;
                            end
        
                        end else if (grant_valid == 1'b1 && !w_ack_received) begin
                            // Rule 2: grant_valid = 1 and no ack → hold all values
                            // grant, grant_id, grant_valid unchanged
                            // r_pending_ack, r_pending_client unchanged
        
                        end else if (grant_valid == 1'b1 && w_ack_received && (w_other_requests == '0)) begin
                            // Rule 3: grant_valid = 1, ack occurs, only pending client requesting → clear all
                            grant            <= '0;
                            grant_id         <= '0;
                            grant_valid      <= 1'b0;
                            last_grant       <= grant;
                            r_last_grant_id  <= grant_id;
                            r_pending_ack    <= 1'b0;
                            r_pending_client <= '0;
        
                        end else if (grant_valid == 1'b1 && w_ack_received && (w_other_requests != '0)) begin
                            // Rule 4: grant_valid = 1, ack occurs, other requests → take new values or clear if none
                            if (w_next_grant_valid) begin
                                grant            <= w_next_grant;
                                grant_id         <= w_next_grant_id;
                                grant_valid      <= w_next_grant_valid;
                                last_grant       <= grant;
                                r_last_grant_id  <= grant_id;
                                r_pending_ack    <= 1'b1;
                                r_pending_client <= w_next_grant_id;
                            end else begin
                                grant            <= '0;
                                grant_id         <= '0;
                                grant_valid      <= 1'b0;
                                r_pending_ack    <= 1'b0;
                                r_pending_client <= '0;
                            end
                        end
                    end
                end
%000000     )
        
        
        endmodule : arbiter_round_robin
        
