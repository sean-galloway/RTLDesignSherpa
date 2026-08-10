// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_deficit_round_robin
// Purpose: Deficit round-robin arbiter: cost-proportional bandwidth shares
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-08-09

`timescale 1ns / 1ps

//==============================================================================
// Module: arbiter_deficit_round_robin
//==============================================================================
// Description:
//   Deficit round-robin (DRR) arbiter. The sibling wrapper to
//   arbiter_round_robin_weighted around the same arbiter_round_robin core:
//   where the WRR spends ONE credit per grant (shares proportional to grant
//   COUNT), the DRR spends the request's COST per grant and carries the
//   remainder as deficit (shares proportional to COST SERVED - bytes, beats,
//   bus cycles). Use the WRR when requests are equal-sized; use this when a
//   grant's resource usage varies per request (packet lengths, burst sizes).
//
// Features:
//   - Deficit-based arbitration: grant only when deficit covers the cost
//   - Per-client runtime quantum (bandwidth share), atomic update FSM
//   - Global quantum replenish when no requesting client can afford its cost
//   - Anti-hoarding: a client's deficit clears when its request deasserts
//   - Fair round-robin among simultaneously-affordable clients
//   - Optional ACK protocol (WAIT_GNT_ACK=0/1), same contract as the family
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   CLIENTS:
//     Description: Number of requesting clients
//     Type: int
//     Range: 2 to 32
//     Default: 4
//
//   MAX_QUANTUM:
//     Description: Maximum quantum value per client (exclusive power bound)
//     Type: int
//     Range: 2 to 256
//     Default: 16
//     Constraints: Quantum field width = $clog2(MAX_QUANTUM). Larger quantum
//                  relative to costs = coarser rounds, fewer replenishes.
//
//   COST_WIDTH:
//     Description: Width of each client's request-cost input
//     Type: int
//     Range: 1 to 16
//     Default: 4
//     Constraints: Costs are 1..2**COST_WIDTH-1. A cost of 0 is defensively
//                  treated as 1 (see Notes).
//
//   WAIT_GNT_ACK:
//     Description: Enable ACK protocol for grant completion
//     Type: int
//     Range: 0 or 1
//     Default: 0
//
//   Derived Parameters (localparam - computed automatically):
//     QW:    Quantum field width ($clog2(MAX_QUANTUM))
//     DW:    Deficit counter width - sized so a deficit can always reach the
//            largest legal cost: $clog2(2**COST_WIDTH + MAX_QUANTUM) + 1.
//            This is what makes livelock impossible (see Behavior).
//     N:     Client ID width ($clog2(CLIENTS))
//     C:     Convenience alias for CLIENTS
//     CXQW:  Packed quantum array width (CLIENTS * QW)
//     CXCW:  Packed cost array width (CLIENTS * COST_WIDTH)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:                  Clock input
//     rst_n:                Asynchronous active-low reset
//     block_arb:            Block all arbitration (external gate)
//     quantum[CXQW-1:0]:    Packed per-client quantum values
//                            Format: {quantum[C-1], ..., quantum[1], quantum[0]}
//     req_cost[CXCW-1:0]:   Packed per-client cost of the HEAD request.
//                            Contract: stable while request[i] is held, like
//                            payload under a valid ([[valid-ready-contracts]]).
//     request[C-1:0]:       Request vector
//     grant_ack[C-1:0]:     Grant acknowledgment (ACK mode only)
//
//   Outputs:
//     grant_valid:          Grant output valid
//     grant[C-1:0]:         Grant vector (one-hot)
//     grant_id[N-1:0]:      Grant client ID (binary encoded)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle steady-state, same as the WRR: deficit compare,
//                   eligibility masking and the RR decision are combinational;
//                   the register stage is the base arbiter's grant.
//   Throughput:     1 grant per cycle (max)
//   Grant Hold:     No-ACK: 1 cycle, ACK: until grant_ack asserted
//   Replenish:      1 cycle per round; repeats until some requester can
//                   afford its cost (multi-round accumulation for costs
//                   larger than one quantum)
//   Quantum Update: 3-15 cycles (FSM: BLOCK -> DRAIN -> UPDATE -> STABILIZE)
//   Reset:          Asynchronous (deficits -> 0, quanta -> 1)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   The DRR discipline:
//   - Each client holds a DEFICIT counter, reset to 0.
//   - A requesting client is ELIGIBLE when its deficit >= its head cost.
//   - When at least one client requests but NONE is eligible, a replenish
//     round fires: every requesting client's deficit gains its quantum.
//     Costs above one quantum simply take several rounds to save up for -
//     the deficit counter is sized to always reach the largest legal cost,
//     so accumulation terminates and livelock cannot occur.
//   - On grant completion the winner's deficit is debited by that request's
//     cost; the REMAINDER carries to its next request. The carry is what
//     makes long-run shares proportional to quantum regardless of how
//     request costs divide into it.
//   - When a client's request deasserts, its deficit clears to zero
//     (classic DRR empty-queue rule). A client cannot bank service while
//     idle and burst later - shares are earned while competing. Consumers
//     with back-to-back frames should hold request through the gap if they
//     want the carry preserved.
//
//   Relation to the WRR sibling:
//   - WRR: weight w  => w GRANTS per round, whatever each grant costs.
//   - DRR: quantum q => q COST-UNITS per round, however many grants that is.
//   - With all costs == 1 and quantum == weight the two disciplines give the
//     same long-run shares (the WRR is the cheaper choice there).
//
//   Arbitration Stages (mirrors the WRR):
//   1. **Affordability:** eligible = requesting && quantum > 0 && deficit >= cost
//   2. **Round-Robin Selection:** base arbiter picks among eligible clients
//   3. **Grant Output:** winning client granted (one-hot)
//   4. **Deficit Update:** winner debited by cost on completion; replenish
//      rounds add quantum to all requesters when nobody can afford service
//
//   Share Example (quanta [4,2,1,1], every request cost 2):
//   - Replenish rounds accumulate: C0 +4/round, C1 +2/round, C2,C3 +1/round
//   - Round 1: C0 affords (4>=2) and is debited to 2, affords again -> 0;
//     C1 affords once -> 0; C2,C3 must wait a second round to reach 2.
//   - Long-run cost-units served: 4:2:1:1 - the quantum ratio, even though
//     C2 and C3 only get a grant every OTHER round.
//
//   Quantum change safety: identical shadow-register FSM to the WRR
//   (IDLE -> BLOCK -> DRAIN -> UPDATE -> STABILIZE, 15-cycle timeout);
//   deficits clear to zero at STABILIZE so old carry cannot distort the new
//   policy's first round.
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // 4 clients arbitrating a shared write port; requests are bursts of
//   // 1..15 beats and shares should be proportional to BEATS, not grants.
//   localparam int NC = 4;
//   localparam int QW = $clog2(16);
//
//   logic [NC-1:0]      req, gnt, ack;
//   logic [NC*4-1:0]    burst_len;    // head-of-queue burst length per client
//   logic [NC*QW-1:0]   quanta;
//
//   assign quanta = {QW'(1), QW'(1), QW'(2), QW'(4)};  // {C3,C2,C1,C0}
//
//   arbiter_deficit_round_robin #(
//       .CLIENTS      (NC),
//       .MAX_QUANTUM  (16),
//       .COST_WIDTH   (4),
//       .WAIT_GNT_ACK (0)
//   ) u_drr (
//       .clk        (clk),
//       .rst_n      (rst_n),
//       .block_arb  (1'b0),
//       .quantum    (quanta),
//       .req_cost   (burst_len),
//       .request    (req),
//       .grant_ack  ('0),
//       .grant_valid(gnt_valid),
//       .grant      (gnt),
//       .grant_id   (gnt_id)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Quantum = 0:** client disabled (never granted), same as WRR weight 0
//   - **Cost = 0:** defensively served as cost 1. Drive real costs >= 1;
//     a zero-cost grant would spend nothing and starve the other clients.
//   - **Cost stability:** req_cost[i] must hold while request[i] is asserted
//     (it is the "payload" of the request). A consumer may present the NEXT
//     frame's cost as soon as it observes the grant for the current one -
//     the internal cost pipeline debits the arbitration-cycle cost, so the
//     back-to-back frame handoff is safe by construction.
//   - Deficit counters clear on request deassert - see Behavior for why
//   - **DO NOT** change quanta every cycle (same thrashing caveat as WRR)
//   - Base arbiter: arbiter_round_robin (rotating-mask RR + ACK protocol)
//   - **Critical path:** deficit >= cost compare -> request filtering ->
//     base arbiter. One comparator wider than the WRR's credit != 0 check;
//     at high CLIENTS consider registering eligibility (adds a cycle).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - arbiter_round_robin.sv - Base round-robin arbiter (used internally)
//   - arbiter_round_robin_weighted.sv - Sibling: grant-count shares (credits)
//   - arbiter_round_robin_simple.sv - Lightweight RR arbiter
//   - arbiter_priority_encoder.sv - Fixed priority core
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_arbiter_deficit_round_robin.py
//   Run: pytest val/common/test_arbiter_deficit_round_robin.py -v
//   Key Test Scenarios:
//     - Cost-proportional share verification (mixed costs, quanta ratios)
//     - Multi-round accumulation (cost > quantum)
//     - Deficit carry across requests (request held)
//     - Anti-hoarding (deficit clears on request drop)
//     - Dynamic quantum change (atomic update)
//     - ACK mode operation
//     - Zero quantum (client disable) and cost-0 defense
//
//==============================================================================

`include "reset_defs.svh"

module arbiter_deficit_round_robin #(
    parameter int CLIENTS      = 4,
    parameter int MAX_QUANTUM  = 16,
    parameter int COST_WIDTH   = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Derived - do not override (declared here so the port list can use
    // them; strict front ends reject body localparams in port ranges)
    parameter int QW   = $clog2(MAX_QUANTUM),
    parameter int N    = $clog2(CLIENTS),
    parameter int C    = CLIENTS,
    parameter int CXQW = CLIENTS * QW,
    parameter int CXCW = CLIENTS * COST_WIDTH
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              block_arb,
    input  logic [CXQW-1:0]   quantum,
    input  logic [CXCW-1:0]   req_cost,

    input  logic [C-1:0]      request,
    input  logic [C-1:0]      grant_ack,

    output logic              grant_valid,
    output logic [C-1:0]      grant,
    output logic [N-1:0]      grant_id
);

    // =======================================================================
    // Derived Parameters (QW/N/C/CXQW/CXCW live in the parameter list -
    // the port declarations need them)
    // =======================================================================
    // Deficit width: must be able to hold (max cost - 1) + one more quantum,
    // i.e. the largest value accumulation can reach the cycle a client
    // becomes eligible. Sizing it this way is the no-livelock guarantee:
    // every legal cost is reachable, so replenish rounds always terminate.
    localparam int DW   = $clog2((2 ** COST_WIDTH) + MAX_QUANTUM) + 1;

    // =======================================================================
    // Local Parameters (same constants as the WRR sibling)
    // =======================================================================
    localparam int QUANTUM_STABILIZE_CYCLES = 3;
    localparam int QUANTUM_DRAIN_CYCLES     = 2;
    localparam int QUANTUM_TIMEOUT_CYCLES   = 15;

    // =======================================================================
    // Quantum Management FSM (mirrors the WRR weight FSM)
    // =======================================================================

    typedef enum logic [4:0] {
        QUANT_IDLE      = 5'b00001,  // Normal operation
        QUANT_BLOCK     = 5'b00010,  // Block new grants
        QUANT_DRAIN     = 5'b00100,  // Wait for pending grants to complete
        QUANT_UPDATE    = 5'b01000,  // Atomic quantum update
        QUANT_STABILIZE = 5'b10000   // Allow system to stabilize
    } quantum_fsm_t;

    quantum_fsm_t r_quant_state;
    logic [3:0]   r_quant_timer;

    logic [CXQW-1:0] r_safe_quantum;       // Active quanta (shadow register)
    logic            w_quantum_change_req;
    logic            w_pending_grants;

    assign w_quantum_change_req = (quantum != r_safe_quantum);

    assign w_pending_grants = (WAIT_GNT_ACK == 1) ?
                              (grant_valid && (grant_ack & grant) == '0) : 1'b0;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_quant_state  <= QUANT_IDLE;
            r_safe_quantum <= {CXQW{1'b1}};  // Default quantum=1 for all clients
            r_quant_timer  <= 4'h0;
        end else begin
            casez (r_quant_state)
                QUANT_IDLE: begin
                    if (w_quantum_change_req) begin
                        r_quant_state <= QUANT_BLOCK;
                        r_quant_timer <= 4'h0;
                    end
                end

                QUANT_BLOCK: begin
                    if (!w_pending_grants) begin
                        r_quant_state <= QUANT_DRAIN;
                        r_quant_timer <= QUANTUM_DRAIN_CYCLES[3:0];
                    end else if (r_quant_timer < QUANTUM_TIMEOUT_CYCLES[3:0]) begin
                        r_quant_timer <= r_quant_timer + 4'h1;
                    end else begin
                        r_quant_state <= QUANT_DRAIN;
                        r_quant_timer <= 4'h0;
                    end
                end

                QUANT_DRAIN: begin
                    if (r_quant_timer == 4'h0) begin
                        r_quant_state <= QUANT_UPDATE;
                    end else begin
                        r_quant_timer <= r_quant_timer - 4'h1;
                    end
                end

                QUANT_UPDATE: begin
                    r_safe_quantum <= quantum;
                    r_quant_state  <= QUANT_STABILIZE;
                    r_quant_timer  <= QUANTUM_STABILIZE_CYCLES[3:0];
                end

                QUANT_STABILIZE: begin
                    if (r_quant_timer == 4'h0) begin
                        r_quant_state <= QUANT_IDLE;
                    end else begin
                        r_quant_timer <= r_quant_timer - 4'h1;
                    end
                end

                // verilator coverage_off
                // DEFENSIVE: Illegal FSM state recovery
                default: begin
                    r_quant_state <= QUANT_IDLE;
                    r_quant_timer <= 4'h0;
                end
                // verilator coverage_on
            endcase
        end
    )


    // =======================================================================
    // Pre-computed Helper Signals
    // =======================================================================

    logic [QW-1:0]         w_client_quantum [C];   // Per-client quanta
    logic [COST_WIDTH-1:0] w_cost_raw     [C];   // Per-client raw cost
    logic [DW-1:0]         w_cost         [C];   // Cost widened, 0 mapped to 1
    logic                  w_normal_operation;
    logic [C-1:0]          w_valid_clients;      // Non-zero quantum
    logic [C-1:0]          w_req_post;           // Post-block requests

    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_quanta
            assign w_client_quantum[j] = r_safe_quantum[(j+1)*QW-1 -: QW];
            assign w_valid_clients[j] = (w_client_quantum[j] > 0);
            assign w_cost_raw[j] = req_cost[(j+1)*COST_WIDTH-1 -: COST_WIDTH];
            // Defensive: a zero cost is served as cost 1, so it still spends
            // deficit and cannot starve the other clients.
            assign w_cost[j] = (w_cost_raw[j] == '0) ? DW'(1) : DW'(w_cost_raw[j]);
        end
    endgenerate

    assign w_normal_operation = (r_quant_state == QUANT_IDLE);
    assign w_req_post = block_arb ? '0 : request;

    // =======================================================================
    // Deficit Management System
    // =======================================================================

    logic [DW-1:0] r_deficit [C];          // Deficit counters
    logic [DW-1:0] w_deficit [C];          // Next deficit values
    logic [C-1:0]  w_affords;              // deficit >= cost (affordability)
    logic [C-1:0]  w_grant_completed;      // Grant completion per client
    logic          w_global_replenish;

    // Grant completion, same contract as the WRR
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_grant_completion
            assign w_grant_completed[i] = (WAIT_GNT_ACK == 0) ?
                                         (grant[i] && grant_valid) :
                                         (grant[i] && grant_valid && grant_ack[i]);
        end
    endgenerate

    // Cost pipeline: the grant registers ONE CYCLE after the arbitration that
    // won it, but a consumer pops its frame on grant and presents the next
    // frame's cost immediately - so in the completion cycle req_cost may
    // already be the NEXT frame's. Debit with the cost that was current in
    // the ARBITRATION cycle, not the completion cycle, or a back-to-back
    // client is debited the wrong frame's cost. (Found by the TB's deficit
    // mirror: granted under cost 2, debited the successor frame's cost 11.)
    logic [DW-1:0] r_cost_arb [C];

    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_cost_pipeline
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_cost_arb[i] <= DW'(1);
                end else begin
                    r_cost_arb[i] <= w_cost[i];
                end
            )
        end
    endgenerate

    // Next-deficit combinational logic. Order of precedence per client:
    // request gone -> clear (anti-hoarding); completion -> debit cost;
    // replenish round -> add quantum. Debit and replenish cannot coincide
    // (replenish requires no eligible client; a granted client was eligible).
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_deficit_combo
            always_comb begin
                w_deficit[i] = r_deficit[i];

                case (r_quant_state)
                    QUANT_IDLE: begin
                        if (!w_req_post[i]) begin
                            // Classic DRR empty-queue rule: no banking
                            // service while idle
                            w_deficit[i] = '0;
                        end else if (w_grant_completed[i]) begin
                            // Debit the ARBITRATION-cycle cost (see the cost
                            // pipeline above); floor at 0 defensively
                            w_deficit[i] = (r_deficit[i] >= r_cost_arb[i]) ?
                                           (r_deficit[i] - r_cost_arb[i]) : '0;
                        end else if (w_global_replenish && w_valid_clients[i]) begin
                            // One DRR round-visit: add this client's quantum
                            w_deficit[i] = r_deficit[i] + DW'(w_client_quantum[i]);
                        end
                    end

                    QUANT_STABILIZE: begin
                        // New policy starts from a clean slate - old carry
                        // must not distort the new quanta's first round
                        w_deficit[i] = '0;
                    end

                    default: begin
                        w_deficit[i] = r_deficit[i];
                    end
                endcase
            end
        end
    endgenerate

    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_deficit_registers
            assign w_affords[i] = (r_deficit[i] >= w_cost[i]);

            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_deficit[i] <= '0;
                end else begin
                    r_deficit[i] <= w_deficit[i];
                end
            )
        end
    endgenerate

    // A requesting, enabled client that can afford its cost right now
    logic w_any_affordable_requester;

    always_comb begin
        w_any_affordable_requester = 1'b0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (w_req_post[i] && w_valid_clients[i] && w_affords[i] &&
                w_normal_operation) begin
                w_any_affordable_requester = 1'b1;
            end
        end
    end

    // Replenish round: requests exist but nobody can afford service. Repeats
    // on consecutive cycles until some deficit reaches its cost - that IS the
    // multi-round accumulation of classic DRR, and the DW sizing guarantees
    // it terminates.
    assign w_global_replenish = (w_normal_operation && !w_pending_grants &&
                                 (|w_req_post) && !w_any_affordable_requester);

    // =======================================================================
    // Request Masking (same fairness structure as the WRR sibling)
    // =======================================================================

    logic [C-1:0] w_mask_req;              // Filtered requests to sub-arbiter
    logic [C-1:0] w_mask_multi_req;
    logic [C-1:0] w_mask_last_client;
    logic [C-1:0] w_requesting_eligible;   // Clients eligible for grants
    logic [C-1:0] r_last_grant;            // Last grant from sub-arbiter
    logic         w_multiple_eligible;

    assign w_multiple_eligible = ($countones(w_requesting_eligible) > 1);

    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_request_logic
            // Eligible: requesting, enabled, normal operation, and can afford
            // its cost from the registered deficit. (Unlike the WRR there is
            // no same-cycle replenish grant - a replenish round is a 1-cycle
            // bubble; the deficit compare would otherwise need an adder in
            // the eligibility cone. See Notes/Critical path.)
            assign w_requesting_eligible[j] = w_req_post[j] &&
                                              w_valid_clients[j] &&
                                              w_normal_operation &&
                                              w_affords[j];

            // 1. Multiple eligible: exclude the current grant holder so the
            //    RR pointer interleaves (grants do not burst per client).
            // 2. Single eligible: keep its request through back-to-back
            //    grants while it can afford ANOTHER service after this one -
            //    the WRR's credit>1 term, translated to deficit >= 2*cost.
            //    (After grant deassertion the multi term re-forwards it, so
            //    the last affordable grant is a 1-cycle bubble, not a loss -
            //    same shape as the WRR.)
            assign w_mask_multi_req[j] = w_requesting_eligible[j] && !grant[j];
            assign w_mask_last_client[j] = !w_multiple_eligible &&
                                           w_requesting_eligible[j] &&
                                           (r_deficit[j] >= (DW'(2) * w_cost[j]));
            assign w_mask_req[j] = w_mask_multi_req[j] || w_mask_last_client[j];
        end
    endgenerate

    // =======================================================================
    // Sub-Arbiter Instance - the shared base round-robin core
    // =======================================================================

    logic w_sub_block_arb;

    assign w_sub_block_arb = (r_quant_state != QUANT_IDLE);

    arbiter_round_robin #(
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (WAIT_GNT_ACK)
    ) u_base_arbiter (
        .clk          (clk),
        .rst_n        (rst_n),
        .block_arb    (w_sub_block_arb),
        .request      (w_mask_req),
        .grant_ack    (grant_ack),
        .grant_valid  (grant_valid),
        .grant        (grant),
        .grant_id     (grant_id),
        .last_grant   (r_last_grant)
    );

endmodule : arbiter_deficit_round_robin
