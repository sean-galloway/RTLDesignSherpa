// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_token_bucket
// Purpose: Free-standing per-client token-bucket request shaper
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-08-10

`timescale 1ns / 1ps

//==============================================================================
// Module: arbiter_token_bucket
//==============================================================================
// Description:
//   Per-client token-bucket request shaper. Sits IN FRONT of any arbiter in
//   the family (round-robin, weighted, deficit) and gates each client's
//   request by its token balance: tokens accumulate at a configured rate on
//   an external refill tick (up to a burst cap) and one token is spent per
//   completed grant. A client out of tokens simply stops requesting until
//   the next refill.
//
//   This is RATE shaping, not fairness. The arbiter behind it still decides
//   who wins among the requests that pass; the shaper decides how OFTEN each
//   client may compete. The two compose freely: token_bucket + RR gives
//   rate-limited fair sharing, token_bucket + WRR/DRR gives shaped rate AND
//   weighted share together - which is why this is a free-standing block
//   rather than a mode of any one arbiter.
//
// Features:
//   - Per-client runtime rate (tokens per refill tick) and burst cap
//   - External refill tick: pair with counter_freq_invariant's 1 us tick
//     (or any pulse) so rates carry real-time meaning across clock speeds
//   - Fail-open: a client with cap 0 is UNSHAPED (request passes through)
//   - Overspend-proof gating: the pass gate accounts for a spend completing
//     in the same cycle, so a client can never be granted more times than
//     it holds tokens (see Notes - this is the registered-decision lesson)
//   - Same completion contract as the arbiter family (WAIT_GNT_ACK=0/1)
//   - No config-update FSM needed: unlike WRR/DRR there is no cross-client
//     invariant to protect - a rate/cap change affects only that client's
//     bucket, and the cap clamp applies IMMEDIATELY (cap is an invariant
//     of the bucket, not a refill-time bound - a lowered cap must not
//     leave banked burst above the new contract)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   CLIENTS:
//     Description: Number of clients being shaped
//     Type: int
//     Range: 2 to 32
//     Default: 4
//
//   MAX_TOKENS:
//     Description: Exclusive bound on bucket contents and caps
//     Type: int
//     Range: 2 to 65536
//     Default: 64
//     Constraints: Token counter and cap field width = $clog2(MAX_TOKENS)
//
//   RATE_WIDTH:
//     Description: Width of each client's tokens-per-tick rate field
//     Type: int
//     Range: 1 to 16
//     Default: 4
//
//   WAIT_GNT_ACK:
//     Description: Completion contract of the DOWNSTREAM arbiter
//     Type: int
//     Range: 0 or 1
//     Default: 0
//     Constraints: Must match the arbiter this shaper feeds - it decides
//                  when a grant SPENDS (immediately vs on grant_ack)
//
//   Derived Parameters (localparam except port-list users):
//     TW:    Token/cap field width ($clog2(MAX_TOKENS))
//     C:     Alias for CLIENTS
//     CXTW:  Packed cap array width (CLIENTS * TW)
//     CXRW:  Packed rate array width (CLIENTS * RATE_WIDTH)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:                  Clock input
//     rst_n:                Asynchronous active-low reset
//     refill_tick:          One-cycle pulse: add rate[i] tokens to every
//                            bucket (saturating at cap[i]). Pace this with
//                            counter_freq_invariant for real-time rates.
//     rate[CXRW-1:0]:       Packed per-client tokens added per tick
//     bucket_cap[CXTW-1:0]: Packed per-client burst caps. CAP 0 = UNSHAPED
//                            (fail-open bypass for that client).
//     request_in[C-1:0]:    Raw client requests
//     grant[C-1:0]:         Downstream arbiter's grant vector (one-hot)
//     grant_valid:          Downstream arbiter's grant valid
//     grant_ack[C-1:0]:     Grant acknowledge (ACK mode only)
//
//   Outputs:
//     request_out[C-1:0]:   Shaped requests - feed the arbiter's request
//     tokens[CXTW-1:0]:     Packed current bucket levels (observability)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Each client i keeps a token counter (reset 0):
//   - refill_tick: tokens[i] <- min(tokens[i] + rate[i], cap[i])
//   - completed grant to i: tokens[i] <- tokens[i] - 1
//   - both in one cycle: tokens[i] <- min(tokens[i]+rate[i], cap[i]) - 1
//   - request_out[i] = request_in[i] when the client is unshaped (cap 0)
//     or its balance NET OF any spend completing this cycle is >= 1
//
//   Burst semantics: a bucket at cap C allows C back-to-back grants before
//   the client throttles to its refill rate - that is the burst allowance a
//   token bucket exists to provide. Long-run rate <= rate[i] per tick
//   interval, exactly.
//
//   Reset starts every bucket EMPTY: no client may compete until its first
//   refill tick. Empty-start is the conservative choice for a rate limiter
//   (a full-start bucket would let every client burst immediately after
//   reset, before the configured rates have ever applied).
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Rate-limit 4 masters in front of the weighted arbiter: client 0 may
//   // burst 8 then sustain 2 grants/us; the rest 1/us. Client 3 unshaped.
//   logic us_tick;
//   counter_freq_invariant #(.COUNTER_WIDTH(16)) u_tick (
//       .clk(clk), .rst_n(rst_n), .sync_reset_n(1'b1),
//       .freq_sel(freq_sel), .o_counter(), .tick(us_tick)
//   );
//
//   logic [3:0] shaped_req;
//   arbiter_token_bucket #(
//       .CLIENTS(4), .MAX_TOKENS(16), .RATE_WIDTH(2), .WAIT_GNT_ACK(0)
//   ) u_shaper (
//       .clk(clk), .rst_n(rst_n),
//       .refill_tick(us_tick),
//       .rate       ({2'd1, 2'd1, 2'd1, 2'd2}),   // {C3,C2,C1,C0}
//       .bucket_cap ({4'd0, 4'd2, 4'd2, 4'd8}),   // C3 cap 0 = unshaped
//       .request_in (m_req),
//       .grant      (gnt),
//       .grant_valid(gnt_valid),
//       .grant_ack  ('0),
//       .request_out(shaped_req),
//       .tokens     ()
//   );
//
//   arbiter_round_robin_weighted #(.CLIENTS(4)) u_arb (
//       // ... .request(shaped_req), .grant(gnt), .grant_valid(gnt_valid) ...
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **cap = 0 means UNSHAPED, not blocked** (fail-open). A shaper should
//     degrade to "no shaping", not to "no service" - a zeroed config must
//     not silently starve a client. To block a client outright, gate its
//     request upstream or give the downstream WRR/DRR a zero weight/quantum.
//   - **rate = 0 with cap > 0** never refills: the client spends whatever
//     it holds and then throttles to nothing. That IS a deliberate block.
//   - **Why the gate uses the net-of-spend balance:** the downstream grant
//     registers one cycle after the arbitration that saw request_out, so in
//     the completion cycle the bucket register still shows the pre-spend
//     value. Gating on the raw register would forward the request during
//     that cycle and let a 1-token client win twice on one token (the same
//     registered-decision window the DRR's r_cost_arb pipeline handles -
//     see [[valid-ready-contracts]]). Subtracting the in-flight spend
//     closes it: request_out drops the moment the last token is committed.
//   - Spend is 1 token per completed grant. A cost-proportional variant
//     (spend = req_cost, pairing with the DRR) is future work - open a task
//     with the consumer that needs it.
//   - The tokens output is observability for TBs/CSRs, not a contract.
//   - Refill and spend in the same cycle compose (refill-then-spend), so a
//     rate-1 client under saturation sustains exactly one grant per tick.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - arbiter_round_robin.sv / _weighted.sv / arbiter_deficit_round_robin.sv -
//     the arbiters this shaper composes with (it is welded to none of them)
//   - counter_freq_invariant.sv - the natural refill_tick source
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_arbiter_token_bucket.py
//   Run: pytest val/common/test_arbiter_token_bucket.py -v
//   Key Test Scenarios:
//     - Sustained rate exactly rate[i] per tick under saturation
//     - Burst allowance up to cap after an idle accumulation period
//     - Never overspent: cumulative grants <= cumulative refill + cap
//     - cap=0 bypass (unshaped client unaffected by ticks)
//     - rate=0 drain-to-block
//     - ACK mode spend timing
//     - Runtime rate/cap changes (no FSM - clamp on next refill)
//
//==============================================================================

`include "reset_defs.svh"

module arbiter_token_bucket #(
    parameter int CLIENTS      = 4,
    parameter int MAX_TOKENS   = 64,
    parameter int RATE_WIDTH   = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Derived - do not override (declared here so the port list can use
    // them; strict front ends reject body localparams in port ranges)
    parameter int TW   = $clog2(MAX_TOKENS),
    parameter int C    = CLIENTS,
    parameter int CXTW = CLIENTS * TW,
    parameter int CXRW = CLIENTS * RATE_WIDTH
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              refill_tick,
    input  logic [CXRW-1:0]   rate,
    input  logic [CXTW-1:0]   bucket_cap,

    input  logic [C-1:0]      request_in,
    input  logic [C-1:0]      grant,
    input  logic              grant_valid,
    input  logic [C-1:0]      grant_ack,

    output logic [C-1:0]      request_out,
    output logic [CXTW-1:0]   tokens
);

    // One headroom bit so refill arithmetic cannot wrap before saturation
    localparam int AW = TW + 1;

    logic [TW-1:0]         w_client_cap  [C];
    logic [RATE_WIDTH-1:0] w_client_rate [C];
    logic [C-1:0]          w_bypass;          // cap 0 = unshaped (fail-open)
    logic [C-1:0]          w_spend;           // completed grant this cycle
    logic [TW-1:0]         r_tokens [C];
    logic [TW-1:0]         w_tokens_next [C];

    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_cfg
            assign w_client_cap[j]  = bucket_cap[(j+1)*TW-1 -: TW];
            assign w_client_rate[j] = rate[(j+1)*RATE_WIDTH-1 -: RATE_WIDTH];
            assign w_bypass[j]    = (w_client_cap[j] == '0);
        end
    endgenerate

    // Completion = spend, same contract as the arbiter family
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_spend
            assign w_spend[i] = (WAIT_GNT_ACK == 0) ?
                                (grant[i] && grant_valid) :
                                (grant[i] && grant_valid && grant_ack[i]);
        end
    endgenerate

    // Bucket update: refill composes with a same-cycle spend as
    // refill-then-spend, so a rate-1 client under saturation sustains
    // exactly one grant per tick. The cap clamp is applied UNCONDITIONALLY,
    // not only at refill: cap is the burst-allowance INVARIANT, and a
    // runtime cap decrease must bite immediately - a refill-time-only clamp
    // leaves a client holding (and spending) tokens above its new cap, and
    // with rate 0 it would never clamp at all. (Found by the TB ledger:
    // clients carried 6 tokens across a cap change to 4 and burst past the
    // contract.)
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_bucket
            logic [AW-1:0] w_after_refill;

            always_comb begin
                w_after_refill = AW'(r_tokens[i]);
                if (refill_tick) begin
                    w_after_refill = AW'(r_tokens[i]) + AW'(w_client_rate[i]);
                end
                if (w_after_refill > AW'(w_client_cap[i])) begin
                    w_after_refill = AW'(w_client_cap[i]);
                end
                if (w_spend[i] && (w_after_refill != '0)) begin
                    w_after_refill = w_after_refill - AW'(1);
                end
                w_tokens_next[i] = TW'(w_after_refill);
            end

            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_tokens[i] <= '0;
                end else begin
                    r_tokens[i] <= w_tokens_next[i];
                end
            )

            assign tokens[(i+1)*TW-1 -: TW] = r_tokens[i];
        end
    endgenerate

    // Pass gate. NET OF the spend completing this cycle: the downstream
    // grant registered one cycle after arbitration saw request_out, so the
    // bucket register still shows the pre-spend value in the completion
    // cycle - gating on it raw lets a 1-token client win twice on one token
    // (the registered-decision window; see Notes). Refill is deliberately
    // NOT counted until it lands in the register - the gate may only be
    // pessimistic, never optimistic.
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_gate
            logic [TW-1:0] w_net_tokens;
            assign w_net_tokens = (w_spend[j] && r_tokens[j] != '0) ?
                                  (r_tokens[j] - TW'(1)) : r_tokens[j];
            assign request_out[j] = request_in[j] &&
                                    (w_bypass[j] || (w_net_tokens != '0));
        end
    endgenerate

endmodule : arbiter_token_bucket
