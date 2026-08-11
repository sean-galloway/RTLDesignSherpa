// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Formal wrapper for arbiter_token_bucket (yosys-compatible)
//
// The shaper's whole contract is assertable at the ports because the tokens
// observability output exposes the bucket levels:
//   - CAP INVARIANT: tokens never exceed the cap, ANY cycle (the per-cycle
//     clamp - this is the invariant the TB found was refill-time-only)
//   - the pass gate only ever masks (subset of request_in), is transparent
//     for a cap-0 bypass client, and never forwards a dry shaped client
//   - spend debits exactly one token; refill adds exactly rate (saturating)
//
// grant/grant_valid are free inputs constrained only to be one-hot-or-idle:
// the shaper must keep its invariants even against an arbiter that grants
// clients that never asked (spend floors at zero, never wraps).
//
// LIMITATION: rate/cap are STATIC in this harness, so the cap-DECREASE
// clamp (banked burst forfeited immediately when cap drops) is not proved
// here - with a static cap, a refill-time-only clamp is indistinguishable
// from the per-cycle clamp. The dynamic-cap behavior is verified by the
// simulation TB's rate0/cap-change scenarios. A free-cap harness with
// $past(cap) assertions is the upgrade path if it ever needs proving.

module formal_arbiter_token_bucket #(
    parameter int CLIENTS      = 4,
    parameter int MAX_TOKENS   = 8,
    parameter int RATE_WIDTH   = 2,
    parameter int WAIT_GNT_ACK = 0,
    // Derived -- mirror the DUT derivations
    parameter int TW   = $clog2(MAX_TOKENS),
    parameter int C    = CLIENTS,
    parameter int CXTW = CLIENTS * TW,
    parameter int CXRW = CLIENTS * RATE_WIDTH
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic         refill_tick,
    input  logic [C-1:0] request_in,
    input  logic [C-1:0] grant,
    input  logic         grant_valid
);

    // DUT outputs
    logic [C-1:0]    request_out;
    logic [CXTW-1:0] tokens;

    // Static config: client C-1 is BYPASS (cap 0); the rest get cap 3 and
    // alternating rates 1/2 - shaping plus the fail-open case in one config.
    logic [CXTW-1:0] bucket_cap;
    logic [CXRW-1:0] rate;
    generate
        for (genvar q = 0; q < CLIENTS; q++) begin : gen_cfg
            if (q == CLIENTS-1) begin : g_bypass
                assign bucket_cap[(q+1)*TW-1 -: TW] = '0;
            end else begin : g_shaped
                assign bucket_cap[(q+1)*TW-1 -: TW] = TW'(3);
            end
            assign rate[(q+1)*RATE_WIDTH-1 -: RATE_WIDTH] =
                (q % 2 == 0) ? RATE_WIDTH'(1) : RATE_WIDTH'(2);
        end
    endgenerate

    arbiter_token_bucket #(
        .CLIENTS      (CLIENTS),
        .MAX_TOKENS   (MAX_TOKENS),
        .RATE_WIDTH   (RATE_WIDTH),
        .WAIT_GNT_ACK (WAIT_GNT_ACK)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .refill_tick (refill_tick),
        .rate        (rate),
        .bucket_cap  (bucket_cap),
        .request_in  (request_in),
        .grant       (grant),
        .grant_valid (grant_valid),
        .grant_ack   ({C{1'b0}}),
        .request_out (request_out),
        .tokens      (tokens)
    );

    // Per-client views
    logic [TW-1:0] tok [C];
    logic [C-1:0]  spend;
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_view
            assign tok[i] = tokens[(i+1)*TW-1 -: TW];
            assign spend[i] = grant[i] && grant_valid;   // no-ACK completion
        end
    endgenerate

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // The downstream arbiter grants one client or none
    always @(posedge clk) begin
        assume ($onehot0(grant));
        assume (grant_valid == |grant);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // THE cap invariant: a shaped bucket never holds more than its cap, on
    // any cycle - the per-cycle clamp, not a refill-time bound
    generate
        for (genvar i = 0; i < CLIENTS-1; i++) begin : gen_cap_inv
            always @(posedge clk) begin
                if (rst_n)
                    assert (tok[i] <= TW'(3));
            end
        end
    endgenerate

    // The gate only masks - never invents a request
    always @(posedge clk) begin
        if (rst_n)
            ap_gate_subset: assert ((request_out & ~request_in) == '0);
    end

    // Fail-open: the bypass client's request passes through untouched
    always @(posedge clk) begin
        if (rst_n)
            ap_bypass_transparent:
                assert (request_out[CLIENTS-1] == request_in[CLIENTS-1]);
    end

    // A dry shaped client is never forwarded - including the net-of-spend
    // case (one token, spend completing this cycle)
    generate
        for (genvar i = 0; i < CLIENTS-1; i++) begin : gen_gate_dry
            always @(posedge clk) begin
                if (rst_n) begin
                    assert (!(request_out[i] && tok[i] == '0));
                    assert (!(request_out[i] && tok[i] == TW'(1)
                                           && spend[i]));
                end
            end
        end
    endgenerate

    // Spend without refill debits exactly one token (floor at zero)
    generate
        for (genvar i = 0; i < CLIENTS-1; i++) begin : gen_debit
            always @(posedge clk) begin
                if (f_past_valid > 2 && rst_n && $past(rst_n)) begin
                    if ($past(spend[i]) && !$past(refill_tick)
                        && $past(tok[i]) != '0)
                        assert (tok[i] == $past(tok[i]) - TW'(1));
                    // No activity: bucket holds
                    if (!$past(spend[i]) && !$past(refill_tick))
                        assert (tok[i] == $past(tok[i]));
                end
            end
        end
    endgenerate

    // =========================================================================
    // Cover properties
    // =========================================================================

    // A shaped bucket reaches its cap (refill saturation is reachable)
    always @(posedge clk) begin
        if (rst_n) cp_saturate: cover (tok[0] == TW'(3));
    end

    // Refill and spend in the same cycle compose
    always @(posedge clk) begin
        if (rst_n) cp_refill_and_spend: cover (refill_tick && spend[0]
                                               && tok[0] != '0);
    end

    // The gate actually blocks someone (request in, dry bucket, masked out)
    always @(posedge clk) begin
        if (rst_n) cp_gate_blocks: cover (request_in[0] && !request_out[0]);
    end

    // The bypass client is forwarded while a shaped client is blocked
    always @(posedge clk) begin
        if (rst_n) cp_bypass_while_blocked:
            cover (request_out[CLIENTS-1] && request_in[0] && !request_out[0]);
    end

endmodule
