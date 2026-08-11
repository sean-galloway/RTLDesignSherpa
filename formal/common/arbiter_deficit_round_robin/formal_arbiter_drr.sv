// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Formal wrapper for arbiter_deficit_round_robin (yosys-compatible)
//
// Safety set mirrors the WRR sibling (one-hot, subset-of-request, id
// matches/range, reset zeros) plus the DRR-specific contract that is
// observable at the ports: a zero-quantum client is never granted, and
// req_cost is a free input every cycle - the harshest test of the DUT's
// r_cost_arb pipeline and cost-0 defense, since the solver may change a
// client's cost in the completion cycle at will.
//
// Deficit dynamics (replenish accumulation, carry) are witnessed by cover
// properties rather than asserted: a grant that arrives only after idle
// accumulation cycles is the external signature of the replenish loop.

module formal_arbiter_drr #(
    parameter int MAX_QUANTUM  = 4,
    parameter int CLIENTS      = 4,
    parameter int COST_WIDTH   = 3,
    parameter int WAIT_GNT_ACK = 0,
    // Derived -- mirror the DUT derivations
    parameter int QW   = $clog2(MAX_QUANTUM),
    parameter int N    = $clog2(CLIENTS),
    parameter int C    = CLIENTS,
    parameter int CXQW = CLIENTS * QW,
    parameter int CXCW = CLIENTS * COST_WIDTH
) (
    input  logic            clk,
    input  logic            rst_n,
    input  logic [C-1:0]    request,
    input  logic [CXCW-1:0] req_cost
);

    // DUT outputs
    logic         grant_valid;
    logic [C-1:0] grant;
    logic [N-1:0] grant_id;

    // Static quantum configuration: client C-1 DISABLED (quantum 0), the
    // rest alternate 1 and 2 - mixed shares plus the disable case in one
    // config, so ap_zero_quantum has a real target.
    logic [CXQW-1:0] quantum;
    generate
        for (genvar q = 0; q < CLIENTS; q++) begin : gen_quanta
            if (q == CLIENTS-1) begin : g_disabled
                assign quantum[(q+1)*QW-1 -: QW] = '0;
            end else if (q % 2 == 0) begin : g_two
                assign quantum[(q+1)*QW-1 -: QW] = QW'(2);
            end else begin : g_one
                assign quantum[(q+1)*QW-1 -: QW] = QW'(1);
            end
        end
    endgenerate

    // Instantiate DUT in no-ACK mode with block_arb=0, grant_ack=0
    arbiter_deficit_round_robin #(
        .CLIENTS      (CLIENTS),
        .MAX_QUANTUM  (MAX_QUANTUM),
        .COST_WIDTH   (COST_WIDTH),
        .WAIT_GNT_ACK (WAIT_GNT_ACK)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (1'b0),
        .quantum     (quantum),
        .req_cost    (req_cost),
        .request     (request),
        .grant_ack   ({C{1'b0}}),
        .grant_valid (grant_valid),
        .grant       (grant),
        .grant_id    (grant_id)
    );

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

    // =========================================================================
    // Safety properties (family set)
    // =========================================================================

    always @(posedge clk) begin
        if (rst_n)
            ap_onehot: assert (!grant_valid || $onehot(grant));
    end

    // Grant only to previously-requesting agents (registered-grant pipeline)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_subset: assert (!grant_valid || ((grant & $past(request)) == grant));
    end

    always @(posedge clk) begin
        if (rst_n)
            ap_no_spurious: assert (grant_valid || (grant == '0));
    end

    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_matches: assert (grant[grant_id]);
    end

    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_range: assert (grant_id < CLIENTS);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_grant: assert (grant == '0);
            ap_reset_valid: assert (!grant_valid);
        end
    end

    // =========================================================================
    // DRR-specific safety
    // =========================================================================

    // A zero-quantum client is disabled: never granted, no matter what costs
    // and requests the solver drives
    always @(posedge clk) begin
        if (rst_n)
            ap_zero_quantum: assert (!grant[CLIENTS-1]);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Every ENABLED client can be granted (the disabled one is asserted
    // never-granted above; covering it would be vacuous by construction)
    generate
        for (genvar i = 0; i < CLIENTS-1; i++) begin : gen_cov
            always @(posedge clk) begin
                if (rst_n) cover (grant_valid && grant[i]);
            end
        end
    endgenerate

    // Replenish accumulation, observed externally: a client granted only
    // AFTER two grant-less cycles with its request held is a client that had
    // to save up deficit across replenish rounds
    always @(posedge clk) begin
        if (f_past_valid > 3 && rst_n)
            cp_accumulate: cover (grant_valid && grant[1] &&
                                  !$past(grant_valid) && !$past(grant_valid, 2) &&
                                  $past(request[1]) && $past(request[1], 2));
    end

    // Rotation among enabled clients
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_rotate: cover (grant_valid && $past(grant_valid) &&
                              (grant != $past(grant)));
    end

    // All enabled clients requesting at once
    always @(posedge clk) begin
        if (rst_n) cp_all_req: cover (&request[CLIENTS-2:0]);
    end

endmodule
