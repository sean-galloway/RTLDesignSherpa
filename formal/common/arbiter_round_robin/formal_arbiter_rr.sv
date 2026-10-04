// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_round_robin (no-ACK mode, yosys-compatible)
// Proves safety properties for the full-featured round-robin arbiter.

module formal_arbiter_rr #(
    parameter int CLIENTS = 4,
    parameter int N = (CLIENTS > 1) ? $clog2(CLIENTS) : 1
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic [CLIENTS-1:0]  request
);

    // DUT outputs
    logic                grant_valid;
    logic [CLIENTS-1:0]  grant;
    logic [N-1:0]        grant_id;
    logic [CLIENTS-1:0]  last_grant;

    // Instantiate DUT in no-ACK mode
    arbiter_round_robin #(
        .CLIENTS(CLIENTS),
        .WAIT_GNT_ACK(0)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (1'b0),        // never blocked
        .request     (request),
        .grant_ack   ({CLIENTS{1'b0}}),  // unused in no-ACK mode
        .grant_valid (grant_valid),
        .grant       (grant),
        .grant_id    (grant_id),
        .last_grant  (last_grant)
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
    // Safety properties
    // =========================================================================

    // Grant is one-hot when valid
    always @(posedge clk) begin
        if (rst_n)
            ap_onehot: assert (!grant_valid || $onehot(grant));
    end

    // Grant only to requesting agents. The multi-client DUT registers its
    // grant, so the request is checked one cycle back; the CLIENTS==1 branch
    // (gen_single_client) is combinational, so its request is checked in the
    // same cycle.
    if (CLIENTS == 1) begin : gen_subset_c1
        always @(posedge clk) begin
            if (rst_n)
                ap_subset: assert (!grant_valid || ((grant & request) == grant));
        end
    end else begin : gen_subset_multi
        always @(posedge clk) begin
            if (f_past_valid > 0 && rst_n && $past(rst_n))
                ap_subset: assert (!grant_valid || ((grant & $past(request)) == grant));
        end
    end

    // No grant bits when not valid
    always @(posedge clk) begin
        if (rst_n)
            ap_no_spurious: assert (grant_valid || (grant == '0));
    end

    // grant_id matches grant bit when valid
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_matches: assert (grant[grant_id]);
    end

    // grant_id in valid range
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_range: assert (grant_id < CLIENTS);
    end

    // last_grant is previous cycle's grant
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_last_grant: assert (last_grant == $past(grant));
    end

    // After reset, outputs are zero. The grant/valid checks assume a
    // registered grant (the multi-client path); the CLIENTS==1 branch is
    // combinational, so its "reset" property is ap_subset+ap_onehot -- a
    // grant is high only while its request is, reset or not. last_grant is
    // registered in BOTH branches, so that check stays universal.
    always @(posedge clk) begin
        if (CLIENTS > 1 && f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_grant: assert (grant == '0);
            ap_reset_valid: assert (!grant_valid);
        end
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_last:  assert (last_grant == '0);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Each agent can be granted
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_cov
            always @(posedge clk) begin
                if (rst_n) cover (grant_valid && grant[i]);
            end
        end
    endgenerate

    // All agents requesting
    always @(posedge clk) begin
        if (rst_n) cp_all_req: cover (&request);
    end

    // Back-to-back grants to different agents
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_rotate: cover (grant_valid && $past(grant_valid) && (grant != $past(grant)));
    end

endmodule
