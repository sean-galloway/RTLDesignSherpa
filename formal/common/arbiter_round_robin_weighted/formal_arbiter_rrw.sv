// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_round_robin_weighted (yosys-compatible)
// Proves one-hot grant, subset-of-request, valid-iff-req, id matches,
// id range, and reset zeros -- same safety set as arbiter_round_robin.

module formal_arbiter_rrw #(
    parameter int MAX_LEVELS = 4,
    parameter int CLIENTS    = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Derived -- mirror the DUT derivations
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    parameter int N    = $clog2(CLIENTS),
    parameter int C    = CLIENTS,
    parameter int MTW  = MAX_LEVELS_WIDTH,
    parameter int CXMTW = CLIENTS * MAX_LEVELS_WIDTH
) (
    input  logic               clk,
    input  logic               rst_n,
    input  logic [CLIENTS-1:0] request
);

    // DUT outputs
    logic                grant_valid;
    logic [C-1:0]        grant;
    logic [N-1:0]        grant_id;

    // Static weight configuration: equal weights of 1 per client
    // Each client gets MTW bits; all set to 1.
    logic [CXMTW-1:0] max_thresh;
    assign max_thresh = {CLIENTS{MTW'(1)}};

    // Instantiate DUT in no-ACK mode with block_arb=0, grant_ack=0
    arbiter_round_robin_weighted #(
        .MAX_LEVELS   (MAX_LEVELS),
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (WAIT_GNT_ACK)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (1'b0),
        .max_thresh  (max_thresh),
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
    // Safety properties
    // =========================================================================

    // Grant is one-hot when valid
    always @(posedge clk) begin
        if (rst_n)
            ap_onehot: assert (!grant_valid || $onehot(grant));
    end

    // Grant only to requesting agents (compare against previous-cycle request,
    // because the weighted arbiter has internal pipeline delay like the base RR).
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_subset: assert (!grant_valid || ((grant & $past(request)) == grant));
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

    // After reset, outputs are zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_grant: assert (grant == '0);
            ap_reset_valid: assert (!grant_valid);
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
