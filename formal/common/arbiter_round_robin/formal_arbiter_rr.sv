// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_round_robin (no-ACK mode, yosys-compatible)
// Proves safety properties for the full-featured round-robin arbiter.

module formal_arbiter_rr #(
    parameter int CLIENTS = 4,
    parameter int N = $clog2(CLIENTS)
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

    // Grant only to requesting agents
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

    // last_grant is previous cycle's grant
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_last_grant: assert (last_grant == $past(grant));
    end

    // After reset, outputs are zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_grant: assert (grant == '0);
            ap_reset_valid: assert (!grant_valid);
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
