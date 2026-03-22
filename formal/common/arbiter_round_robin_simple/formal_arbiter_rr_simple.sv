// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_round_robin_simple (yosys-compatible)
// Run with: sby arbiter_round_robin_simple.sby

module formal_arbiter_rr_simple #(
    parameter int N = 4,
    parameter int W = $clog2(N)
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] request
);

    // DUT outputs
    logic          grant_valid;
    logic [N-1:0]  grant;
    logic [W-1:0]  grant_id;

    // Instantiate DUT
    arbiter_round_robin_simple #(
        .N(N), .W(W)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .request     (request),
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
            ap_grant_onehot: assert (!grant_valid || $onehot(grant));
    end

    // Grant only to a requesting agent
    always @(posedge clk) begin
        if (rst_n)
            ap_grant_subset: assert (!grant_valid || ((grant & request) == grant));
    end

    // No grant bits when not valid
    always @(posedge clk) begin
        if (rst_n)
            ap_no_spurious: assert (grant_valid || (grant == '0));
    end

    // grant_valid iff any request
    always @(posedge clk) begin
        if (rst_n)
            ap_valid_iff_req: assert (grant_valid == |request);
    end

    // grant_id matches granted bit
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_matches: assert (grant[grant_id]);
    end

    // grant_id in range
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_id_range: assert (grant_id < N);
    end

    // =========================================================================
    // Fairness note: This arbiter is combinational — it picks a new winner
    // each cycle based on (request, r_last_grant). With changing request
    // patterns, bounded fairness properties are hard to express in BMC.
    // The safety properties above (one-hot, subset, valid-iff-request)
    // are the high-value formal checks. Fairness is validated by simulation.

    // =========================================================================
    // Cover properties
    // =========================================================================
    generate
        for (genvar i = 0; i < N; i++) begin : gen_cov
            always @(posedge clk) begin
                if (rst_n) cover (grant_valid && grant[i]); // cp_grant_i
            end
        end
    endgenerate

    always @(posedge clk) begin
        if (rst_n) cp_all_req: cover (&request && grant_valid);
    end

    always @(posedge clk) begin
        if (rst_n) cp_single: cover ($onehot(request) && grant_valid);
    end

endmodule
