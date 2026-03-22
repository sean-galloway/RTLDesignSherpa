// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_priority_encoder (yosys-compatible)

module formal_arbiter_pe #(
    parameter int CLIENTS = 4,
    parameter int N = $clog2(CLIENTS)
) (
    input logic clk
);

    (* anyconst *) logic [CLIENTS-1:0] requests_masked;
    (* anyconst *) logic [CLIENTS-1:0] requests_unmasked;
    (* anyconst *) logic               any_masked_requests;

    logic [N-1:0] winner;
    logic          winner_valid;

    arbiter_priority_encoder #(.CLIENTS(CLIENTS)) dut (
        .requests_masked    (requests_masked),
        .requests_unmasked  (requests_unmasked),
        .any_masked_requests(any_masked_requests),
        .winner             (winner),
        .winner_valid       (winner_valid)
    );

    wire [CLIENTS-1:0] pri_req = any_masked_requests ? requests_masked : requests_unmasked;

    // winner_valid iff any request
    always @(posedge clk)
        ap_valid_iff_req: assert (winner_valid == |pri_req);

    // winner in range
    always @(posedge clk)
        if (winner_valid)
            ap_id_range: assert (winner < CLIENTS);

    // winner bit is set in priority requests
    always @(posedge clk)
        if (winner_valid)
            ap_winner_set: assert (pri_req[winner]);

    // winner is LOWEST set bit — no lower bit is set
    always @(posedge clk)
        if (winner_valid)
            ap_lowest: assert ((pri_req & ((1 << winner) - 1)) == '0);

    // masked path used when any_masked_requests
    always @(posedge clk)
        if (any_masked_requests)
            ap_masked: assert (winner_valid == |requests_masked);

    // unmasked path used otherwise
    always @(posedge clk)
        if (!any_masked_requests)
            ap_unmasked: assert (winner_valid == |requests_unmasked);

    // no valid when no requests
    always @(posedge clk)
        if (pri_req == '0)
            ap_no_req: assert (!winner_valid);

    // Cover
    always @(posedge clk) begin
        cp_all_req: cover (&pri_req && winner_valid);
        cp_no_req:  cover (pri_req == '0);
        cp_masked:  cover (any_masked_requests && winner_valid);
        cp_unmasked: cover (!any_masked_requests && winner_valid);
    end

endmodule
