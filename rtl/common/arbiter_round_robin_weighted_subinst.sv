`timescale 1ns / 1ps
module arbiter_round_robin_weighted_subinst #(
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter int C = CLIENTS
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [C-1:0] req,
    input  logic         replenish,
    output logic [C-1:0] grant,
    input  logic [C-1:0] gnt_ack
);
    logic [C-1:0] r_mask;
    logic [C-1:0] w_mask_req;
    logic [C-1:0] w_raw_grant;
    logic [C-1:0] w_mask_grant;
    logic w_select_raw;

    // mask update logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n)
            r_mask <= {CLIENTS{1'b1}};
        else begin
            r_mask <= {CLIENTS{1'b0}};
            for (int i = 0; i < CLIENTS; i++) begin
                if (grant[i])
                    if ((WAIT_GNT_ACK == 0) || (gnt_ack[i]))
                        r_mask[i] <= 1'b1;
                end
            end
    end
    // masked requests
    assign w_mask_req = req & r_mask;
    // grant for raw requests in case mask == 'b0
    arbiter_round_robin_weighted_fixed_priority #(CLIENTS) u_arb_raw (
        .req(req),
        .grant(w_raw_grant)
    );
    // grant for masked requests in case mask != 'b0
    arbiter_round_robin_weighted_fixed_priority #(CLIENTS) u_arb_mask (
        .req(w_mask_req),
        .grant(w_mask_grant)
    );
    // final grant
    assign w_select_raw = replenish || (w_mask_req == {CLIENTS{1'b0}});
    assign grant = w_select_raw ? w_raw_grant : w_mask_grant;

endmodule : arbiter_round_robin_weighted_subinst
