`timescale 1ns / 1ps
module arbiter_round_robin_weighted_subinst #(
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter int C = CLIENTS
) (
    input  logic i_clk,
    input  logic i_rst_n,
    input  logic [C-1:0] i_req,
    input  logic i_replenish,
    output logic [C-1:0] ow_grant,
    input  logic [C-1:0] i_gnt_ack
);
    logic [C-1:0] r_mask;
    logic [C-1:0] w_mask_req;
    logic [C-1:0] w_raw_grant;
    logic [C-1:0] w_mask_grant;
    logic w_select_raw;

    // mask update logic
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n)
            r_mask <= {CLIENTS{1'b1}};
        else begin
            r_mask <= {CLIENTS{1'b0}};
            for (int i = 0; i < CLIENTS; i++) begin
                if (ow_grant[i])
                    if ((WAIT_GNT_ACK == 0) || (i_gnt_ack[i]))
                        r_mask[i] <= 1'b1;
                end
            end
    end
    // masked requests
    assign w_mask_req = i_req & r_mask;
    // grant for raw requests in case mask == 'b0
    arbiter_round_robin_weighted_fixed_priority #(CLIENTS) u_arb_raw (
        .i_req(i_req),
        .ow_grant(w_raw_grant)
    );
    // grant for masked requests in case mask != 'b0
    arbiter_round_robin_weighted_fixed_priority #(CLIENTS) u_arb_mask (
        .i_req(w_mask_req),
        .ow_grant(w_mask_grant)
    );
    // final grant
    assign w_select_raw = i_replenish || (w_mask_req == {CLIENTS{1'b0}});
    assign ow_grant = w_select_raw ? w_raw_grant : w_mask_grant;

endmodule : arbiter_round_robin_weighted_subinst
