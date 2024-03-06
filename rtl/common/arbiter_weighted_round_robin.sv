`timescale 1ns / 1ps
// I got the originl design from here:
// https://chipress.online/2019/06/23/weighted-round-robin-arbiter/
// I've made a bunch of changes since then, not all are tracked in git individually.
// mada a number of tweaks to make arbitration more even and performant.
module arbiter_weighted_round_robin #(
    parameter int MAX_THRESH = 4,
    parameter int MAX_THRESH_WIDTH = $clog2(MAX_THRESH),
    parameter int CLIENTS = 4
) (
    input  logic                                  i_clk,
    input  logic                                  i_rst_n,
    input  logic [(CLIENTS*MAX_THRESH_WIDTH)-1:0] i_max_thresh,
    input  logic [                   CLIENTS-1:0] i_req,
    input  logic                                  i_block_arb,
    output logic [                   CLIENTS-1:0] ow_grant
);

    // Define a local parameter
    localparam int MTW = MAX_THRESH_WIDTH;

    // Define the combi signal and flops
    logic [(CLIENTS*MAX_THRESH_WIDTH)-1:0] r_crd_cnt;
    logic [(CLIENTS*MAX_THRESH_WIDTH)-1:0] w_crd_cnt_next;
    logic [(CLIENTS*MAX_THRESH_WIDTH)-1:0] w_crd_cnt_incr;

    logic [                   CLIENTS-1:0] w_has_crd;
    logic [                   CLIENTS-1:0] w_mask_req;

    logic                                  w_replenish;

    logic [                   CLIENTS-1:0] w_req_post;
    assign w_req_post  = (i_block_arb) ? 'b0 : i_req;

    // when none of the asserted requests have credits, replenish all credit counters
    assign w_replenish = ((i_req & w_has_crd) == '0);

    genvar i;
    generate
        for (i = 0; i < CLIENTS; i++) begin : gen_credit_mgt
            // Calculate start and end indices for each client in the flattened array
            localparam int EndIdx = (i + 1) * MTW - 1;

            assign w_crd_cnt_incr[EndIdx-:MTW] = r_crd_cnt[EndIdx-:MTW] + 1'b1;
            assign w_has_crd[i] = (w_crd_cnt_incr[EndIdx-:MTW] <= i_max_thresh[EndIdx-:MTW]);

            // credit mask logic generates masked version of requests
            assign w_mask_req[i] = (w_has_crd[i] | w_replenish) & w_req_post[i];

            // next credit counter value
            always_comb begin
                w_crd_cnt_next[EndIdx-:MTW] = r_crd_cnt[EndIdx-:MTW];
                if (w_replenish)
                    if (ow_grant[i]) w_crd_cnt_next[EndIdx-:MTW] = 1;
                    else w_crd_cnt_next[EndIdx-:MTW] = 0;
                else if (ow_grant[i]) w_crd_cnt_next[EndIdx-:MTW] = w_crd_cnt_incr[EndIdx-:MTW];
            end

            // only update the credit counters when replenish or being granted
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (~i_rst_n) r_crd_cnt[EndIdx-:MTW] <= '0;
                else if (w_replenish || (ow_grant[i] && w_has_crd[i]))
                    // Only update when granted and has credits
                    r_crd_cnt[EndIdx-:MTW] <= w_crd_cnt_next[EndIdx-:MTW];
            end
        end
    endgenerate

    // the masked version of requests will be fed into normal round robin arbiter
    arbiter_round_robin_subinst #(CLIENTS) u_rrb_arb (
        .i_clk,
        .i_rst_n,
        .i_req(w_mask_req),
        .i_replenish(w_replenish),
        .ow_grant(ow_grant)
    );

endmodule : arbiter_weighted_round_robin
