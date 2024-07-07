`timescale 1ns / 1ps
// I got the originl design from here:
// https://chipress.online/2019/06/23/weighted-round-robin-arbiter/
// I've made a bunch of changes since then, not all are tracked in git individually.
// mada a number of tweaks to make arbitration more even and performant.
module arbiter_weighted_round_robin #(
    parameter int MAX_THRESH = 16,
    parameter int MAX_THRESH_WIDTH = $clog2(MAX_THRESH),
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0
) (
    input  logic              i_clk,
    input  logic              i_rst_n,
    input  logic              i_block_arb,
    input  logic [CXMTW-1:0]  i_max_thresh,
    input  logic [C-1:0]      i_req,
    output logic              ow_gnt_valid,
    output logic [C-1:0]      ow_gnt,
    output logic [N-1:0]      ow_gnt_id,
    input  logic [C-1:0]      i_gnt_ack
);

    // =======================================================================
    // Declarations & Parameters
    localparam int C = CLIENTS;
    localparam int N = $clog2(CLIENTS);
    localparam int MTW = MAX_THRESH_WIDTH;
    localparam int CXMTW = CLIENTS*MAX_THRESH_WIDTH;

    // Define the combi signal and flops
    logic [CXMTW-1:0] r_crd_cnt;
    logic [CXMTW-1:0] w_crd_cnt_next;
    logic [CXMTW-1:0] w_crd_cnt_incr;
    logic [C-1:0]     w_has_crd;
    logic [C-1:0]     w_mask_req;
    logic             w_replenish;
    logic [C-1:0]     w_req_post;

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
                    if (ow_gnt[i]) w_crd_cnt_next[EndIdx-:MTW] = 1;
                    else w_crd_cnt_next[EndIdx-:MTW] = 0;
                else if (ow_gnt[i]) w_crd_cnt_next[EndIdx-:MTW] = w_crd_cnt_incr[EndIdx-:MTW];
            end

            // only update the credit counters when replenish or being granted
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (~i_rst_n) r_crd_cnt[EndIdx-:MTW] <= '0;
                else if (w_replenish || (ow_gnt[i] && w_has_crd[i]))
                    if ((~WAIT_GNT_ACK) || (i_gnt_ack[i]))
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
        .ow_grant(ow_gnt),
        .i_gnt_ack(i_gnt_ack)
    );

    // Iterate over the one-hot bus to find the set bit
    always_comb begin
        ow_gnt_id = '0;  // Default value, can be used to indicate an error
        for (int i = 0; i < C; i++) begin
            if (ow_gnt[i]) begin
                ow_gnt_id = i;
            end
        end
    end

    assign ow_gnt_valid = |ow_gnt;

endmodule : arbiter_weighted_round_robin
