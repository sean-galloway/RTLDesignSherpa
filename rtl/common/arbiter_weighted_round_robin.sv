`timescale 1ns / 1ps
// I got the originl design from here:
// https://chipress.online/2019/06/23/weighted-round-robin-arbiter/
// I've made a bunch of changes since then, not all are tracked in git individually.
// mada a number of tweaks to make arbitration more even and performant.
module arbiter_weighted_round_robin
#(  parameter MAX_THRESH = 8,
    parameter CLIENTS = 8)
(
    input  logic                                        i_clk,
    input  logic                                        i_rst_n,
    input  logic [CLIENTS-1:0] [$clog2(MAX_THRESH)-1:0] i_max_thresh,
    input  logic [CLIENTS-1:0]                          i_req,
    input  logic                                        i_block_arb,
    output logic [CLIENTS-1:0]                          ow_grant
);

    // Define the combi signal and flops
    logic [CLIENTS-1:0] [$clog2(MAX_THRESH+1)-1:0]     r_crd_cnt;
    logic [CLIENTS-1:0] [$clog2(MAX_THRESH+1)-1:0]     w_crd_cnt_next;
    logic [CLIENTS-1:0] [$clog2(MAX_THRESH+1)-1:0]     w_crd_cnt_incr;

    logic [CLIENTS-1:0] w_has_crd;
    logic [CLIENTS-1:0] w_mask_req;

    logic w_replenish;

    logic [CLIENTS-1:0] w_req_post;
    assign w_req_post = (i_block_arb) ? 'b0 : i_req;

    // when none of the asserted requests have credits, replenish all credit counters
    assign w_replenish = ((i_req & w_has_crd) == '0);

    genvar i;
    generate
        for (i = 0; i < CLIENTS; i++) begin
            assign w_crd_cnt_incr[i] = r_crd_cnt[i] + 1'b1;
            assign w_has_crd[i] = (w_crd_cnt_incr[i] <= i_max_thresh[i]);

            // credit mask logic generates masked version of requests
            assign w_mask_req[i] = (w_has_crd[i] | w_replenish) & w_req_post[i];

            // next credit counter value
            always_comb begin
                w_crd_cnt_next[i] = r_crd_cnt[i];
                if (w_replenish)
                    if (ow_grant[i])
                        w_crd_cnt_next[i] = 1;
                    else
                        w_crd_cnt_next[i] = 0;
                else if (ow_grant[i])
                    w_crd_cnt_next[i] = w_crd_cnt_incr[i];
            end

            // only update the credit counters when replenish or being granted
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (~i_rst_n)
                    r_crd_cnt[i] <= '0;
                else if (w_replenish || (ow_grant[i] && w_has_crd[i])) // Only update when granted and has credits
                    r_crd_cnt[i] <= w_crd_cnt_next[i];
            end
            
        end
    endgenerate

    // the masked version of requests will be fed into normal round robin arbiter
    arbiter_round_robin_subinst #(CLIENTS) u_rrb_arb (.i_clk, .i_rst_n, .i_req(w_mask_req), .i_replenish(w_replenish), .ow_grant(ow_grant));

    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, arbiter_weighted_round_robin);
    end
    // synopsys translate_on

endmodule: arbiter_weighted_round_robin