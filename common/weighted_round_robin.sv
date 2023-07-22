`timescale 1ns / 1ps
// I got the originl design from here:
// https://chipress.online/2019/06/23/weighted-round-robin-arbiter/
// I've made a bunch of changes since then, not all are tracked in git.
module weighted_round_robin
#(  parameter MAX_THRESH = 8,
    parameter CLIENTS = 8)
(
    input  logic                                       clk,
    input  logic                                       rst_n,
    input  logic [CLIENTS-1:0][$clog2(MAX_THRESH)-1:0] max_thresh,
    input  logic [CLIENTS-1:0]                         req,
    output logic [CLIENTS-1:0]                         grant
);

    // Define the combi signal and flops
    logic [CLIENTS-1:0][$clog2(MAX_THRESH+1)-1:0]     crd_cnt;
    logic [CLIENTS-1:0][$clog2(MAX_THRESH+1)-1:0]     crd_cnt_next;
    logic [CLIENTS-1:0][$clog2(MAX_THRESH+1)-1:0]     crd_cnt_incr;

    logic [CLIENTS-1:0] has_crd;
    logic [CLIENTS-1:0] mask_req;

    logic replenish;

    // when none of the asserted requests have credits, replenish all credit counters
    assign replenish = ((req & has_crd) == '0);

    genvar i;
    generate
        for (i = 0; i < CLIENTS; i = i + 1) begin
            assign crd_cnt_incr[i] = crd_cnt[i] + 1'b1;
            assign has_crd[i] = (crd_cnt_incr[i] <= max_thresh[i]);

            // credit mask logic generates masked version of requests
            assign mask_req[i] = (has_crd[i] | replenish) & req[i];

            // next credit counter value
            // next credit counter value
            always_comb begin
                crd_cnt_next[i] = crd_cnt[i];
                if (replenish)
                    if (grant[i])
                        crd_cnt_next[i] = 1;
                    else
                        crd_cnt_next[i] = 0;
                else if (grant[i])
                    crd_cnt_next[i] = crd_cnt_incr[i];
            end

            // only update the credit counters when replenish or being granted
            always_ff @(posedge clk or negedge rst_n)
                if (~rst_n)
                    crd_cnt[i] <= '0;
                else if (replenish | grant[i])
                    crd_cnt[i] <= crd_cnt_next[i];
        end
    endgenerate

    // the masked version of requests will be fed into normal round robin arbiter
    rrb_arb #(CLIENTS) u_rrb_arb (.clk, .rst_n, .req(mask_req), .grant(grant));

endmodule: weighted_round_robin