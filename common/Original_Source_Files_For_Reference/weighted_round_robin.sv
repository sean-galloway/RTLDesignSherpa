// https://chipress.online/2019/06/23/weighted-round-robin-arbiter/

module wrr_arb
#( parameter MAX_THRE = 8)
(
    input                           clk,
    input                           rst_n,

    input [$clog2(MAX_THRE+1)-1:0]  max_thre,

    input [2:0]                     req,
    
    output logic [2:0]              grant
);

    logic [2:0][$clog2(MAX_THRE+1)-1:0]     crd_cnt;
    logic [2:0][$clog2(MAX_THRE+1)-1:0]     crd_cnt_next;
    logic [2:0][$clog2(MAX_THRE+1)-1:0]     crd_cnt_incr;

    logic [2:0] has_crd;
    logic [2:0] mask_req;

    logic replenish;

    // when none of the asserted requests have credits, replenish all credit counters
    assign replenish = ((req & has_crd) == '0);

    genvar i;
    generate
        for (i = 0; i < 3; i++) begin
            assign crd_cnt_incr[i] = crd_cnt[i] + 1'b1;
            assign has_crd[i] = (crd_cnt_incr[i] <= max_thre);

            // credit mask logic generates masked version of requests
            assign mask_req[i] = (has_crd[i] | replenish) & req[i];

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
    rrb_arb u_rrb_arb (.clk, .rst_n, .req(mask_req), .grant);

endmodule: wrr_arb
共