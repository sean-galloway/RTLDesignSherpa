`timescale 1ns / 1ps

module arbiter_round_robin_weighted #(
    parameter int MAX_THRESH = 16,
    parameter int MAX_THRESH_WIDTH = $clog2(MAX_THRESH),
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Short Parameters
    parameter int C = CLIENTS,
    parameter int N = $clog2(CLIENTS),
    parameter int MTW = MAX_THRESH_WIDTH,
    parameter int CXMTW = CLIENTS*MAX_THRESH_WIDTH

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
    assign w_replenish = ((i_req & w_has_crd) == '0) && (i_req != '0);

    genvar i;
    generate
        for (i = 0; i < CLIENTS; i++) begin : gen_credit_mgt
            // Calculate start and end indices for each client in the flattened array
            localparam int EndIdx = (i + 1) * MTW - 1;

            assign w_crd_cnt_incr[EndIdx-:MTW] = r_crd_cnt[EndIdx-:MTW] + 1'b1;
            assign w_has_crd[i] = (w_crd_cnt_incr[EndIdx-:MTW] <= i_max_thresh[EndIdx-:MTW]);

            // credit mask logic generates masked version of requests
            assign w_mask_req[i] = (w_has_crd[i] | w_replenish) & w_req_post[i];

            // Simplified next credit counter value calculation
            always_comb begin
                w_crd_cnt_next[EndIdx-:MTW] = r_crd_cnt[EndIdx-:MTW];
                if (w_replenish) begin
                    // During replenish, set credits based on grants
                    if (ow_gnt[i])
                        w_crd_cnt_next[EndIdx-:MTW] = 1;
                    else
                        w_crd_cnt_next[EndIdx-:MTW] = 0;
                end else if (ow_gnt[i] && w_has_crd[i]) begin
                    // Normal operation: increment credit counter when granted
                    w_crd_cnt_next[EndIdx-:MTW] = w_crd_cnt_incr[EndIdx-:MTW];
                end
            end

            // Modified credit counter update logic with better synchronization
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (~i_rst_n) begin
                    r_crd_cnt[EndIdx-:MTW] <= '0;
                end else begin
                    // When replenish signal is active or this client is granted
                    if ((w_replenish && ow_gnt[i]) || (ow_gnt[i] && w_has_crd[i])) begin
                        // Only update when grant is acknowledged (if waiting for ack)
                        if (~WAIT_GNT_ACK || i_gnt_ack[i]) begin
                            r_crd_cnt[EndIdx-:MTW] <= w_crd_cnt_next[EndIdx-:MTW];
                        end
                    end else if (w_replenish && !ow_gnt[i]) begin
                        // Reset credits for non-granted clients during replenish
                        r_crd_cnt[EndIdx-:MTW] <= '0;
                    end
                end
            end
        end
    endgenerate

    // the masked version of requests will be fed into normal round robin arbiter
    arbiter_round_robin_weighted_subinst #(
        .CLIENTS(CLIENTS),
        .WAIT_GNT_ACK(WAIT_GNT_ACK)
    ) u_rrb_arb (
        .i_clk,
        .i_rst_n,
        .i_req(w_mask_req),
        .i_replenish(w_replenish),
        .ow_grant(ow_gnt),
        .i_gnt_ack(i_gnt_ack)
    );

    // Compute the grant ID from the one-hot ow_gnt signal
    always_comb begin
        ow_gnt_id = '0;  // Default value
        for (int j = 0; j < C; j++) begin
            if (ow_gnt[j]) begin
                ow_gnt_id = j;
            end
        end
    end

    // Generate grant valid signal
    assign ow_gnt_valid = |ow_gnt;

endmodule : arbiter_round_robin_weighted
