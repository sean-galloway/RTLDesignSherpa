`timescale 1ns / 1ps

module arbiter_round_robin #(
    parameter int CLIENTS      = 4,
    parameter int WAIT_GNT_ACK = 0,
    // Abbreviation
    parameter int N = $clog2(CLIENTS)
) (
    input logic clk,
    input logic rst_n,
    input logic block_arb,

    input  logic [CLIENTS-1:0]  req,
    output logic                gnt_valid,
    output logic [CLIENTS-1:0]  gnt,
    output logic [N-1:0]        gnt_id,
    input  logic [CLIENTS-1:0]  gnt_ack
);

    // =======================================================================
    logic [CLIENTS-1:0] r_mask;
    logic [CLIENTS-1:0] r_win_mask_only;
    logic [CLIENTS-1:0] w_req_post;
    logic [      N-1:0] w_req_location;
    logic [      N-1:0] w_reqm_location;
    logic               w_vld_ffs_req;
    logic               w_vld_ffs_reqm;
    logic [CLIENTS-1:0] w_req_masked;
    logic [CLIENTS-1:0] w_req_win_mask;
    logic [      N-1:0] w_winner;
    logic               w_win_vld;

    // =======================================================================
    // Logic
    assign w_req_post = (block_arb) ? 'b0 : req;
    assign w_req_masked = w_req_post & r_mask;
    assign w_req_win_mask = ($countones(req) > 1) ? (w_req_post & r_win_mask_only) :
            w_req_post;  // only look at the req's if there is only one

    // find highest set bit in both request and masked request; priority shifts
    // down the bit vector, but returns to the top of the bit vector when no
    // lower bits are set
    // NOTE: due to the way the arb colde below is structured, it will always start at the highest bit and work its way down.
    leading_one_trailing_one #(
        .WIDTH(CLIENTS)
    ) u_req_leading_one_trailing_one (
        .data               (w_req_win_mask),
        .leadingone        (),
        .leadingone_vector (),
        .trailingone       (w_req_location),
        .trailingone_vector(),
        .all_zeroes        (),
        .all_ones          (),
        .valid             (w_vld_ffs_req)
    );

    leading_one_trailing_one #(
        .WIDTH(CLIENTS)
    ) u_reqm_leading_one_trailing_one (
        .data               (w_req_masked),
        .leadingone        (),
        .leadingone_vector (),
        .trailingone       (w_reqm_location),
        .trailingone_vector(),
        .all_zeroes        (),
        .all_ones          (),
        .valid             (w_vld_ffs_reqm)
    );

    // determine the winner--either the masked version (because a lower-priority
    // request was set) or the unmasked version (because we started over from
    // the top)
    always_comb begin
        if (w_vld_ffs_reqm) begin
            w_winner  = w_reqm_location;
            w_win_vld = 1'b1;
        end else if (w_vld_ffs_req) begin
            w_winner  = w_req_location;
            w_win_vld = 1'b1;
        end else begin
            w_winner  = {{N{1'b0}}};
            w_win_vld = 1'b0;
        end
    end

    // Register:  r_win_mask_only
    //
    // When considering the upper part of the vector for the start-over
    // case, we still need to mask off the bit that just won so we don't
    // grant to it twice in a row.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) r_win_mask_only <= '0;
        else if (w_win_vld && (WAIT_GNT_ACK == 0 || gnt_ack[w_winner]))
            r_win_mask_only <= ~({(CLIENTS - 1)'('d0), 1'b1} << w_winner);
        else
            r_win_mask_only <= {CLIENTS{1'b1}};

    // Register:  r_mask
    //
    // The r_mask depends on the previous winner.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) r_mask <= '0;
        else if (w_win_vld && (WAIT_GNT_ACK == 0 || gnt_ack[w_winner]))
            r_mask <= ({(CLIENTS - 1)'('d0), 1'b1} << w_winner) - 1'b1;

    // Register:  gnt
    //
    // Priority is given to lower bits i.e., those getting a gnt when using
    // the mask vector.  If no lower bits are set, the unmasked request result
    // is used.
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            gnt       <= '0;
            gnt_id    <= '0;
            gnt_valid <= '0;
        end else if (w_win_vld) begin
            gnt           <= '0;
            gnt[w_winner] <= 1'b1;
            gnt_id        <= w_winner[$clog2(CLIENTS)-1:0];
            gnt_valid     <= '1;
        end else begin
            gnt       <= '0;
            gnt_id    <= '0;
            gnt_valid <= '0;
        end

endmodule : arbiter_round_robin
