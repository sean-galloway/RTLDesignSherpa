`timescale 1ns / 1ps

// Mostly based on code from this github:
// https://github.com/gsw73/ffs_arbiter/blob/master/design.sv
// I made a couple of tweaks myself to make it more efficient if only one agent is requesting
module arbiter_round_robin #(
    parameter int CLIENTS = 4
) (
    input logic i_clk,
    input logic i_rst_n,
    input logic i_block_arb,

    input  logic [CLIENTS-1:0] i_req,
    output logic [CLIENTS-1:0] o_gnt
);

    // =======================================================================
    // Declarations & Parameters
    localparam int N = $clog2(CLIENTS) + 1;

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
    assign w_req_post = (i_block_arb) ? 'b0 : i_req;
    assign w_req_masked = w_req_post & r_mask;
    assign w_req_win_mask = ($countones(
            i_req
        ) > 1) ? (w_req_post & r_win_mask_only) :
            w_req_post;  // only look at the req's if there is only one

    // find highest set bit in both request and masked request; priority shifts
    // down the bit vector, but returns to the top of the bit vector when no
    // lower bits are set
    // NOTE: due to the way the arb colde below is structured, it will always start at the highest bit and work its way down.
    leading_one_trailing_one #(
        .WIDTH(CLIENTS)
    ) u_req_leading_one_trailing_one (
        .i_data               (w_req_win_mask),
        .ow_leadingone        (),
        .ow_leadingone_vector (),
        .ow_trailingone       (w_req_location),
        .ow_trailingone_vector(),
        .ow_all_zeroes        (),
        .ow_valid             (w_vld_ffs_req)
    );

    leading_one_trailing_one #(
        .WIDTH(CLIENTS)
    ) u_reqm_leading_one_trailing_one (
        .i_data               (w_req_masked),
        .ow_leadingone        (),
        .ow_leadingone_vector (),
        .ow_trailingone       (w_reqm_location),
        .ow_trailingone_vector(),
        .ow_all_zeroes        (),
        .ow_valid             (w_vld_ffs_reqm)
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
    always_ff @(posedge i_clk or negedge i_rst_n)
        if (!i_rst_n) r_win_mask_only <= '0;
        else if (w_win_vld) r_win_mask_only <= ~({(CLIENTS - 1)'('d0), 1'b1} << w_winner);
        else r_win_mask_only <= {CLIENTS{1'b1}};

    // Register:  r_mask
    //
    // The r_mask depends on the previous winner.
    always_ff @(posedge i_clk or negedge i_rst_n)
        if (!i_rst_n) r_mask <= '0;
        else r_mask <= ({(CLIENTS - 1)'('d0), 1'b1} << w_winner) - 1'b1;

    // Register:  o_gnt
    //
    // Priority is given to lower bits i.e., those getting a o_gnt when using
    // the mask vector.  If no lower bits are set, the unmasked request result
    // is used.
    always_ff @(posedge i_clk or negedge i_rst_n)
        if (!i_rst_n) o_gnt <= '0;
        else if (w_win_vld) begin
            o_gnt <= '0;
            o_gnt[w_winner] <= 1'b1;
        end else o_gnt <= '0;

endmodule : arbiter_round_robin
