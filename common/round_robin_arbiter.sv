`timescale 1ns / 1ps

// Mostly based on code from this github:
// https://github.com/gsw73/ffs_arbiter/blob/master/design.sv
// I made a couple of tweaks myself to make it more efficient if only one agent is requesting
module round_robin_arbiter #(parameter CLIENTS=16)
    (
        input  logic               clk,
        input  logic               rst_n,

        input  logic [CLIENTS-1:0] req,
        output logic [CLIENTS-1:0] gnt
    );

    // =======================================================================
    // Declarations & Parameters
    localparam  N = $clog2(CLIENTS);

    logic [CLIENTS-1:0] mask;
    logic [CLIENTS-1:0] win_mask_only;
    logic [N-1:0] req_location;
    logic [N-1:0] reqm_location;
    logic vld_ffs_req;
    logic vld_ffs_reqm;

    logic [N-1:0] req_location_sg;
    logic [N-1:0] reqm_location_sg;
    logic vld_ffs_req_sg;
    logic vld_ffs_reqm_sg;

    logic [CLIENTS-1:0] req_masked;
    logic [CLIENTS-1:0] req_win_mask;

    logic [N-1:0] winner;
    logic win_vld;

    // =======================================================================
    // Logic

    assign req_masked = req & mask;
    assign req_win_mask = ($countones(req) > 1) ? (req & win_mask_only) : req;  // only look at the req's if there is only one

    // find first set bit in both request and masked request; priority shifts
    // down the bit vector, but returns to the to of the bit vector when no
    // lower bits are set

    assign {vld_ffs_req, req_location} = ffs(req_win_mask);
    assign {vld_ffs_reqm, reqm_location} = ffs(req_masked);

    leading_one_trailing_one 
    #(.WIDTH (N))
    u_req_leading_one_trailing_one(
    	.data               (req_win_mask),
        .leadingone         (),
        .leadingone_vector  (req_location_sg),
        .trailingone        (),
        .trailingone_vector (),
        .all_zeroes         (),
        .valid              (vld_ffs_req_sg)
    );

    leading_one_trailing_one 
    #(.WIDTH (N))
    u_reqm_leading_one_trailing_one(
    	.data               (req_masked),
        .leadingone         (),
        .leadingone_vector  (reqm_location_sg),
        .trailingone        (),
        .trailingone_vector (),
        .all_zeroes         (),
        .valid              (vld_ffs_reqm_sg)
    );
    

    // determine the winner--either the masked version (because a lower-priority
    // request was set) or the unmasked version (because we started over from
    // the top)
    always_comb begin
        if (vld_ffs_reqm)
            begin
                winner = reqm_location;
                win_vld = 1'b1;
            end
        else if (vld_ffs_req)
            begin
                winner = req_location;
                win_vld = 1'b1;
            end
        else
            begin
                winner = 16'd0;
                win_vld = 1'b0;
            end
    end

    // Register:  win_mask_only
    //
    // When considering the upper part of the vector for the start-over
    // case, we still need to mask off the bit that just won so we don't
    // grant to it twice in a row.
    always_ff @(posedge clk, negedge rst_n)
        if (!rst_n)
            win_mask_only <= '0;
        else if (win_vld)
            win_mask_only <= ~({(CLIENTS-1)'('d0), 1'b1} << winner);
        else
            win_mask_only <= {CLIENTS{1'b1}};

    // Register:  mask
    //
    // The mask depends on the previous winner.
    always_ff @(posedge clk, negedge rst_n)
        if (!rst_n)
            mask <= '0;
        else
            mask <= ({(CLIENTS-1)'('d0), 1'b1} << winner)-1'b1;

    // Register:  gnt
    //
    // Priority is given to lower bits i.e., those getting a gnt when using
    // the mask vector.  If no lower bits are set, the unmasked request result
    // is used.
    always_ff @(posedge clk, negedge rst_n)
        if (!rst_n)
            gnt <= '0;
        else if (win_vld)
            begin
                gnt <= '0;
                gnt[winner] <= 1'b1;
            end
        else
            gnt <= '0;

    // =======================================================================
    // Function

    // Function:  ffs
    // TODO: replace with leading one/trailing one module.
    // Returns the first set bit starting with the most-significant bit.
    // Format for return is { vld, location[ 15:0 ] }

    function automatic logic [16:0] ffs(input logic [CLIENTS-1:0] vector);
        logic vld;
        logic [15:0] location;

        vld = 1'b0;
        location = 16'hffff;

        for (int i = 0; i < CLIENTS; i++)
            if (vector[i] == 1'b1)
                begin
                    vld = 1'b1;
                    location = i[15:0];
                end

        return {vld, location};
    endfunction

endmodule : round_robin_arbiter
