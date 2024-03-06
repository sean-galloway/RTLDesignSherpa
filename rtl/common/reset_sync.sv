`timescale 1ns / 1ps

// Paramerized Reset Synchronizer
module reset_sync #(
    parameter int N_FLOP_CROSS = 3
) (
    // clocks and resets
    input  logic i_clk,
    i_rst_n,
    output logic o_sync_rst_n
);

    /////////////////////////////////////////////////////////////////////////
    // Instantiate the clock crossing modules
    glitch_free_n_dff_arn #(
        .FLOP_COUNT(N_FLOP_CROSS),
        .WIDTH(1)
    ) rd_ptr_gray_cross_inst (
        .o_q(o_sync_rst_n),
        .i_d(1'b1),
        .i_clk(i_clk),
        .i_rst_n(i_rst_n)
    );

endmodule : reset_sync
