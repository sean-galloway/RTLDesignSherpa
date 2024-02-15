`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module fifo_control #(
    parameter int DEL = 1,
    parameter int ADDR_WIDTH = 3,
    parameter int DEPTH = 16,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic        i_wr_clk,
    i_wr_rst_n,
    i_rd_clk,
    i_rd_rst_n,
    // Pointers
    input  logic [AW:0] iw_wr_ptr_bin,
    input  logic [AW:0] iw_wdom_rd_ptr_bin,
    input  logic [AW:0] iw_rd_ptr_bin,
    input  logic [AW:0] iw_rdom_wr_ptr_bin,
    output logic        o_wr_full,
    output logic        o_wr_almost_full,
    output logic        o_rd_empty,
    output logic        o_rd_almost_empty
);

    localparam int D = DEPTH;
    localparam int AW = ADDR_WIDTH;
    localparam int AFULL = ALMOST_WR_MARGIN;
    localparam int AEMPTY = ALMOST_RD_MARGIN;
    localparam int AFT = D - AFULL;
    localparam int AET = AEMPTY;

    logic w_ptr_xor;
    logic w_wr_full_d, w_wr_almost_full_d;
    logic w_rd_empty_d, w_rd_almost_empty_d;
    logic [AW-1:0] w_almost_full_count, w_almost_empty_count;

    /////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty equations
    assign #DEL w_wdom_ptr_xor = iw_wr_ptr_bin[AW] ^ iw_wdom_rd_ptr_bin[AW];
    assign #DEL w_rdom_ptr_xor = iw_rd_ptr_bin[AW] ^ iw_rdom_wr_ptr_bin[AW];

    /////////////////////////////////////////////////////////////////////////
    // Full signals
    assign w_wr_full_d = (w_wdom_ptr_xor && (iw_wr_ptr_bin[AW-1:0] == iw_wdom_rd_ptr_bin[AW-1:0]));
    assign w_almost_full_count = (w_wdom_ptr_xor) ?
                        {(D - iw_wdom_rd_ptr_bin[AW-1:0]) - iw_wr_ptr_bin[AW-1:0]} :
                        {iw_wr_ptr_bin[AW-1:0] - iw_wdom_rd_ptr_bin[AW-1:0]};
    assign w_wr_almost_full_d = w_almost_full_count >= AFT;

    always_ff @(posedge i_wr_clk, negedge i_wr_rst_n) begin
        if (!i_wr_rst_n) begin
            o_wr_full <= 'b0;
            o_wr_almost_full <= 'b0;
        end else begin
            o_wr_full <= w_wr_full_d;
            o_wr_almost_full <= w_wr_almost_full_d;
        end
    end

    /////////////////////////////////////////////////////////////////////////
    // Empty Signals
    assign w_rd_empty_d = (!w_rdom_ptr_xor &&
                            (iw_rd_ptr_bin[AW-1:0] == iw_rdom_wr_ptr_bin[AW-1:0]));
    assign w_almost_empty_count = (w_rdom_ptr_xor) ?
                        {(D - iw_rd_ptr_bin[AW-1:0]) - iw_rdom_wr_ptr_bin[AW-1:0]} :
                        {iw_rdom_wr_ptr_bin[AW-1:0] - iw_rd_ptr_bin[AW-1:0]};
    assign w_rd_almost_empty_d = (w_almost_empty_count > 0) ? w_almost_empty_count <= AET : 'b0;

    always_ff @(posedge i_rd_clk, negedge i_rd_rst_n) begin
        if (!i_rd_rst_n) begin
            o_rd_empty <= 'b0;
            o_rd_almost_empty <= 'b0;
        end else begin
            o_rd_empty <= w_rd_empty_d;
            o_rd_almost_empty <= w_rd_almost_empty_d;
        end
    end
endmodule : fifo_control
