`timescale 1ns / 1ps

// AXI Skid buffer where all ports are driven or received by a flop
module axi_skid_buffer_async #(
    parameter int DATA_WIDTH    = 32,
    parameter int DEPTH         = 2,
    parameter int N_FLOP_CROSS  = 2,
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DW = DATA_WIDTH
) (
    // Global Clock and Reset
    input  logic          i_axi_wr_aclk,
    input  logic          i_axi_wr_aresetn,
    input  logic          i_axi_rd_aclk,
    input  logic          i_axi_rd_aresetn,

    // input side
    input  logic          i_wr_valid,
    output logic          o_wr_ready,
    input  logic [DW-1:0] i_wr_data,

    // output side
    output logic          o_rd_valid,
    input  logic          i_rd_ready,
    output logic [DW-1:0] o_rd_data
);

    logic           r_xfer_valid;
    logic           r_xfer_ready;
    logic [DW-1:0]  r_xfer_data;

    // Instantiate the axi_skid_buffer module
    axi_skid_buffer #(
        .DATA_WIDTH(DW)
    ) inst_skid_buffer (
        .i_axi_aclk   (i_axi_wr_aclk),
        .i_axi_aresetn(i_axi_wr_aresetn),
        .i_wr_valid   (i_wr_valid),
        .o_wr_ready   (o_wr_ready),
        .i_wr_data    (i_wr_data),
        .o_rd_valid   (r_xfer_valid),
        .i_rd_ready   (r_xfer_ready),
        .o_rd_data    (r_xfer_data)
    );

    // Instantiate the axi_fifo_async module
    axi_fifo_async #(
        .DEL(1),
        .DATA_WIDTH(DW),
        .DEPTH(DEPTH),
        .N_FLOP_CROSS(N_FLOP_CROSS),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) inst_axi_fifo_async (
        .i_axi_wr_aclk   (i_axi_wr_aclk),
        .i_axi_wr_aresetn(i_axi_wr_aresetn),
        .i_axi_rd_aclk   (i_axi_rd_aclk),
        .i_axi_rd_aresetn(i_axi_rd_aresetn),
        .i_wr_valid      (r_xfer_valid),
        .o_wr_ready      (r_xfer_ready),
        .i_wr_data       (r_xfer_data),
        .i_rd_ready      (i_rd_ready),
        .o_rd_valid      (o_rd_valid),
        .ow_rd_data      (o_rd_data),
        .o_rd_data       ()
    );

endmodule : axi_skid_buffer_async
