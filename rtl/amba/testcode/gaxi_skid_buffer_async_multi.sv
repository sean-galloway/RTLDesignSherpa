`timescale 1ns / 1ps

// AXI Skid buffer where all ports are driven or received by a flop
module gaxi_skid_buffer_async_multi #(
    parameter integer ADDR_WIDTH = 4,
    parameter integer CTRL_WIDTH = 4,
    parameter integer DATA_WIDTH = 8,
    parameter integer DEPTH         = 2,
    parameter integer N_FLOP_CROSS  = 2,
    parameter         INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter integer AW = ADDR_WIDTH,
    parameter integer CW = CTRL_WIDTH,
    parameter integer DW = DATA_WIDTH
) (
    // Global Clock and Reset
    input  logic          i_axi_wr_aclk,
    input  logic          i_axi_wr_aresetn,
    input  logic          i_axi_rd_aclk,
    input  logic          i_axi_rd_aresetn,

    // input side
    input  logic          i_wr_valid,
    output logic          wr_ready,
    input  logic [AW-1:0] i_wr_addr,
    input  logic [CW-1:0] i_wr_ctrl,
    input  logic [DW-1:0] i_wr_data0,
    input  logic [DW-1:0] i_wr_data1,

    // output side
    output logic          rd_valid,
    input  logic          i_rd_ready,
    output logic [AW-1:0] rd_addr,
    output logic [CW-1:0] rd_ctrl,
    output logic [DW-1:0] rd_data0,
    output logic [DW-1:0] rd_data1,
    output logic [AW-1:0] rd_addr,
    output logic [CW-1:0] rd_ctrl,
    output logic [DW-1:0] rd_data0,
    output logic [DW-1:0] rd_data1
);

    logic                 r_xfer_valid;
    logic                 r_xfer_ready;

    // Instantiate the axi_skid_buffer module
    gaxi_skid_buffer #(
        .DATA_WIDTH(AW+CW+DW+DW)
    ) inst_gaxi_skid_buffer (
        .i_axi_aclk   (i_axi_wr_aclk),
        .i_axi_aresetn(i_axi_wr_aresetn),
        .i_wr_valid   (i_wr_valid),
        .wr_ready   (wr_ready),
        .i_wr_data    ({i_wr_addr, i_wr_ctrl, i_wr_data1, i_wr_data0}),
        .rd_valid   (r_xfer_valid),
        .i_rd_ready   (r_xfer_ready),
        .rd_data    (r_xfer_data),
        .count     (),
        .rd_count   ()

    );

    // Instantiate the axi_fifo_async module
    gaxi_fifo_async #(
        .DATA_WIDTH(AW+CW+DW+DW),
        .DEPTH(DEPTH),
        .N_FLOP_CROSS(N_FLOP_CROSS),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) inst_gaxi_fifo_async (
        .i_axi_wr_aclk   (i_axi_wr_aclk),
        .i_axi_wr_aresetn(i_axi_wr_aresetn),
        .i_axi_rd_aclk   (i_axi_rd_aclk),
        .i_axi_rd_aresetn(i_axi_rd_aresetn),
        .i_wr_valid      (r_xfer_valid),
        .wr_ready      (r_xfer_ready),
        .i_wr_data       (r_xfer_data),
        .i_rd_ready      (i_rd_ready),
        .rd_valid      (rd_valid),
        .rd_data        ({rd_addr, rd_ctrl, rd_data1, rd_data0}),
        .rd_data         ({rd_addr,   rd_ctrl,  rd_data1,  rd_data0})
    );

endmodule : gaxi_skid_buffer_async_multi
