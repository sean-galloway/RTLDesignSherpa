`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync_multi #(
    parameter int DEL = 1,
    parameter int ADDR_WIDTH = 4,
    parameter int CTRL_WIDTH = 4,
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int AW = ADDR_WIDTH,
    parameter int CW = CTRL_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH
) (
    input  logic                  i_clk,
                                i_rst_n,
    input  logic                  i_write,
    input  logic [AW-1:0]         i_wr_addr,
    input  logic [CW-1:0]         i_wr_ctrl,
    input  logic [DW-1:0]         i_wr_data0,
    input  logic [DW-1:0]         i_wr_data1,

    output logic                  o_wr_full,
    output logic                  o_wr_almost_full,
    input  logic                  i_read,
    output logic [AW-1:0]         o_rd_addr,
    output logic [CW-1:0]         o_rd_ctrl,
    output logic [DW-1:0]         o_rd_data0,
    output logic [DW-1:0]         o_rd_data1,
    output logic [AW-1:0]         ow_rd_addr,
    output logic [CW-1:0]         ow_rd_ctrl,
    output logic [DW-1:0]         ow_rd_data0,
    output logic [DW-1:0]         ow_rd_data1,
    output logic                  o_rd_empty,
    output logic                  o_rd_almost_empty
);

    fifo_sync #(
        .DEL               (1),
        .DATA_WIDTH        (AW+CW+DW+DW),
        .DEPTH             (DEPTH),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .INSTANCE_NAME     ("fifo_multi")
    ) u_fifo_sync (
        // Clocks & Reset
        .i_clk              (i_clk),
        .i_rst_n            (i_rst_n),

        // Write side
        .i_write            (i_write),
        .i_wr_data          ({i_wr_addr, i_wr_ctrl, i_wr_data1, i_wr_data0}),
        .o_wr_full          (o_wr_full),
        .o_wr_almost_full   (o_wr_almost_full),

        // Read side
        .i_read             (i_read),
        .ow_rd_data         ({ow_rd_addr, ow_rd_ctrl, ow_rd_data1, ow_rd_data0}),
        .o_rd_data          ({o_rd_addr,   o_rd_ctrl,  o_rd_data1,  o_rd_data0}),
        .o_rd_empty         (o_rd_empty),
        .o_rd_almost_empty  (o_rd_almost_empty)
    );

endmodule : fifo_sync_multi
