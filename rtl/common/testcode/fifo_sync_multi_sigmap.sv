`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync_multi_sigmap #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
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
    input  logic                    clk,
                                    rst_n,
    input  logic                    write,
    input  logic [AW-1:0]           wr_siga,
    input  logic [CW-1:0]           wr_sigb,
    input  logic [DW-1:0]           wr_sigc,
    input  logic [DW-1:0]           wr_sigd,

    output logic                    wr_full,
    output logic                    wr_almost_full,
    input  logic                    read,
    output logic [AW-1:0]           rd_sige,
    output logic [CW-1:0]           rd_sigf,
    output logic [DW-1:0]           rd_sigg,
    output logic [DW-1:0]           rd_sigh,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    fifo_sync #(
        .REGISTERED        (REGISTERED),
        .DATA_WIDTH        (AW+CW+DW+DW),
        .DEPTH             (DEPTH),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .INSTANCE_NAME     ("fifo_multi")
    ) u_fifo_sync (
        // Clocks & Reset
        .i_clk              (clk),
        .i_rst_n            (rst_n),

        // Write side
        .i_write            (write),
        .i_wr_data          ({wr_siga, wr_sigb, wr_sigd, wr_sigc}),
        .o_wr_full          (wr_full),
        .o_wr_almost_full   (wr_almost_full),

        // Read side
        .i_read             (read),
        .o_rd_data          ({rd_sige,  rd_sigf,  rd_sigh,  rd_sigg}),
        .o_rd_empty         (rd_empty),
        .o_rd_almost_empty  (rd_almost_empty)
    );

endmodule : fifo_sync_multi_sigmap
