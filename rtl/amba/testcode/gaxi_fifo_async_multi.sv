`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This works for any even depth
module gaxi_fifo_async_multi #(
    parameter int ADDR_WIDTH = 4,
    parameter int CTRL_WIDTH = 4,
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 10,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int AW = ADDR_WIDTH,
    parameter int CW = CTRL_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH,
    parameter int PAW = $clog2(DEPTH),
    parameter int JCW = D,  // Johnson Counter Width
    parameter int N = N_FLOP_CROSS
) (
    // clocks and resets
    input  logic            i_axi_wr_aclk,
                            i_axi_wr_aresetn,
                            i_axi_rd_aclk,
                            i_axi_rd_aresetn,
    input  logic            i_wr_valid,
    output logic            wr_ready,   // not full
    input  logic [AW-1:0]   i_wr_addr,
    input  logic [CW-1:0]   i_wr_ctrl,
    input  logic [DW-1:0]   i_wr_data0,
    input  logic [DW-1:0]   i_wr_data1,
    input  logic            i_rd_ready,
    output logic            rd_valid,   // not empty
    output logic [AW-1:0]   rd_addr,
    output logic [CW-1:0]   rd_ctrl,
    output logic [DW-1:0]   rd_data0,
    output logic [DW-1:0]   rd_data1,
    output logic [AW-1:0]   rd_addr,
    output logic [CW-1:0]   rd_ctrl,
    output logic [DW-1:0]   rd_data0,
    output logic [DW-1:0]   rd_data1
    );


    gaxi_fifo_async #(
        .DATA_WIDTH        (8),                // Data width
        .DEPTH             (10),               // FIFO depth
        .N_FLOP_CROSS      (2),                // Number of flop crossings
        .ALMOST_WR_MARGIN  (1),                // Almost write margin
        .ALMOST_RD_MARGIN  (1),                // Almost read margin
        .INSTANCE_NAME     ("DEADF1F0"),       // Instance name
        .DW                (AW+CW+DW+DW),       // Data width alias
        .D                 (DEPTH),            // Depth alias
        .AW                ($clog2(DEPTH)),    // Address width
        .JCW               (D),                // Johnson Counter Width
        .N                 (N_FLOP_CROSS)      // N flop cross alias
    ) u_gaxi_fifo_async (
        // Clocks and resets
        .i_axi_wr_aclk     (i_axi_wr_aclk),    // Write clock
        .i_axi_wr_aresetn  (i_axi_wr_aresetn), // Write reset (active low)
        .i_axi_rd_aclk     (i_axi_rd_aclk),    // Read clock
        .i_axi_rd_aresetn  (i_axi_rd_aresetn), // Read reset (active low)

        // Write interface
        .i_wr_valid        (i_wr_valid),       // Write valid signal
        .wr_ready        (wr_ready),       // Write ready (not full)
        .i_wr_data         ({i_wr_addr, i_wr_ctrl, i_wr_data1, i_wr_data0}),        // Write data

        // Read interface
        .i_rd_ready        (i_rd_ready),       // Read ready signal
        .rd_valid        (rd_valid),       // Read valid (not empty)
        .rd_data        ({rd_addr, rd_ctrl, rd_data1, rd_data0}),
        .rd_data         ({rd_addr,   rd_ctrl,  rd_data1,  rd_data0})
    );


endmodule : gaxi_fifo_async_multi
