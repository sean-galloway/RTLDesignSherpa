// axi_fifo_sync_multi.sv: Wrapper for multi-signal FIFO (synchronous)
module gaxi_fifo_sync_multi #(
    parameter integer ADDR_WIDTH = 4,
    parameter integer CTRL_WIDTH = 4,
    parameter integer DATA_WIDTH = 8,
    parameter integer DEPTH = 2,
    parameter integer AW = ADDR_WIDTH,
    parameter integer CW = CTRL_WIDTH,
    parameter integer DW = DATA_WIDTH
)(
    input  logic                i_axi_aclk,
    input  logic                i_axi_aresetn,
    // Write channel
    input  logic                i_wr_valid,
    output logic                o_wr_ready,
    input  logic [AW-1:0]       i_wr_addr,
    input  logic [CW-1:0]       i_wr_ctrl,
    input  logic [DW-1:0]       i_wr_data0,
    input  logic [DW-1:0]       i_wr_data1,
    // Read channel
    output logic                o_rd_valid,
    input  logic                i_rd_ready,
    output logic [AW-1:0]       o_rd_addr,
    output logic [CW-1:0]       o_rd_ctrl,
    output logic [DW-1:0]       o_rd_data0,
    output logic [DW-1:0]       o_rd_data1
);

    // Instantiate the original FIFO
    gaxi_fifo_sync #(
        .DATA_WIDTH(AW+CW+DW+DW),
        .DEPTH(DEPTH)
    ) u_dut (
        .i_axi_aclk    (i_axi_aclk),
        .i_axi_aresetn (i_axi_aresetn),
        .i_wr_valid    (i_wr_valid),
        .o_wr_ready    (o_wr_ready),
        .i_wr_data     ({i_wr_addr, i_wr_ctrl, i_wr_data1, i_wr_data0}),
        .o_rd_valid    (o_rd_valid),
        .i_rd_ready    (i_rd_ready),
        .o_rd_data     ({o_rd_addr,   o_rd_ctrl,  o_rd_data1,  o_rd_data0}),
        .ow_count      ()
    );

endmodule : gaxi_fifo_sync_multi
