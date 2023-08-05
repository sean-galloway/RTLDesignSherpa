`timescale 1ns / 1ps

module sync_fifo#(
        parameter DATA_WIDTH = 4,
        parameter DEPTH = 4,
        parameter ALMOST_WR_MARGIN = 1,
        parameter ALMOST_RD_MARGIN = 1,
        parameter INSTANCE_NAME = "DEADF1F0"
    ) (
    input wire i_clk, i_rst_n,
    input wire i_write,
    input wire [DATA_WIDTH-1:0] i_wr_data,
    output reg ow_wr_full,
    output reg ow_wr_almost_full,
    input wire i_read,
    output wire [DATA_WIDTH-1:0] ow_rd_data,
    output reg ow_rd_empty,
    output reg ow_rd_almost_empty
);

    localparam DW = DATA_WIDTH;
    localparam D = DEPTH;
    localparam AW = $clog2(DEPTH);
    localparam AFULL = ALMOST_WR_MARGIN;
    localparam AEMPTY = ALMOST_RD_MARGIN;
    localparam AFT = D - AFULL;
    localparam AET = AEMPTY;

	/////////////////////////////////////////////////////////////////////////
    // local wires/register signals
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic          w_ptr_xor;
    logic [AW-1:0] w_almost_full_count, almost_empty_count;

    // The flop storage
    logic [DW-1:0] r_mem [0:((1<<AW)-1)];

	/////////////////////////////////////////////////////////////////////////
    // Write counter
    counter_bin #(.WIDTH(AW+1), .MAX(D)) write_counter (
        .i_clk(i_clk), .i_rst_n(i_rst_n), .i_enable(i_write && !ow_wr_full), .o_counter_out(r_wr_ptr_bin)
    );

	/////////////////////////////////////////////////////////////////////////
    // Read counter
    counter_bin #(.WIDTH(AW+1), .MAX(D)) read_counter (
        .i_clk(i_clk), .i_rst_n(i_rst_n), .i_enable(i_read && !ow_rd_empty), .o_counter_out(r_rd_ptr_bin)
    );

	/////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty equations
    assign w_ptr_xor = r_wr_ptr_bin[AW] ^ r_rd_ptr_bin[AW];

	/////////////////////////////////////////////////////////////////////////
    // Get the write/read address to the memory
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

	/////////////////////////////////////////////////////////////////////////
    // Write to the FIFO on a clock
    always @ (posedge i_clk)
        if (i_write && !ow_wr_full)
            r_mem[r_wr_addr] <= i_wr_data;

	/////////////////////////////////////////////////////////////////////////
    // Full logic
    assign ow_wr_full = (w_ptr_xor && (r_wr_addr == r_rd_addr));

	/////////////////////////////////////////////////////////////////////////
    // Almost full logic
    assign w_almost_full_count = (w_ptr_xor) ?  {(D - r_rd_ptr_bin[AW-1:0]) - r_wr_ptr_bin[AW-1:0]} : 
                                                {r_wr_ptr_bin[AW-1:0] - r_rd_ptr_bin[AW-1:0]};
    assign ow_wr_almost_full = w_almost_full_count >= AFT;

	/////////////////////////////////////////////////////////////////////////
    // Empty logic
    assign ow_rd_empty = (!w_ptr_xor && (r_rd_addr == r_wr_addr));

	/////////////////////////////////////////////////////////////////////////
    // Almost empty logic
    assign w_almost_empty_count = (w_ptr_xor) ? {(D - r_rd_ptr_bin[AW-1:0]) - r_wr_ptr_bin[AW-1:0]} : 
                                                {r_wr_ptr_bin[AW-1:0] - r_rd_ptr_bin[AW-1:0]};
    assign ow_rd_almost_empty = (w_almost_empty_count > 0) ? w_almost_empty_count <= AET : 'b0;

	/////////////////////////////////////////////////////////////////////////
    // Read data
    assign ow_rd_data = r_mem[r_rd_addr];

endmodule : sync_fifo
