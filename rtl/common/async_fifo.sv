`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module async_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16,
    parameter N_FLOP_CROSS = 2,
    parameter ALMOST_WR_MARGIN = 1,
    parameter ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"
)(
    // clocks and resets
    input wire i_wr_clk, i_wr_rst_n, i_rd_clk, i_rd_rst_n,
    // i_wr_clk domain
    input wire i_write,
    input wire [DATA_WIDTH-1:0] i_wr_data,
    output reg ow_wr_full,
    output reg ow_wr_almost_full,
    // i_rd_clk domain
    input wire i_read,
    output wire [DATA_WIDTH-1:0] ow_rd_data,
    output reg ow_rd_empty,
    output reg ow_rd_almost_empty
);

    localparam DW = DATA_WIDTH;
    localparam D = DEPTH;
    localparam AW = $clog2(DEPTH);
    localparam N = N_FLOP_CROSS;
    localparam AFULL = ALMOST_WR_MARGIN;
    localparam AEMPTY = ALMOST_RD_MARGIN;
    localparam AFT = D - AFULL;
    localparam AET = AEMPTY;

	/////////////////////////////////////////////////////////////////////////
    // local wires
    logic [AW-1:0] r_wr_addr, r_rd_addr;

    logic [AW:0]   r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0]   r_wr_ptr_bin,  w_wdom_rd_ptr_bin,  r_rd_ptr_bin,  w_rdom_wr_ptr_bin;

	logic [AW-1:0] w_almost_full_count,  w_almost_empty_count;
    logic          w_wdom_ptr_xor, w_rdom_ptr_xor;

    // The flop storage registers
    logic [DW-1:0] r_mem [0:((1<<AW)-1)];

	/////////////////////////////////////////////////////////////////////////
    // Instantiate the bin and gray counters for write and read pointers
    counter_bingray #(.WIDTH(AW+1)) wr_ptr_counter_gray (
        .i_clk(i_wr_clk), .i_rst_n(i_wr_rst_n), .i_enable(i_write && !ow_wr_full), .o_counter_bin(r_wr_ptr_bin), .o_counter_gray(r_wr_ptr_gray)
    );

    counter_bingray #(.WIDTH(AW+1)) rd_ptr_counter_gray (
        .i_clk(i_rd_clk), .i_rst_n(i_rd_rst_n), .i_enable(i_read && !ow_rd_empty), .o_counter_bin(r_rd_ptr_bin), .o_counter_gray(r_rd_ptr_gray)
    );

	/////////////////////////////////////////////////////////////////////////
	// Instantiate the clock crossing modules
	glitch_free_n_dff_arn #(.FLOP_COUNT (2), .WIDTH (AW+1))
		rd_ptr_gray_cross_inst (.o_q(r_wdom_rd_ptr_gray), .i_d(r_rd_ptr_gray), .i_clk(i_wr_clk), .i_rst_n(i_wr_rst_n));
	
	// convert the gray rd ptr to binary
	gray2bin #(.WIDTH(AW+1)) rd_ptr_gray2bin_inst (.ow_binary(w_wdom_rd_ptr_bin), .i_gray(r_wdom_rd_ptr_gray));

	glitch_free_n_dff_arn #(.FLOP_COUNT(2), .WIDTH(AW+1))
        wr_ptr_gray_cross_inst (.o_q(r_rdom_wr_ptr_gray), .i_d(r_wr_ptr_gray), .i_clk(i_rd_clk), .i_rst_n(i_rd_rst_n));
	
	// convert the gray wr ptr to binary
	gray2bin #(.WIDTH(AW+1)) wr_ptr_gray2bin_inst (.ow_binary(w_rdom_wr_ptr_bin), .i_gray(r_rdom_wr_ptr_gray));

	/////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty equations
    assign w_wdom_ptr_xor = r_wr_ptr_bin[AW] ^ w_wdom_rd_ptr_bin[AW];
    assign w_rdom_ptr_xor = r_rd_ptr_bin[AW] ^ w_rdom_wr_ptr_bin[AW];

	/////////////////////////////////////////////////////////////////////////
	// assign read/write addresses
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

	/////////////////////////////////////////////////////////////////////////
    // Memory Flops
    always_ff @(posedge i_wr_clk) begin
        if (i_write && !ow_wr_full)
            r_mem[r_wr_addr] <= i_wr_data;
    end

	/////////////////////////////////////////////////////////////////////////
    // Read Port
    assign ow_rd_data = r_mem[r_rd_addr];

	/////////////////////////////////////////////////////////////////////////
    // Full and Empty signals
    assign ow_wr_full = (w_wdom_ptr_xor && (r_wr_ptr_bin[AW-1:0] == w_wdom_rd_ptr_bin[AW-1:0]));

    assign ow_rd_empty = (!w_rdom_ptr_xor && (r_rd_ptr_bin[AW-1:0] == w_rdom_wr_ptr_bin[AW-1:0]));

	/////////////////////////////////////////////////////////////////////////
    // Almost Full/Empty logic
    assign w_almost_full_count = (w_wdom_ptr_xor) ?  {(D - w_wdom_rd_ptr_bin[AW-1:0]) - r_wr_ptr_bin[AW-1:0]} : 
                                                        {r_wr_ptr_bin[AW-1:0] - w_wdom_rd_ptr_bin[AW-1:0]};
    assign ow_wr_almost_full = w_almost_full_count >= AFT;

    assign w_almost_empty_count = (w_rdom_ptr_xor) ? {(D - r_rd_ptr_bin[AW-1:0]) - w_rdom_wr_ptr_bin[AW-1:0]} : 
                                                        {w_rdom_wr_ptr_bin[AW-1:0] - r_rd_ptr_bin[AW-1:0]};
    assign ow_rd_almost_empty = (w_almost_empty_count > 0) ? w_almost_empty_count <= AET : 'b0;

	/////////////////////////////////////////////////////////////////////////
    // Error checking and debug stuff
    // synopsys translate_off
    wire [(DW*DEPTH)-1:0] flat_r_mem;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i = i+1)
            begin : flatten_memory
                assign flat_r_mem[i*DW +: DW] = r_mem[i];
            end
    endgenerate

    always @(posedge i_wr_clk) begin
        if (!i_wr_rst_n && (i_write && ow_wr_full) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
    end

    always @(posedge i_rd_clk) begin
        if (!i_wr_rst_n && (i_read && ow_rd_empty) == 1'b1) begin
            $timeformat(-9, 3, " ns", 10); $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, async_fifo);
    end
    // synopsys translate_on

endmodule : async_fifo