`timescale 1ns / 1ps
//`include "./glitch_free_n_dff_arn.sv"
// `include "gray2bin.sv"
// `include "bin2gray.sv"

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module async_fifo#(
        parameter DATA_WIDTH       = 8,
        parameter DEPTH            = 16,
        parameter N_FLOP_CROSS     = 2,
        parameter ALMOST_WR_MARGIN = 1,       // TODO: Need to *_next equations for pessimism
        parameter ALMOST_RD_MARGIN = 1        // TODO: Need to *_next equations for pessimism
    ) (
    // clocks and resets
    input	wire	            wr_clk, wr_rst_n, rd_clk, rd_rst_n,
    // wr_clk domain
    input	wire	            write,
	input	wire	[DW-1:0]	wr_data,
	output	reg			        wr_full,
	output  reg                 wr_almost_full,
    // rd_clk domain
	input	wire			    read,
	output	wire	[DW-1:0]	rd_data,
	output	reg			        rd_empty,
	output  reg                 rd_almost_empty
);

	localparam	DW = DATA_WIDTH,
			    D  = DEPTH,
                AW = $clog2(DEPTH),
                N  = N_FLOP_CROSS,
				AL_WR = ALMOST_WR_MARGIN,
				AL_RD = ALMOST_RD_MARGIN,
				ZERO = {AW-1{1'b0}};

    // local wires
	logic	[AW-1:0]	wr_addr, rd_addr;
	logic			    wr_full_next, rd_empty_next;

	logic   [AW:0]	    wr_ptr_gray, wr_ptr_bin, wdom_rd_ptr_gray, wdom_rd_ptr_bin,
				    	rd_ptr_gray, rd_ptr_bin, rdom_wr_ptr_gray, rdom_wr_ptr_bin;
	// local flops
	logic	[AW:0]	    wr_ptr_gray_next, wr_ptr_bin_next;
	logic	[AW:0]	    rd_ptr_gray_next, rd_ptr_bin_next;

    // The flop storage
	logic	[DW-1:0]	mem	[0:((1<<AW)-1)];

    /////////////////////////////////////////////////////////////////////////
    // Write Domain Logic
    /////////////////////////////////////////////////////////////////////////
	// Cross clock domains
	//
	// Cross the Read Gray pointer into the write clock domain
	glitch_free_n_dff_arn # (.FLOP_COUNT (2), .WIDTH (AW+1))
		rd_ptr_gray_cross_inst (.q(wdom_rd_ptr_gray), .d(rd_ptr_gray), .clk(wr_clk), .rst_n(wr_rst_n));

	// convert the gray rd ptr to binary
	gray2bin #(.WIDTH(AW+1)) rd_ptr_gray2bin_inst (.binary(wdom_rd_ptr_bin), .gray(wdom_rd_ptr_gray));

	// Calculate the next write address, and the next graycode pointer.
	assign	wr_ptr_bin_next  = wr_ptr_bin + { {{AW}{1'b0}}, ((write) && (!wr_full)) };

	bin2gray #(.WIDTH(AW+1)) wr_ptr_gray_inst (.binary(wr_ptr_bin_next), .gray(wr_ptr_gray_next));

	assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Register these two values--the address and its Gray code
	// representation
	always @ (posedge wr_clk, negedge wr_rst_n) begin
		if (!wr_rst_n) wr_ptr_bin <= 'b0;
		else           wr_ptr_bin <= wr_ptr_bin_next;
	end

	always @ (posedge wr_clk, negedge wr_rst_n) begin
		if (!wr_rst_n) wr_ptr_gray <= 'b0;
		else           wr_ptr_gray <= wr_ptr_gray_next;
	end

	assign	wr_full        = (wr_ptr_gray == {~wdom_rd_ptr_gray[AW:AW-1], wdom_rd_ptr_gray[AW-2:0]});
	assign	wr_almost_full = 1'b0;

	// Write to the Memory on a clock
	always @(posedge wr_clk)
        if ((write)&&(!wr_full))
            mem[wr_addr] <= wr_data;

    /////////////////////////////////////////////////////////////////////////
    // Read Domain Logic
    /////////////////////////////////////////////////////////////////////////
	// Cross clock domains
	//
	// Cross the Write Gray pointer into the read clock domain
	glitch_free_n_dff_arn #(.FLOP_COUNT(2), .WIDTH(AW+1))
        wr_ptr_gray_cross_inst (.q(rdom_wr_ptr_gray), .d(wr_ptr_gray), .clk(rd_clk), .rst_n(rd_rst_n));

	// convert the gray rd ptr to binary
	gray2bin #(.WIDTH(AW+1)) wr_ptr_gray2bin_inst (.binary(rdom_wr_ptr_bin), .gray(rdom_wr_ptr_gray));

	// Calculate the next read address,
	assign	rd_ptr_bin_next  = rd_ptr_bin + (read & !rd_empty);

	bin2gray #(.WIDTH(AW+1)) rd_ptr_gray_inst (.binary(rd_ptr_bin_next), .gray(rd_ptr_gray_next));

	// Register these two values, the read address and the Gray code version
	// of it, on the next read clock
	always @(posedge rd_clk, negedge rd_rst_n) begin
		if (!rd_rst_n) rd_ptr_bin <= 'b0;
		else           rd_ptr_bin <= rd_ptr_bin_next;
	end

	always @(posedge rd_clk, negedge rd_rst_n) begin
		if (!rd_rst_n) rd_ptr_gray <= 'b0;
		else           rd_ptr_gray <= rd_ptr_gray_next;
	end

	// Memory read address Gray code and pointer calculation
	assign	rd_addr = rd_ptr_bin[AW-1:0];

	// Determine if we'll be empty on the next clock
	assign	rd_empty = (rd_ptr_gray == rdom_wr_ptr_gray); // TODO: Explain why this is different from the full equation
	assign  rd_almost_empty = 1'b0;

	// Read from the memory--a clockless read here, clocked by the next
	// read FLOP in the next processing stage (somewhere else)
	assign	rd_data = mem[rd_addr];

// synopsys translate_off
always @(posedge wr_clk)
begin
    if ((write && wr_full) == 1'b1)
        $display("Error: write while fifo full");
end

always @(posedge rd_clk)
begin
    if ((read && rd_empty) == 1'b1)
        $display("Error: read while fifo empty");
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, async_fifo);
end
// synopsys translate_on

endmodule