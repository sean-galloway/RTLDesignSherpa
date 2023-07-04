`include "macros_inc.svh"
`timescale 1ns / 1ps

// Paramerized Synchronous FIFO -- This works for all depths of the FIFO
module sync_fifo#(
        parameter DATA_WIDTH = 8,
        parameter DEPTH = 16
    ) (
    // clocks and resets
    input	wire	            clk, rst_n,
    // clk domain
    input	wire	            write,
	input	wire	[DW-1:0]	wr_data,
	output	reg			        wr_full,
    // clk domain
	input	wire			    read,
	output	wire	[DW-1:0]	rd_data,
	output	reg			        rd_empty
);

	localparam	DW = DATA_WIDTH,
			    D  = DEPTH,
                AW = $clog2(DEPTH)+1,
                AWp1 = AW+1;

    // local wires
	wire	[AW-1:0]	wr_addr, rd_addr;
	reg	    [AW:0]	    wr_ptr_bin,      rd_ptr_bin;
    wire    [AW:0]      wr_ptr_bin_next, rd_ptr_bin_next;
    wire                wr_rollover,     rd_rollover, pointer_xor;
    integer             count;

    // The flop storage
	reg	    [DW-1:0]	mem	[0:((1<<AW)-1)];

    /////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty eqns
    assign ptr_xor = write_ptr_bin[AW] ^ read_ptr_bin[AW];

    /////////////////////////////////////////////////////////////////////////
    // Write Domain Logic
    assign wr_rollover =        (D == wr_ptr_bin[AW-1:0]);
    assign wr_ptr_bin_next = wr_ptr_bin;
    // assign wr_ptr_bin_next =    (write && ~wr_full && wr_rollover) ? {{wr_ptr_bin[AW]+1},{AW-1}{1'b0}} :
    //                             (write && ~wr_full)                ? wr_ptr_bin + 'b1 :
    //                             wr_ptr_bin;
    // `DFF_ARN #(WIDTH=AWp1) wr_ptr_flop (.q(wr_ptr_bin), .d(wr_ptr_bin_next), .clk(clk), .rst_n(rst_n));

    assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Write to the FIFO on a clock
	always @(posedge clk)
        if ((write)&&(!wr_full))
            mem[wr_addr] <= wr_data;

    // Full logic; this will be an XOR of the extra bit when I get time to validate
    // assign wr_full = (ptr_xor && (wr_addr == read_addr));

    // Read Domain Logic

    /////////////////////////////////////////////////////////////////////////
    // Read Domain Logic
    assign rd_rollover =        (D == rd_ptr_bin[AW-1:0]);
    assign rd_ptr_bin_next = rd_ptr_bin;
    // assign rd_ptr_bin_next =    (read && ~rd_empty && rd_rollover) ? {{rd_ptr_bin[AW]+1},{AW-1}{1'b0}} :
    //                             (read && ~rd_empty)                ? rd_ptr_bin + 'b1 :
    //                             rd_ptr_bin;
    // `DFF_ARN #(WIDTH=AWp1) rd_ptr_flop (.q(rd_ptr_bin), .d(rd_ptr_bin_next), .clk(clk), .rst_n(rst_n));

    assign rd_addr = rd_ptr_bin[AW-1:0];

	assign	rd_data = mem[rd_addr];

    // Empty logic; this will be an XOR of the extra bit when I get time to validate
    assign rd_empty = (~ptr_xor && (rd_addr == write_addr));

endmodule