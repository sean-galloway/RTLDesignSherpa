`include "macro_inc.svh"
`timescale 1ns / 1ps

// Paramerized Synchronous FIFO -- This work for non-powers of two depths
// Note: the ports are the same as the AsyncFifo on for ease of instantiation
// Paramerized Synchronous FIFO -- This only works for power of two depths
module sync_fifo#(
        parameter DATA_WIDTH = 8,
        parameter DEPTH = 16
    ) (
    // clocks and resets
    input	wire	            wr_clk, wr_rst_n, rd_clk, rd_rst_n,
    // wr_clk domain
    input	wire	            write,
	input	wire	[DW-1:0]	wr_data,
	output	reg			        wr_full,
    // rd_clk domain
	input	wire			    read,
	output	wire	[DW-1:0]	rd_data,
	output	reg			        rd_empty,
);

	localparam	DW = DATA_WIDTH,
			    D  = DEPTH
                AW = $clog2(DEPTH);

    // local wires
	wire	[AW-1:0]	wr_addr, rd_addr;
	reg	    [AW:0]	    wr_ptr_bin,      rd_ptr_bin;
    wire    [AW:0]      wr_ptr_bin_next, rd_ptr_bin_next;
    wire                wr_rollover,     rd_rollover;
    integer             count;

    // The flop storage
	reg	    [DW-1:0]	mem	[0:((1<<AW)-1)];

    /////////////////////////////////////////////////////////////////////////
    // Count Handling: this isn't actually needed;
    // it is a short cut until I figure out how to get around it.
    count_next =    (read && write)      ? count :
                    (read && ~rd_full)   ? count-1 :
                    (write && ~ wr_full) ? (count+1) : count;
    `DFF_ARN(.d(count), .d(count_next),  .clk(wr_clk) .rst_n(wr_rst_n))

    /////////////////////////////////////////////////////////////////////////
    // Write Domain Logic
    wr_rollover = (D == wr_ptr_bin[AW-1:0]);
    wr_ptr_bin_next =   (write && wr_rollover) ? {{wr_ptr_bin[AW]+1},{AW-1}{1'b0}} :
                        (write && ~wr_full)    ? wr_ptr_bin + 'b1 :
                        wr_ptr_bin;
    `DFF_ARN(.d(wr_ptr_bin),  .d(wr_ptr_bin_next),  .clk(wr_clk), .rst_n(wr_rst_n))

    assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Write to the FIFO on a clock
	always @(posedge wr_clk)
        if ((write)&&(!wr_full))
            mem[wr_addr] <= wr_data;

    // Full logic; this will be an XOR of the extra bit when I get time to validate
`   wr_full = count == D;

    /////////////////////////////////////////////////////////////////////////
    // Read Domain Logic
    rd_rollover = (D == rd_ptr_bin[AW-1:0]);
    rd_ptr_bin_next =   (read && rd_rollover) ? {{rd_ptr_bin[AW]+1},{AW-1}{1'b0}} :
                        (read && ~rd_empty)   ? rd_ptr_bin + 'b1 :
                        rd_ptr_bin;
    `DFF_ARN(.d(rd_ptr_bin),  .d(rd_ptr_bin_next),  .clk(rd_clk), .rst_n(rd_rst_n))

    assign	rd_addr = rd_ptr_bin[AW-1:0];

	// Read from the memory--a clockless read here, clocked by the
	// rd_ptr_bin FLOP
	assign	rd_data = mem[rd_addr];

    // Empty logic; this will be an XOR of the extra bit when I get time to validate
`   rd_empty = count == 0;

endmodule