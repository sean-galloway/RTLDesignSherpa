`include "common/macros_inc.svh"
`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module async_fifo#(
        parameter DATA_WIDTH = 8,
        parameter DEPTH = 16,
        parameter N_FLOP_CROSS = 2,
        parameter ALMOST = 1        // TODO: Need to *_next equations for pessimism
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
                AW = $clog2(DEPTH),
                N  = N_FLOP_CROSS;

    // local wires
	wire	[AW-1:0]	wr_addr, rd_addr;
	wire			    wr_full_next, rd_empty_next;

	reg	    [AW:0]	    wr_ptr_gray, wr_ptr_bin, wq2_rd_ptr_gray,
				        rd_ptr_gray, rd_ptr_bin, rq2_wr_ptr_gray;
	// local flops
	wire	[AW:0]		wr_ptr_gray_next, wr_ptr_bin_next;
	wire	[AW:0]		rd_ptr_gray_next, rd_ptr_bin_next;

    // The flop storage
	reg	    [DW-1:0]	mem	[0:((1<<AW)-1)];


    /////////////////////////////////////////////////////////////////////////
    // Write Domain Logic
    /////////////////////////////////////////////////////////////////////////
	// Cross clock domains
	//
	// Cross the Read Gray pointer into the write clock domain
    `GLITCH_FREE_N_DFF_ARN(wq2_rd_ptr_gray, rd_ptr_gray, wr_clk, wr_rst_n, N)

	// Calculate the next write address, and the next graycode pointer.
	assign	wr_ptr_bin_next  = wr_ptr_bin + { {(AW){1'b0}}, ((write) && (!wr_full)) };
	assign	wr_ptr_gray_next = (wr_ptr_bin_next >> 1) ^ wr_ptr_bin_next;

	assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Register these two values--the address and its Gray code
	// representation
    `DFF_ARN(wr_ptr_bin,  wr_ptr_bin_next,  wr_clk, wr_rst_n)
    `DFF_ARN(wr_ptr_gray, wr_ptr_gray_next, wr_clk, wr_rst_n)

	assign	wr_full_next = (wr_ptr_gray_next == { ~wq2_rd_ptr_gray[AW:AW-1], wq2_rd_ptr_gray[AW-2:0] });

	// Calculate whether or not the register will be full on the next clock.
    `DFF_ARN(wr_full, wr_full_next, wr_clk, wr_rst_n)

	// Write to the FIFO on a clock
	always @(posedge wr_clk)
        if ((write)&&(!wr_full))
            mem[wr_addr] <= wr_data;

    /////////////////////////////////////////////////////////////////////////
    // Read Domain Logic
    /////////////////////////////////////////////////////////////////////////
	// Cross clock domains
	//
	// Cross the Write Gray pointer into the read clock domain
    `GLITCH_FREE_N_DFF_ARN( rq2_wr_ptr_gray, wr_ptr_gray, rd_clk, rd_rst_n, N)

	// Calculate the next read address,
	assign	rd_ptr_bin_next  = rd_ptr_bin + { {(AW){1'b0}}, ((read)&&(!rd_empty)) };
	// and the next Gray code version associated with it
	assign	rd_ptr_gray_next = (rd_ptr_bin_next >> 1) ^ rd_ptr_bin_next;

	// Register these two values, the read address and the Gray code version
	// of it, on the next read clock
    `DFF_ARN(rd_ptr_bin,  rd_ptr_bin_next,  rd_clk, rd_rst_n)
    `DFF_ARN(rd_ptr_gray, rd_ptr_gray_next, rd_clk, rd_rst_n)

	// Memory read address Gray code and pointer calculation
	assign	rd_addr = rd_ptr_bin[AW-1:0];

	// Determine if we'll be empty on the next clock
	assign	rd_empty_next = (rd_ptr_gray_next == rq2_wr_ptr_gray); // TODO: Explain why this is different from the full equation

    `DFF_ARN(rd_empty, rd_empty_next, rd_clk, rd_rst_n)

	// Read from the memory--a clockless read here, clocked by the next
	// read FLOP in the next processing stage (somewhere else)
	assign	rd_data = mem[rd_addr];

endmodule