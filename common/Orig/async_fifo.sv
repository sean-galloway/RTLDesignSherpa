`include "common/macros_inc.svh"
`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for powers of two depths
module AsyncFifo#(
        parameter DATA_WIDTH = 8,
        parameter DEPTH = 16,
        parameter N_FLOP_CROSS = 2
    ) (
    // clocks and resets
    input	wire	            i_wclk, i_wrst_n, i_rclk, i_rrst_n,
    // i_wclk domain
    input	wire	            i_wr,
	input	wire	[DW-1:0]	i_wdata,
	output	reg			        o_wfull,
    // i_rclk domain
	input	wire			    i_rd,
	output	wire	[DW-1:0]	o_rdata,
	output	reg			        o_rempty,
);

	localparam	DW = DATA_WIDTH,
			    D  = DEPTH
                AW = $clog2(DEPTH),
                N  = N_FLOP_CROSS;

    // local wires
	wire	[AW-1:0]	wr_addr, rd_addr;
	wire			    wr_full_next, rd_empty_next;

    // These flops won't be necessary if I switch to using my own n-clock crossing macro
	reg	    [AW:0]	    wr_ptr_gray, wr_ptr_bin, wq2_rd_ptr_gray, wq1_rd_ptr_gray,
				        rd_ptr_gray, rd_ptr_bin, rq2_wr_ptr_gray, rq1_wr_ptr_gray;
	// local flops
	wire	[AW:0]		wr_ptr_gray_next, wr_ptr_bin_next;
	wire	[AW:0]		rd_ptr_gray_next, rd_ptr_bin_next;

    // The flop storage
	reg	    [DW-1:0]	mem	[0:((1<<AW)-1)];

	//
	// Cross clock domains
	//
	// Cross the read Gray pointer into the write clock domain
	// initial	{ wq2_rd_ptr_gray,  wq1_rd_ptr_gray } = 0; // not synthesizeable
    `GLITCH_FREE_N_DFF_ARN(wq2_rd_ptr_gray, rd_ptr_gray, i_wclk, i_wrst_n, N)
	// always @(posedge i_wclk or negedge i_wrst_n)
	// if (!i_wrst_n)
	// 	{ wq2_rd_ptr_gray, wq1_rd_ptr_gray } <= 0;
	// else
	// 	{ wq2_rd_ptr_gray, wq1_rd_ptr_gray } <= { wq1_rd_ptr_gray, rd_ptr_gray };

	// Calculate the next write address, and the next graycode pointer.
	assign	wr_ptr_bin_next  = wr_ptr_bin + { {(AW){1'b0}}, ((i_wr) && (!o_wfull)) };
	assign	wr_ptr_gray_next = (wr_ptr_bin_next >> 1) ^ wr_ptr_bin_next;

	assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Register these two values--the address and its Gray code
	// representation
	// initial	{ wr_ptr_bin, wr_ptr_gray } = 0; // not synthsizeable
    `DFF_ARN(wr_ptr_bin,  wr_ptr_bin_next,  i_wclk, i_wrst_n)
    `DFF_ARN(wr_ptr_gray, wr_ptr_gray_next, i_wclk, i_wrst_n)
	// always @(posedge i_wclk or negedge i_wrst_n)
	// if (!i_wrst_n)
	// 	{ wr_ptr_bin, wr_ptr_gray } <= 0;
	// else
	// 	{ wr_ptr_bin, wr_ptr_gray } <= { wr_ptr_bin_next, wr_ptr_gray_next };

	assign	wr_full_next = (wr_ptr_gray_next == { ~wq2_rd_ptr_gray[AW:AW-1], wq2_rd_ptr_gray[AW-2:0] });

	//
	// Calculate whether or not the register will be full on the next
	// clock.
	initial	o_wfull = 0; // not synthesizeable
    `DFF_ARN(o_wfull, wr_full_next, i_wclk, i_wrst_n)
	// always @(posedge i_wclk or negedge i_wrst_n)
	// if (!i_wrst_n)
	// 	o_wfull <= 1'b0;
	// else
	// 	o_wfull <= wr_full_next;

	//
	// Write to the FIFO on a clock
	always @(posedge i_wclk)
	if ((i_wr)&&(!o_wfull))
		mem[wr_addr] <= i_wdata;

	//
	// Cross clock domains
	//
	// Cross the write Gray pointer into the read clock domain
	// initial	{ rq2_wr_ptr_gray,  rq1_wr_ptr_gray } = 0; // not synthesizable
    `GLITCH_FREE_N_DFF_ARN( rq2_wr_ptr_gray, wr_ptr_gray, i_rclk, i_rrst_n, N)
	// always @(posedge i_rclk or negedge i_rrst_n)
	// if (!i_rrst_n)
	// 	{ rq2_wr_ptr_gray, rq1_wr_ptr_gray } <= 0;
	// else
	// 	{ rq2_wr_ptr_gray, rq1_wr_ptr_gray } <= { rq1_wr_ptr_gray, wr_ptr_gray };

	// Calculate the next read address,
	assign	rd_ptr_bin_next  = rd_ptr_bin + { {(AW){1'b0}}, ((i_rd)&&(!o_rempty)) };
	// and the next Gray code version associated with it
	assign	rd_ptr_gray_next = (rd_ptr_bin_next >> 1) ^ rd_ptr_bin_next;

	// Register these two values, the read address and the Gray code version
	// of it, on the next read clock
	//
	// initial	{ rd_ptr_bin, rd_ptr_gray } = 0;// not synthesizeable
    `DFF_ARN(rd_ptr_bin,  rd_ptr_bin_next,  i_rclk, i_rrst_n)
    `DFF_ARN(rd_ptr_gray, rd_ptr_gray_next, i_rclk, i_rrst_n)
	// always @(posedge i_rclk or negedge i_rrst_n)
	// if (!i_rrst_n)
	// 	{ rd_ptr_bin, rd_ptr_gray } <= 0;
	// else
	// 	{ rd_ptr_bin, rd_ptr_gray } <= { rd_ptr_bin_next, rd_ptr_gray_next };

	// Memory read address Gray code and pointer calculation
	assign	rd_addr = rd_ptr_bin[AW-1:0];

	// Determine if we'll be empty on the next clock
	assign	rd_empty_next = (rd_ptr_gray_next == rq2_wr_ptr_gray);

    `DFF_ARN(o_rempty, rd_empty_next, i_rclk, i_rrst_n)
	// initial o_rempty = 1;
	// always @(posedge i_rclk or negedge i_rrst_n)
	// if (!i_rrst_n)
	// 	o_rempty <= 1'b1;
	// else
	// 	o_rempty <= rd_empty_next;

	//
	// Read from the memory--a clockless read here, clocked by the next
	// read FLOP in the next processing stage (somewhere else)
	//
	assign	o_rdata = mem[rd_addr];

endmodule

