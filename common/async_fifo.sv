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
			    D = DEPTH
                AW = $clog2(DEPTH),
                N = N_FLOP_CROSS;

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
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		{ wq2_rd_ptr_gray, wq1_rd_ptr_gray } <= 0;
	else
		{ wq2_rd_ptr_gray, wq1_rd_ptr_gray } <= { wq1_rd_ptr_gray, rd_ptr_gray };

	// Calculate the next write address, and the next graycode pointer.
	assign	wr_ptr_bin_next  = wr_ptr_bin + { {(AW){1'b0}}, ((i_wr) && (!o_wfull)) };
	assign	wr_ptr_gray_next = (wr_ptr_bin_next >> 1) ^ wr_ptr_bin_next;

	assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Register these two values--the address and its Gray code
	// representation
	initial	{ wr_ptr_bin, wr_ptr_gray } = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		{ wr_ptr_bin, wr_ptr_gray } <= 0;
	else
		{ wr_ptr_bin, wr_ptr_gray } <= { wr_ptr_bin_next, wr_ptr_gray_next };

	assign	wr_full_next = (wr_ptr_gray_next == { ~wq2_rd_ptr_gray[AW:AW-1], wq2_rd_ptr_gray[AW-2:0] });

	//
	// Calculate whether or not the register will be full on the next
	// clock.
	initial	o_wfull = 0;
	always @(posedge i_wclk or negedge i_wrst_n)
	if (!i_wrst_n)
		o_wfull <= 1'b0;
	else
		o_wfull <= wr_full_next;

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
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		{ rq2_wr_ptr_gray, rq1_wr_ptr_gray } <= 0;
	else
		{ rq2_wr_ptr_gray, rq1_wr_ptr_gray } <= { rq1_wr_ptr_gray, wr_ptr_gray };

	// Calculate the next read address,
	assign	rd_ptr_bin_next  = rd_ptr_bin + { {(AW){1'b0}}, ((i_rd)&&(!o_rempty)) };
	// and the next Gray code version associated with it
	assign	rd_ptr_gray_next = (rd_ptr_bin_next >> 1) ^ rd_ptr_bin_next;

	// Register these two values, the read address and the Gray code version
	// of it, on the next read clock
	//
	initial	{ rd_ptr_bin, rd_ptr_gray } = 0;
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		{ rd_ptr_bin, rd_ptr_gray } <= 0;
	else
		{ rd_ptr_bin, rd_ptr_gray } <= { rd_ptr_bin_next, rd_ptr_gray_next };

	// Memory read address Gray code and pointer calculation
	assign	rd_addr = rd_ptr_bin[AW-1:0];

	// Determine if we'll be empty on the next clock
	assign	rd_empty_next = (rd_ptr_gray_next == rq2_wr_ptr_gray);

	initial o_rempty = 1;
	always @(posedge i_rclk or negedge i_rrst_n)
	if (!i_rrst_n)
		o_rempty <= 1'b1;
	else
		o_rempty <= rd_empty_next;

	//
	// Read from the memory--a clockless read here, clocked by the next
	// read FLOP in the next processing stage (somewhere else)
	//
	assign	o_rdata = mem[rd_addr];

endmodule
// module AsyncFifo #(
//     parameter DATA_WIDTH = 8,
//     parameter DEPTH = 16,
//     parameter N_FLOP_CROSS = 2
//     ) (
//     input wire  clk_wr,
//     input wire  clk_rd,
//     input wire  rst_n,
//     // clk_wr domain
//     input wire  wr_en,
//     input wire  [DATA_WIDTH-1:0] data_in,
//     output wire full,
//     // clk_rd domain
//     input wire  rd_en,
//     output wire [DATA_WIDTH-1:0] data_out,
//     output wire empty
//     );

//     parameter ADDR_WIDTH = $clog2(DEPTH);
//     parameter FLOP_COUNT = (N_FLOP_CROSS <= 1) ? 1 : N;

//     reg  [DATA_WIDTH-1:0] fifo_data_reg [0:DEPTH-1];
//     reg  [ADDR_WIDTH-1:0] wr_ptr_bin;
//     reg  [ADDR_WIDTH-1:0] rd_ptr_bin;
//     reg  [ADDR_WIDTH-1:0] wr_ptr_gray;
//     reg  [ADDR_WIDTH-1:0] rd_ptr_gray;
//     wire [ADDR_WIDTH-1:0] wr_ptr_gray_next;
//     wire [ADDR_WIDTH-1:0] wr_ptr_gray_next;
//     reg  [ADDR_WIDTH-1:0] valid_count;
//     reg  empty_reg;
//     reg  full_reg;
//     wire empty_next;
//     wire full_next;

//     assign = data_out <= fifo_data_reg[rd_ptr_bin];

//     assign wr_ptr_gray_next = wr_ptr_bin ^ {1'b0, wr_ptr_bin[ADDR_WIDTH-1:1]};
//     GLITCH_FREEN_DFF_ARN #(FLOP_COUNT) wr_ptr_gray_flop (
//         .clk_in(clk_rd),
//         .rst_n(rst_n),
//         .d(wr_ptr_gray_next),
//         .q(wr_ptr_gray)
//     );

//     assign rd_ptr_gray_next = rd_ptr_bin ^ {1'b0, rd_ptr_bin[ADDR_WIDTH-1:1]};
//     GLITCH_FREEN_DFF_ARN #(FLOP_COUNT) rd_ptr_gray_flop (
//         .clk_in(clk_wr),
//         .rst_n(rst_n),
//         .d(rd_ptr_gray_next),
//         .q(rd_ptr_gray)
//     );

//     always @(posedge clk_wr or posedge rst_n) begin
//         if (rst_n) begin
//             empty_reg <= 1'b1;
//             full_reg <= 1'b0;
//             wr_ptr_bin <= 0;
//             wr_ptr_gray <= 0;
//             valid_count <= 0;
//         end else begin
//         empty_reg <= empty_next;
//         full_reg <= full_next;
//         if (wr_en && ~full_reg) begin
//             fifo_data_reg[wr_ptr_bin] <= data_in;
//             wr_ptr_bin <= (wr_ptr_bin + 1'b1) % DEPTH;
//             valid_count <= valid_count + 1'b1;
//         end
//         end
//     end

//     always @(posedge clk_rd or posedge rst_n) begin
//         if (rst_n) begin
//         rd_ptr_bin <= 0;
//         rd_ptr_gray <= 0;
//         valid_count <= 0;
//         end else begin
//         if (rd_en && ~empty_reg) begin
//             rd_ptr_bin <= (rd_ptr_bin + 1'b1) % DEPTH;
//             rd_ptr_gray <= rd_ptr_bin ^ {1'b0, rd_ptr_bin[ADDR_WIDTH-1:1]};
//             valid_count <= valid_count - 1'b1;
//         end
//         end
//     end

//     assign empty = (valid_count == 0);
//     assign full = (valid_count == DEPTH);

//     assign empty_next = (wr_ptr_gray == rd_ptr_gray) ? ~wr_en : empty_reg;
//     assign full_next = ((wr_ptr_gray + 1'b1) % DEPTH == rd_ptr_gray) ? wr_en : full_reg;

// endmodule

