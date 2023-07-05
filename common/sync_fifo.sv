`timescale 1ns / 1ps

// Paramerized Synchronous FIFO -- This works for all depths of the FIFO
module sync_fifo#(
        parameter DATA_WIDTH = 4,
        parameter DEPTH = 4
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
                AW = $clog2(DEPTH),
                ZERO = {AW{1'b0}};

    // local wires
	logic	[AW-1:0]	wr_addr, rd_addr;
	logic	[AW:0]	    wr_ptr_bin,      rd_ptr_bin;
    logic   [AW:0]      wr_ptr_bin_next, rd_ptr_bin_next;
    logic               wr_rollover,     rd_rollover, pointer_xor;

    // The flop storage
	logic	    [DW-1:0]	mem	[0:((1<<AW)-1)];

    /////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty eqns
    /////////////////////////////////////////////////////////////////////////
    assign ptr_xor = wr_ptr_bin[AW] ^ rd_ptr_bin[AW];

    /////////////////////////////////////////////////////////////////////////
    // Write Domain Logic
    /////////////////////////////////////////////////////////////////////////
    assign wr_rollover = (D == wr_addr+1);
    assign write_and_rollover = write && !wr_full && wr_rollover;
    assign wr_ptr_bin_next =    (write_and_rollover)  ? {!wr_ptr_bin[AW], ZERO} :
                                (write && !wr_full)   ? wr_ptr_bin + 'b1 :
                                wr_ptr_bin;

    // wr_ptr flops
    always @ (posedge clk, negedge rst_n) begin
        if (!rst_n) wr_ptr_bin <= '0;
        else        wr_ptr_bin <= wr_ptr_bin_next;
    end

    // Get the write address to the memory
    assign	wr_addr = wr_ptr_bin[AW-1:0];

	// Write to the FIFO on a clock
	always @ (posedge clk)
        if ((write)&&(!wr_full))
            mem[wr_addr] <= wr_data;

    // Full logic; this will be an XOR of the extra bit when I get time to validate
    assign wr_full = (ptr_xor && (wr_addr == rd_addr));

    /////////////////////////////////////////////////////////////////////////
    // Read Domain Logic
    /////////////////////////////////////////////////////////////////////////
    assign rd_rollover = (D == rd_addr+1);
    assign read_and_rollover = read && !rd_empty && rd_rollover;
    assign rd_ptr_bin_next =    (read_and_rollover) ? {!rd_ptr_bin[AW], ZERO} :
                                (read && !rd_empty) ? rd_ptr_bin + 'b1 :
                                rd_ptr_bin;
    // rd_ptr flops
    always @ (posedge clk, negedge rst_n) begin
        if (!rst_n) rd_ptr_bin <= '0;
        else        rd_ptr_bin <= rd_ptr_bin_next;
    end

    // get the read address to the memory
    assign rd_addr = rd_ptr_bin[AW-1:0];

    // get the read address to the memory
	assign	rd_data = mem[rd_addr];

    // Empty logic; this will be an XOR of the extra bit when I get time to validate
    assign rd_empty = (!ptr_xor && (rd_addr == wr_addr));

// synopsys translate_off
always @(posedge clk)
begin
    if ((write && wr_full) == 1'b1)
        $display("Error: write while fifo full");
end

always @(posedge clk)
begin
    if ((read && rd_empty) == 1'b1)
        $display("Error: read while fifo empty");
end

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, sync_fifo);
end
// synopsys translate_on
endmodule