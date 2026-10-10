module amber_victim (
	clk,
	rst_n,
	victim_load,
	victim_addr_in,
	victim_data_in,
	victim_clear,
	victim_busy,
	victim_empty,
	victim_valid,
	victim_addr,
	victim_data
);
	localparam signed [31:0] amber_pkg_AMBER_ADDR_WIDTH = 32;
	parameter signed [31:0] ADDR_WIDTH = amber_pkg_AMBER_ADDR_WIDTH;
	localparam signed [31:0] amber_pkg_AMBER_SETS = 128;
	parameter signed [31:0] SETS = amber_pkg_AMBER_SETS;
	localparam signed [31:0] amber_pkg_AMBER_LINE_BYTES = 64;
	parameter signed [31:0] LINE_BYTES = amber_pkg_AMBER_LINE_BYTES;
	localparam signed [31:0] amber_pkg_AMBER_BUS_WIDTH = 64;
	parameter signed [31:0] BUS_WIDTH = amber_pkg_AMBER_BUS_WIDTH;
	localparam signed [31:0] LINE_OFFSET_WIDTH = $clog2(LINE_BYTES);
	localparam signed [31:0] STRB_W = BUS_WIDTH / 8;
	localparam signed [31:0] FILL_BEATS = LINE_BYTES / STRB_W;
	localparam signed [31:0] LINE_WIDTH = LINE_BYTES * 8;
	input wire clk;
	input wire rst_n;
	input wire victim_load;
	input wire [ADDR_WIDTH - 1:0] victim_addr_in;
	input wire [LINE_WIDTH - 1:0] victim_data_in;
	input wire victim_clear;
	output wire victim_busy;
	output wire victim_empty;
	output wire victim_valid;
	output wire [ADDR_WIDTH - 1:0] victim_addr;
	output wire [LINE_WIDTH - 1:0] victim_data;
	initial begin
		if ((SETS & (SETS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_victim/amber_victim.sv:124:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: SETS must be a power of two");
		if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_victim/amber_victim.sv:126:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: LINE_BYTES must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_victim/amber_victim.sv:128:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
		if ((BUS_WIDTH % 8) != 0)
			$display("Error [%0t] /tmp/formal_amber_victim/amber_victim.sv:130:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: BUS_WIDTH must be a multiple of 8");
	end
	reg victim_valid_q;
	reg [ADDR_WIDTH - 1:0] victim_addr_q;
	reg [LINE_WIDTH - 1:0] victim_data_q;
	assign victim_valid = victim_valid_q;
	assign victim_busy = victim_valid_q;
	assign victim_empty = !victim_valid_q;
	assign victim_addr = victim_addr_q;
	assign victim_data = victim_data_q;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			victim_valid_q <= 1'b0;
			victim_addr_q <= 1'sb0;
			victim_data_q <= 1'sb0;
		end
		else if (victim_clear)
			victim_valid_q <= 1'b0;
		else if (victim_load && !victim_valid_q) begin
			victim_valid_q <= 1'b1;
			victim_addr_q <= victim_addr_in;
			victim_data_q <= victim_data_in;
		end
endmodule
