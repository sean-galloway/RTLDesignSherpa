module amber_pending_fill_bypass (
	clk,
	rst_n,
	pf_load,
	pf_load_addr,
	pf_load_state,
	pf_beat_set,
	pf_beat_idx,
	pf_snoop_addr,
	pf_match,
	pf_active,
	pf_addr,
	pf_state,
	pf_data_valid,
	pf_beat_valid,
	pf_clear
);
	localparam signed [31:0] amber_pkg_AMBER_ADDR_WIDTH = 32;
	parameter signed [31:0] ADDR_WIDTH = amber_pkg_AMBER_ADDR_WIDTH;
	localparam signed [31:0] amber_pkg_AMBER_SETS = 128;
	parameter signed [31:0] SETS = amber_pkg_AMBER_SETS;
	localparam signed [31:0] amber_pkg_AMBER_LINE_BYTES = 64;
	parameter signed [31:0] LINE_BYTES = amber_pkg_AMBER_LINE_BYTES;
	localparam signed [31:0] amber_pkg_AMBER_BUS_WIDTH = 64;
	parameter signed [31:0] BUS_WIDTH = amber_pkg_AMBER_BUS_WIDTH;
	localparam signed [31:0] SET_INDEX_WIDTH = $clog2(SETS);
	localparam signed [31:0] LINE_OFFSET_WIDTH = $clog2(LINE_BYTES);
	localparam signed [31:0] STRB_W = BUS_WIDTH / 8;
	localparam signed [31:0] FILL_BEATS = LINE_BYTES / STRB_W;
	localparam signed [31:0] BEAT_INDEX_WIDTH = $clog2(FILL_BEATS);
	localparam signed [31:0] LINE_ADDR_WIDTH = ADDR_WIDTH - LINE_OFFSET_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire pf_load;
	input wire [LINE_ADDR_WIDTH - 1:0] pf_load_addr;
	input wire [2:0] pf_load_state;
	input wire pf_beat_set;
	input wire [BEAT_INDEX_WIDTH - 1:0] pf_beat_idx;
	input wire [LINE_ADDR_WIDTH - 1:0] pf_snoop_addr;
	output wire pf_match;
	output wire pf_active;
	output wire [LINE_ADDR_WIDTH - 1:0] pf_addr;
	output wire [2:0] pf_state;
	output wire [FILL_BEATS - 1:0] pf_data_valid;
	output wire pf_beat_valid;
	input wire pf_clear;
	initial begin
		if ((SETS & (SETS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_pending_fill_bypass/amber_pending_fill_bypass.sv:125:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: SETS must be a power of two");
		if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_pending_fill_bypass/amber_pending_fill_bypass.sv:127:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: LINE_BYTES must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_pending_fill_bypass/amber_pending_fill_bypass.sv:129:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
		if ((BUS_WIDTH % 8) != 0)
			$display("Error [%0t] /tmp/formal_amber_pending_fill_bypass/amber_pending_fill_bypass.sv:131:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: BUS_WIDTH must be a multiple of 8");
	end
	reg pf_active_q;
	reg [LINE_ADDR_WIDTH - 1:0] pf_addr_q;
	reg [2:0] pf_state_q;
	reg [FILL_BEATS - 1:0] pf_data_valid_q;
	assign pf_active = pf_active_q;
	assign pf_addr = pf_addr_q;
	assign pf_state = pf_state_q;
	assign pf_data_valid = pf_data_valid_q;
	assign pf_match = pf_active_q && (pf_snoop_addr == pf_addr_q);
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign pf_beat_valid = pf_data_valid_q[sv2v_cast_32(pf_beat_idx)];
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			pf_active_q <= 1'b0;
			pf_addr_q <= 1'sb0;
			pf_state_q <= 3'b000;
			pf_data_valid_q <= 1'sb0;
		end
		else if (pf_load) begin
			pf_active_q <= 1'b1;
			pf_addr_q <= pf_load_addr;
			pf_state_q <= pf_load_state;
			pf_data_valid_q <= 1'sb0;
		end
		else if (pf_clear)
			pf_active_q <= 1'b0;
		else if (pf_beat_set)
			pf_data_valid_q[sv2v_cast_32(pf_beat_idx)] <= 1'b1;
endmodule
