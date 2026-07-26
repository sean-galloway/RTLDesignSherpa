module axi_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_addr,
	cmd_id,
	cmd_valid,
	cmd_ready,
	cfg_addr_check_enable,
	cfg_debug_enable,
	cfg_error_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	addr_pkt_valid,
	addr_pkt_ready,
	addr_pkt_data,
	addr_pkt_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] N_ADDR_RANGES = 4;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 6;
	parameter [7:0] UNIT_ID = 8'h00;
	parameter [15:0] AGENT_ID = 16'h0000;
	parameter [0:0] IS_READ = 1'b1;
	parameter signed [31:0] M = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire clk;
	input wire aresetn;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [M - 1:0] cmd_addr;
	input wire [IW - 1:0] cmd_id;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cfg_addr_check_enable;
	input wire cfg_debug_enable;
	input wire cfg_error_enable;
	input wire [N_ADDR_RANGES - 1:0] cfg_addr_range_enable;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_low;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_high;
	output wire addr_pkt_valid;
	input wire addr_pkt_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] addr_pkt_data;
	output wire [63:0] addr_pkt_timestamp;
	wire cmd_fire;
	reg [N_ADDR_RANGES - 1:0] raw_hit;
	wire any_hit;
	assign cmd_fire = (cmd_valid && cmd_ready) && cfg_addr_check_enable;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				raw_hit[i] = (cfg_addr_range_enable[i] && (cmd_addr >= cfg_addr_range_low[i * M+:M])) && (cmd_addr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	assign any_hit = |raw_hit;
	reg [N_ADDR_RANGES - 1:0] match_set;
	wire miss_set;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				match_set[i] = (cmd_fire && cfg_debug_enable) && raw_hit[i];
		end
	end
	assign miss_set = (cmd_fire && cfg_error_enable) && !any_hit;
	reg [N_ADDR_RANGES - 1:0] r_match_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_match_addr;
	reg [(N_ADDR_RANGES * IW) - 1:0] r_match_id;
	reg r_miss_pending;
	reg [M - 1:0] r_miss_addr;
	reg [IW - 1:0] r_miss_id;
	reg [N_ADDR_RANGES - 1:0] match_emit_oh;
	wire match_emit_any;
	reg [3:0] match_emit_idx;
	assign match_emit_any = |r_match_pending;
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		match_emit_oh = 1'sb0;
		match_emit_idx = 4'h0;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_match_pending[i] && (match_emit_oh == {N_ADDR_RANGES {1'sb0}})) begin
					match_emit_oh[i] = 1'b1;
					match_emit_idx = sv2v_cast_4_signed(i);
				end
		end
	end
	wire emit_is_miss;
	assign emit_is_miss = r_miss_pending;
	assign addr_pkt_valid = (r_miss_pending || match_emit_any) && cfg_addr_check_enable;
	wire accept;
	assign accept = addr_pkt_valid && addr_pkt_ready;
	always @(posedge clk)
		if (!aresetn) begin
			r_match_pending <= 1'sb0;
			r_match_addr <= 1'sb0;
			r_match_id <= 1'sb0;
			r_miss_pending <= 1'b0;
			r_miss_addr <= 1'sb0;
			r_miss_id <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (match_set[i]) begin
						r_match_addr[i * M+:M] <= cmd_addr;
						r_match_id[i * IW+:IW] <= cmd_id;
					end
			end
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (match_set[i])
						r_match_pending[i] <= 1'b1;
					else if ((accept && !emit_is_miss) && match_emit_oh[i])
						r_match_pending[i] <= 1'b0;
			end
			if (miss_set) begin
				r_miss_addr <= cmd_addr;
				r_miss_id <= cmd_id;
			end
			if (miss_set)
				r_miss_pending <= 1'b1;
			else if (accept && emit_is_miss)
				r_miss_pending <= 1'b0;
		end
	localparam [3:0] MISS_RANGE_SENTINEL = 4'hf;
	reg [3:0] pkt_type_field;
	reg [7:0] event_code_field;
	reg [3:0] emit_idx;
	reg [M - 1:0] emit_addr;
	reg [IW - 1:0] emit_id;
	wire [8:0] channel_id_field;
	wire [63:0] event_data_field;
	wire [59:0] addr_payload;
	localparam [3:0] monitor_common_pkg_PktTypeAddrMatch = 4'h8;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	always @(*) begin
		if (_sv2v_0)
			;
		if (emit_is_miss) begin
			pkt_type_field = monitor_common_pkg_PktTypeError;
			event_code_field = 8'h0d;
			emit_idx = MISS_RANGE_SENTINEL;
			emit_addr = r_miss_addr;
			emit_id = r_miss_id;
		end
		else begin
			pkt_type_field = monitor_common_pkg_PktTypeAddrMatch;
			event_code_field = 8'h01;
			emit_idx = match_emit_idx;
			emit_addr = 1'sb0;
			emit_id = 1'sb0;
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (match_emit_oh[i]) begin
						emit_addr = r_match_addr[i * M+:M];
						emit_id = r_match_id[i * IW+:IW];
					end
			end
		end
	end
	generate
		if (IW >= 9) begin : g_chan_id_wide
			assign channel_id_field = emit_id[8:0];
		end
		else begin : g_chan_id_narrow
			assign channel_id_field = {{9 - IW {1'b0}}, emit_id};
		end
		if (M >= 60) begin : g_addr_wide
			assign addr_payload = emit_addr[59:0];
		end
		else begin : g_addr_narrow
			assign addr_payload = {{60 - M {1'b0}}, emit_addr};
		end
	endgenerate
	assign event_data_field = {emit_idx[3:0], addr_payload};
	function automatic [127:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [3:0] protocol;
		input reg [7:0] event_code;
		input reg [8:0] channel_id;
		input reg [7:0] unit_id;
		input reg [15:0] agent_id;
		input reg [63:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, 15'h0000, protocol, event_code, channel_id, agent_id, unit_id, event_data};
	endfunction
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(pkt_type_field, 4'h0, event_code_field, channel_id_field, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
	initial _sv2v_0 = 0;
endmodule
