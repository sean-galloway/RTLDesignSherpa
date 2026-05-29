module axi_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_addr,
	cmd_id,
	cmd_valid,
	cmd_ready,
	cfg_addr_check_enable,
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
	input wire [N_ADDR_RANGES - 1:0] cfg_addr_range_enable;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_low;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_high;
	output wire addr_pkt_valid;
	input wire addr_pkt_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] addr_pkt_data;
	output wire [63:0] addr_pkt_timestamp;
	wire cmd_fire;
	reg [N_ADDR_RANGES - 1:0] hit_oh;
	assign cmd_fire = (cmd_valid && cmd_ready) && cfg_addr_check_enable;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				hit_oh[i] = ((cfg_addr_range_enable[i] && cmd_fire) && (cmd_addr >= cfg_addr_range_low[i * M+:M])) && (cmd_addr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_lat_addr;
	reg [(N_ADDR_RANGES * IW) - 1:0] r_lat_id;
	reg [N_ADDR_RANGES - 1:0] emit_oh;
	wire emit_any;
	reg [3:0] emit_idx;
	assign emit_any = |r_pending;
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		emit_oh = 1'sb0;
		emit_idx = 4'h0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_pending[i] && (emit_oh == {N_ADDR_RANGES {1'sb0}})) begin
					emit_oh[i] = 1'b1;
					emit_idx = sv2v_cast_4_signed(i);
				end
		end
	end
	assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
	wire accept;
	assign accept = addr_pkt_valid && addr_pkt_ready;
	always @(posedge clk)
		if (!aresetn) begin
			r_pending <= 1'sb0;
			r_lat_addr <= 1'sb0;
			r_lat_id <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i]) begin
						r_lat_addr[i * M+:M] <= cmd_addr;
						r_lat_id[i * IW+:IW] <= cmd_id;
					end
			end
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i])
						r_pending[i] <= 1'b1;
					else if (accept && emit_oh[i])
						r_pending[i] <= 1'b0;
			end
		end
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] PKT_TYPE_FIELD = monitor_common_pkg_PktTypeError;
	localparam [3:0] PROTOCOL_FIELD = 4'h0;
	localparam [7:0] EVENT_CODE = 8'h0d;
	reg [M - 1:0] emit_addr;
	reg [IW - 1:0] emit_id;
	wire [8:0] channel_id_field;
	wire [63:0] event_data_field;
	wire [59:0] addr_payload;
	always @(*) begin
		if (_sv2v_0)
			;
		emit_addr = 1'sb0;
		emit_id = 1'sb0;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (emit_oh[i]) begin
					emit_addr = r_lat_addr[i * M+:M];
					emit_id = r_lat_id[i * IW+:IW];
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
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(PKT_TYPE_FIELD, PROTOCOL_FIELD, EVENT_CODE, channel_id_field, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
	initial _sv2v_0 = 0;
endmodule
