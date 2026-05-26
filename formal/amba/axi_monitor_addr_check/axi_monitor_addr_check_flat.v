module axi_monitor_addr_check (
	clk,
	aresetn,
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
	addr_pkt_data
);
	reg _sv2v_0;
	parameter signed [31:0] N_ADDR_RANGES = 4;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 6;
	parameter signed [31:0] UNIT_ID = 4'h0;
	parameter signed [31:0] AGENT_ID = 8'h00;
	parameter [0:0] IS_READ = 1'b1;
	parameter signed [31:0] M = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire clk;
	input wire aresetn;
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
	output wire [63:0] addr_pkt_data;
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
	reg [4:0] emit_idx;
	assign emit_any = |r_pending;
	function automatic signed [4:0] sv2v_cast_5_signed;
		input reg signed [4:0] inp;
		sv2v_cast_5_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		emit_oh = 1'sb0;
		emit_idx = 5'h00;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_pending[i] && (emit_oh == {N_ADDR_RANGES {1'sb0}})) begin
					emit_oh[i] = 1'b1;
					emit_idx = sv2v_cast_5_signed(i);
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
	localparam [2:0] PROTOCOL_FIELD = 3'b000;
	localparam [3:0] EVENT_CODE = 4'hd;
	reg [M - 1:0] emit_addr;
	reg [IW - 1:0] emit_id;
	wire [5:0] channel_id_field;
	wire [34:0] event_data_field;
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
	assign channel_id_field = (IW >= 6 ? emit_id[5:0] : {{6 - IW {1'b0}}, emit_id});
	assign event_data_field = {emit_idx[4:0], IS_READ, emit_addr[28:0]};
	function automatic [63:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [2:0] protocol;
		input reg [3:0] event_code;
		input reg [5:0] channel_id;
		input reg [3:0] unit_id;
		input reg [7:0] agent_id;
		input reg [34:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
	endfunction
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(PKT_TYPE_FIELD, PROTOCOL_FIELD, EVENT_CODE, channel_id_field, UNIT_ID[3:0], AGENT_ID[7:0], event_data_field);
	initial _sv2v_0 = 0;
endmodule
