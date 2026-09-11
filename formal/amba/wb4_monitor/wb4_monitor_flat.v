module apb_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_paddr,
	cmd_pwrite,
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
	parameter [7:0] UNIT_ID = 8'h00;
	parameter [15:0] AGENT_ID = 16'h0000;
	parameter [3:0] PROTOCOL = 4'h2;
	parameter signed [31:0] M = ADDR_WIDTH;
	input wire clk;
	input wire aresetn;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [M - 1:0] cmd_paddr;
	input wire cmd_pwrite;
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
				hit_oh[i] = ((cfg_addr_range_enable[i] && cmd_fire) && (cmd_paddr >= cfg_addr_range_low[i * M+:M])) && (cmd_paddr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_lat_addr;
	reg [N_ADDR_RANGES - 1:0] r_lat_is_read;
	wire [N_ADDR_RANGES - 1:0] emit_oh;
	wire emit_any;
	reg [3:0] emit_idx;
	assign emit_any = |r_pending;
	reg [N_ADDR_RANGES - 1:0] w_emit_pick;
	always @(*) begin
		if (_sv2v_0)
			;
		w_emit_pick = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_pending[i] && (w_emit_pick == {N_ADDR_RANGES {1'sb0}}))
					w_emit_pick[i] = 1'b1;
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_emit_hold;
	reg r_emit_held;
	assign emit_oh = (r_emit_held ? r_emit_hold : w_emit_pick);
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		emit_idx = 4'h0;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (emit_oh[i])
					emit_idx = sv2v_cast_4_signed(i);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_shadow_valid;
	reg [(N_ADDR_RANGES * M) - 1:0] r_shadow_addr;
	reg [N_ADDR_RANGES - 1:0] r_shadow_is_read;
	assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
	wire accept;
	assign accept = addr_pkt_valid && addr_pkt_ready;
	reg [N_ADDR_RANGES - 1:0] w_presented;
	reg [N_ADDR_RANGES - 1:0] w_range_accept;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				begin
					w_presented[i] = addr_pkt_valid && emit_oh[i];
					w_range_accept[i] = accept && emit_oh[i];
				end
		end
	end
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			r_pending <= 1'sb0;
			r_lat_addr <= 1'sb0;
			r_lat_is_read <= 1'sb0;
			r_shadow_valid <= 1'sb0;
			r_shadow_addr <= 1'sb0;
			r_shadow_is_read <= 1'sb0;
			r_emit_hold <= 1'sb0;
			r_emit_held <= 1'b0;
		end
		else begin
			if (accept)
				r_emit_held <= 1'b0;
			else if (addr_pkt_valid && !addr_pkt_ready) begin
				r_emit_held <= 1'b1;
				r_emit_hold <= emit_oh;
			end
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (w_range_accept[i]) begin
						if (hit_oh[i]) begin
							r_lat_addr[i * M+:M] <= cmd_paddr;
							r_lat_is_read[i] <= !cmd_pwrite;
						end
						else if (r_shadow_valid[i]) begin
							r_lat_addr[i * M+:M] <= r_shadow_addr[i * M+:M];
							r_lat_is_read[i] <= r_shadow_is_read[i];
						end
					end
					else if (hit_oh[i] && !w_presented[i]) begin
						r_lat_addr[i * M+:M] <= cmd_paddr;
						r_lat_is_read[i] <= !cmd_pwrite;
					end
			end
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (w_range_accept[i])
						r_shadow_valid[i] <= 1'b0;
					else if (hit_oh[i] && w_presented[i]) begin
						r_shadow_valid[i] <= 1'b1;
						r_shadow_addr[i * M+:M] <= cmd_paddr;
						r_shadow_is_read[i] <= !cmd_pwrite;
					end
			end
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i])
						r_pending[i] <= 1'b1;
					else if (w_range_accept[i] && !r_shadow_valid[i])
						r_pending[i] <= 1'b0;
			end
		end
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] PKT_TYPE_FIELD = monitor_common_pkg_PktTypeError;
	localparam [3:0] PROTOCOL_FIELD = PROTOCOL;
	localparam [7:0] EVENT_CODE = 8'h08;
	reg [M - 1:0] emit_addr;
	reg emit_is_read;
	wire [63:0] event_data_field;
	wire [58:0] addr_payload;
	always @(*) begin
		if (_sv2v_0)
			;
		emit_addr = 1'sb0;
		emit_is_read = 1'b0;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (emit_oh[i]) begin
					emit_addr = r_lat_addr[i * M+:M];
					emit_is_read = r_lat_is_read[i];
				end
		end
	end
	generate
		if (M >= 59) begin : g_addr_wide
			assign addr_payload = emit_addr[58:0];
		end
		else begin : g_addr_narrow
			assign addr_payload = {{59 - M {1'b0}}, emit_addr};
		end
	endgenerate
	assign event_data_field = {emit_idx[3:0], emit_is_read, addr_payload};
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
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(PKT_TYPE_FIELD, PROTOCOL_FIELD, EVENT_CODE, 9'h000, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
	initial _sv2v_0 = 0;
endmodule
module counter_bin (
	clk,
	rst_n,
	enable,
	counter_bin_curr,
	counter_bin_next
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 5;
	parameter signed [31:0] MAX = 10;
	input wire clk;
	input wire rst_n;
	input wire enable;
	output reg [WIDTH - 1:0] counter_bin_curr;
	output reg [WIDTH - 1:0] counter_bin_next;
	wire [WIDTH - 2:0] w_max_val;
	function automatic signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] sv2v_cast_00F62_signed;
		input reg signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] inp;
		sv2v_cast_00F62_signed = inp;
	endfunction
	assign w_max_val = sv2v_cast_00F62_signed(MAX - 1);
	always @(*) begin
		if (_sv2v_0)
			;
		if (enable) begin
			if (counter_bin_curr[WIDTH - 2:0] == w_max_val)
				counter_bin_next = {~counter_bin_curr[WIDTH - 1], {WIDTH - 1 {1'b0}}};
			else
				counter_bin_next = counter_bin_curr + 1;
		end
		else
			counter_bin_next = counter_bin_curr;
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			counter_bin_curr <= 'b0;
		else
			counter_bin_curr <= counter_bin_next;
	initial _sv2v_0 = 0;
endmodule
module fifo_control (
	wr_clk,
	wr_rst_n,
	rd_clk,
	rd_rst_n,
	wr_ptr_bin,
	wdom_rd_ptr_bin,
	rd_ptr_bin,
	rdom_wr_ptr_bin,
	count,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] ADDR_WIDTH = 3;
	parameter signed [31:0] DEPTH = 8;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 0;
	input wire wr_clk;
	input wire wr_rst_n;
	input wire rd_clk;
	input wire rd_rst_n;
	input wire [ADDR_WIDTH:0] wr_ptr_bin;
	input wire [ADDR_WIDTH:0] wdom_rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rdom_wr_ptr_bin;
	output wire [ADDR_WIDTH:0] count;
	output reg wr_full;
	output reg wr_almost_full;
	output reg rd_empty;
	output reg rd_almost_empty;
	localparam signed [31:0] D = DEPTH;
	localparam signed [31:0] AW = ADDR_WIDTH;
	localparam signed [31:0] AFULL = ALMOST_WR_MARGIN;
	localparam signed [31:0] AEMPTY = ALMOST_RD_MARGIN;
	localparam signed [31:0] AFT = D - AFULL;
	localparam signed [31:0] AET = AEMPTY;
	wire w_wdom_ptr_xor;
	wire w_rdom_ptr_xor;
	wire w_wr_full_d;
	wire w_wr_almost_full_d;
	wire w_rd_empty_d;
	wire w_rd_almost_empty_d;
	wire [AW:0] w_almost_full_count;
	wire [AW:0] w_almost_empty_count;
	assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
	assign w_rdom_ptr_xor = rd_ptr_bin[AW] ^ rdom_wr_ptr_bin[AW];
	assign w_wr_full_d = w_wdom_ptr_xor && (wr_ptr_bin[AW - 1:0] == wdom_rd_ptr_bin[AW - 1:0]);
	function automatic signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65_signed;
		input reg signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65_signed = inp;
	endfunction
	assign w_almost_full_count = (w_wdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - wdom_rd_ptr_bin[AW - 1:0]) + wr_ptr_bin[AW - 1:0] : wr_ptr_bin[AW - 1:0] - wdom_rd_ptr_bin[AW - 1:0]);
	assign w_wr_almost_full_d = w_almost_full_count >= sv2v_cast_2BB65_signed(AFT);
	always @(posedge wr_clk or negedge wr_rst_n)
		if (!wr_rst_n) begin
			wr_full <= 'b0;
			wr_almost_full <= 'b0;
		end
		else begin
			wr_full <= w_wr_full_d;
			wr_almost_full <= w_wr_almost_full_d;
		end
	wire [ADDR_WIDTH:0] w_wr_ptr_for_empty;
	wire w_rdom_ptr_xor_for_empty;
	generate
		if (REGISTERED == 1) begin : gen_flop_mode
			reg [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;
			always @(posedge rd_clk or negedge rd_rst_n)
				if (!rd_rst_n)
					r_rdom_wr_ptr_bin_delayed <= 1'sb0;
				else
					r_rdom_wr_ptr_bin_delayed <= rdom_wr_ptr_bin;
			assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
		end
		else begin : gen_mux_mode
			assign w_wr_ptr_for_empty = rdom_wr_ptr_bin;
		end
	endgenerate
	assign w_rdom_ptr_xor_for_empty = rd_ptr_bin[AW] ^ w_wr_ptr_for_empty[AW];
	assign w_rd_empty_d = !w_rdom_ptr_xor_for_empty && (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]);
	assign w_almost_empty_count = (w_rdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - rd_ptr_bin[AW - 1:0]) + rdom_wr_ptr_bin[AW - 1:0] : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign w_rd_almost_empty_d = w_almost_empty_count <= sv2v_cast_2BB65_signed(AET);
	wire [ADDR_WIDTH:0] w_count;
	reg [ADDR_WIDTH:0] r_count;
	assign w_count = (w_rdom_ptr_xor ? (rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]) + sv2v_cast_2BB65_signed(D) : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign count = (REGISTERED == 1 ? r_count : w_count);
	always @(posedge rd_clk or negedge rd_rst_n)
		if (!rd_rst_n) begin
			rd_empty <= 'b1;
			rd_almost_empty <= 'b0;
			r_count <= 'b0;
		end
		else begin
			rd_empty <= w_rd_empty_d;
			rd_almost_empty <= w_rd_almost_empty_d;
			r_count <= w_count;
		end
endmodule
module gaxi_fifo_sync (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_ready,
	count,
	rd_valid,
	rd_data
);
	parameter signed [31:0] MEM_STYLE = 32'sd0;
	parameter signed [31:0] REGISTERED = 0;
	parameter signed [31:0] DATA_WIDTH = 4;
	parameter signed [31:0] DEPTH = 4;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(DEPTH);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire [DW - 1:0] wr_data;
	input wire rd_ready;
	output wire [AW:0] count;
	output wire rd_valid;
	output wire [DW - 1:0] rd_data;
	wire [AW - 1:0] r_wr_addr;
	wire [AW - 1:0] r_rd_addr;
	wire [AW:0] r_wr_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire w_write;
	wire w_read;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) write_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_write && !r_wr_full),
		.counter_bin_curr(r_wr_ptr_bin),
		.counter_bin_next(w_wr_ptr_bin_next)
	);
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) read_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_read && !r_rd_empty),
		.counter_bin_curr(r_rd_ptr_bin),
		.counter_bin_next(w_rd_ptr_bin_next)
	);
	fifo_control #(
		.DEPTH(D),
		.ADDR_WIDTH(AW),
		.ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
		.ALMOST_WR_MARGIN(ALMOST_WR_MARGIN),
		.REGISTERED(REGISTERED)
	) fifo_control_inst(
		.wr_clk(axi_aclk),
		.wr_rst_n(axi_aresetn),
		.rd_clk(axi_aclk),
		.rd_rst_n(axi_aresetn),
		.wr_ptr_bin(w_wr_ptr_bin_next),
		.wdom_rd_ptr_bin(w_rd_ptr_bin_next),
		.rd_ptr_bin(w_rd_ptr_bin_next),
		.rdom_wr_ptr_bin(w_wr_ptr_bin_next),
		.count(count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_valid = !r_rd_empty;
	assign r_wr_addr = r_wr_ptr_bin[AW - 1:0];
	assign r_rd_addr = r_rd_ptr_bin[AW - 1:0];
	generate
		if (MEM_STYLE == 32'sd1) begin : gen_srl
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			reg [DATA_WIDTH - 1:0] r_rd_data;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_rd_data <= 1'sb0;
				else
					r_rd_data <= mem[r_rd_addr];
			assign rd_data = r_rd_data;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
	endgenerate
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
endmodule
module gaxi_skid_buffer (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	count,
	rd_valid,
	rd_ready,
	rd_count,
	rd_data
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DEPTH = 2;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output reg wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire [3:0] count;
	output reg rd_valid;
	input wire rd_ready;
	output wire [3:0] rd_count;
	output wire [DW - 1:0] rd_data;
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/amba/gaxi/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
			localparam gi = _gv_gi_1;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_data[gi] <= 1'sb0;
				else
					(* full_case, parallel_case *)
					case ({w_wr_xfer, w_rd_xfer})
						2'b10:
							if (r_data_count == gi[3:0])
								r_data[gi] <= wr_data;
						2'b01:
							if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						2'b11:
							if ((r_data_count >= 1) && (gi[3:0] == (r_data_count - 4'd1)))
								r_data[gi] <= wr_data;
							else if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						default:
							;
					endcase
		end
	endgenerate
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_data_count <= 1'sb0;
		else
			(* full_case, parallel_case *)
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: r_data_count <= r_data_count + 4'd1;
				2'b01: r_data_count <= r_data_count - 4'd1;
				default:
					;
			endcase
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[0];
	assign rd_count = r_data_count;
	assign count = r_data_count;
endmodule
module wb4_monitor (
	aclk,
	aresetn,
	cmd_valid,
	cmd_ready,
	cmd_we,
	cmd_adr,
	cmd_dat,
	cmd_sel,
	cmd_cti,
	rsp_valid,
	rsp_ready,
	rsp_status,
	rsp_dat,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_protocol_enable,
	cfg_slverr_enable,
	cfg_perf_enable,
	cfg_latency_enable,
	cfg_throughput_enable,
	cfg_debug_enable,
	cfg_trans_debug_enable,
	cfg_debug_level,
	cfg_cmd_timeout_cnt,
	cfg_rsp_timeout_cnt,
	cfg_latency_threshold,
	cfg_throughput_threshold,
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	active_count,
	error_count,
	transaction_count
);
	reg _sv2v_0;
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000b;
	parameter signed [31:0] MAX_TRANSACTIONS = 8;
	parameter signed [31:0] MONITOR_FIFO_DEPTH = 8;
	parameter signed [31:0] USE_BURST_HINTS = 0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = DW / 8;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_CTI_WIDTH = 3;
	parameter signed [31:0] CTW = wb4_pkg_WB4_CTI_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cmd_we;
	input wire [AW - 1:0] cmd_adr;
	input wire [DW - 1:0] cmd_dat;
	input wire [SW - 1:0] cmd_sel;
	input wire [CTW - 1:0] cmd_cti;
	input wire rsp_valid;
	input wire rsp_ready;
	input wire [STW - 1:0] rsp_status;
	input wire [DW - 1:0] rsp_dat;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_protocol_enable;
	input wire cfg_slverr_enable;
	input wire cfg_perf_enable;
	input wire cfg_latency_enable;
	input wire cfg_throughput_enable;
	input wire cfg_debug_enable;
	input wire cfg_trans_debug_enable;
	input wire [3:0] cfg_debug_level;
	input wire [15:0] cfg_cmd_timeout_cnt;
	input wire [15:0] cfg_rsp_timeout_cnt;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_throughput_threshold;
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_high;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire [7:0] active_count;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
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
	function automatic [2:0] sv2v_cast_90DB4;
		input reg [2:0] inp;
		sv2v_cast_90DB4 = inp;
	endfunction
	function automatic [CTW - 1:0] sv2v_cast_E0906;
		input reg [CTW - 1:0] inp;
		sv2v_cast_E0906 = inp;
	endfunction
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [1:0] sv2v_cast_1AA03;
		input reg [1:0] inp;
		sv2v_cast_1AA03 = inp;
	endfunction
	function automatic [3:0] sv2v_cast_4;
		input reg [3:0] inp;
		sv2v_cast_4 = inp;
	endfunction
	generate
		if (USE_MONITOR) begin : gen_monitor
			localparam signed [31:0] QW = $clog2(MAX_TRANSACTIONS);
			localparam signed [31:0] CW = $clog2(MAX_TRANSACTIONS + 1);
			wire [CTW - 1:0] w_cmd_cti;
			assign w_cmd_cti = (USE_BURST_HINTS != 0 ? cmd_cti : sv2v_cast_E0906(sv2v_cast_90DB4(3'b000)));
			reg [(((1 + AW) + 4) + CTW) + 32:0] r_q [0:MAX_TRANSACTIONS - 1];
			reg [QW - 1:0] r_head;
			reg [QW - 1:0] r_tail;
			reg [CW - 1:0] r_count;
			wire w_q_empty;
			wire w_q_full;
			wire [(((1 + AW) + 4) + CTW) + 32:0] w_head;
			reg [31:0] r_timestamp;
			reg [15:0] r_error_count;
			reg [31:0] r_transaction_count;
			wire w_cmd_handshake;
			wire w_rsp_handshake;
			wire w_push;
			wire w_pop;
			wire w_track_lost;
			wire w_orphan;
			reg [15:0] r_cmd_stall_timer;
			reg r_cmd_timeout_reported;
			wire w_cmd_timeout_fire;
			wire w_rsp_timeout_fire;
			wire [31:0] w_head_age;
			assign w_cmd_handshake = cmd_valid && cmd_ready;
			assign w_rsp_handshake = rsp_valid && rsp_ready;
			assign w_q_empty = r_count == {CW {1'sb0}};
			assign w_q_full = sv2v_cast_32(r_count) >= MAX_TRANSACTIONS;
			assign w_head = r_q[r_head];
			assign w_push = w_cmd_handshake && !w_q_full;
			assign w_track_lost = w_cmd_handshake && w_q_full;
			assign w_pop = w_rsp_handshake && !w_q_empty;
			assign w_orphan = w_rsp_handshake && w_q_empty;
			assign active_count = sv2v_cast_8(r_count);
			assign error_count = r_error_count;
			assign transaction_count = r_transaction_count;
			wire [31:0] w_latency;
			wire w_is_err;
			wire w_is_rty;
			wire w_is_ack;
			assign w_latency = r_timestamp - w_head[32-:32];
			assign w_is_err = rsp_status == sv2v_cast_1AA03(2'b01);
			assign w_is_rty = rsp_status == sv2v_cast_1AA03(2'b10);
			assign w_is_ack = !w_is_err && !w_is_rty;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_timestamp <= 1'sb0;
					r_head <= 1'sb0;
					r_tail <= 1'sb0;
					r_count <= 1'sb0;
					r_error_count <= 1'sb0;
					r_transaction_count <= 1'sb0;
					begin : sv2v_autoblock_1
						reg signed [31:0] i;
						for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
							r_q[i] <= 1'sb0;
					end
				end
				else begin
					r_timestamp <= r_timestamp + 1'b1;
					if (w_push) begin
						r_q[r_tail][1 + (AW + (4 + (CTW + 32)))] <= cmd_we;
						r_q[r_tail][AW + (4 + (CTW + 32))-:((AW + (4 + (CTW + 32))) >= (4 + (CTW + 33)) ? ((AW + (4 + (CTW + 32))) - (4 + (CTW + 33))) + 1 : ((4 + (CTW + 33)) - (AW + (4 + (CTW + 32)))) + 1)] <= cmd_adr;
						r_q[r_tail][4 + (CTW + 32)-:((4 + (CTW + 32)) >= (CTW + 33) ? ((4 + (CTW + 32)) - (CTW + 33)) + 1 : ((CTW + 33) - (4 + (CTW + 32))) + 1)] <= sv2v_cast_4(cmd_sel);
						r_q[r_tail][CTW + 32-:((CTW + 32) >= 33 ? CTW + 0 : 34 - (CTW + 32))] <= w_cmd_cti;
						r_q[r_tail][32-:32] <= r_timestamp;
						r_q[r_tail][0] <= 1'b0;
						r_tail <= (sv2v_cast_32(r_tail) == (MAX_TRANSACTIONS - 1) ? {QW {1'sb0}} : r_tail + 1'b1);
					end
					if (w_pop) begin
						r_head <= (sv2v_cast_32(r_head) == (MAX_TRANSACTIONS - 1) ? {QW {1'sb0}} : r_head + 1'b1);
						r_transaction_count <= r_transaction_count + 1'b1;
					end
					begin : sv2v_autoblock_2
						reg [CW - 1:0] sv2v_tmp_cast;
						reg [CW - 1:0] sv2v_tmp_cast_1;
						sv2v_tmp_cast = w_push;
						sv2v_tmp_cast_1 = w_pop;
						r_count <= (r_count + sv2v_tmp_cast) - sv2v_tmp_cast_1;
					end
					if (w_rsp_timeout_fire && !w_q_empty)
						r_q[r_head][0] <= 1'b1;
					if ((((w_rsp_handshake && w_is_err) && cfg_slverr_enable) || w_orphan) || w_track_lost)
						r_error_count <= r_error_count + 1'b1;
				end
			assign w_head_age = r_timestamp - w_head[32-:32];
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_cmd_stall_timer <= 1'sb0;
					r_cmd_timeout_reported <= 1'b0;
				end
				else if (cmd_valid && !cmd_ready) begin
					if (r_cmd_stall_timer != 16'hffff)
						r_cmd_stall_timer <= r_cmd_stall_timer + 1'b1;
					if (w_cmd_timeout_fire)
						r_cmd_timeout_reported <= 1'b1;
				end
				else begin
					r_cmd_stall_timer <= 1'sb0;
					r_cmd_timeout_reported <= 1'b0;
				end
			assign w_cmd_timeout_fire = ((((cfg_timeout_enable && cmd_valid) && !cmd_ready) && !r_cmd_timeout_reported) && (cfg_cmd_timeout_cnt != {16 {1'sb0}})) && (r_cmd_stall_timer >= cfg_cmd_timeout_cnt);
			assign w_rsp_timeout_fire = (((cfg_timeout_enable && !w_q_empty) && !w_head[0]) && (cfg_rsp_timeout_cnt != {16 {1'sb0}})) && (w_head_age >= sv2v_cast_32(cfg_rsp_timeout_cnt));
			reg r_q_active_q;
			wire w_q_active_edge;
			wire w_q_idle_edge;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn)
					r_q_active_q <= 1'b0;
				else
					r_q_active_q <= !w_q_empty;
			assign w_q_active_edge = !w_q_empty && !r_q_active_q;
			assign w_q_idle_edge = w_q_empty && r_q_active_q;
			reg w_fifo_wr_valid;
			wire w_fifo_wr_ready;
			wire w_fifo_rd_valid;
			wire w_fifo_rd_ready;
			reg [51:0] w_fifo_wr_data;
			wire [51:0] w_fifo_rd_data;
			wire [7:0] w_aux_head;
			wire [7:0] w_aux_cmd;
			wire [31:0] w_adr_head;
			wire [31:0] w_adr_cmd;
			assign w_aux_head = {w_head[CTW + 32-:((CTW + 32) >= 33 ? CTW + 0 : 34 - (CTW + 32))], w_head[4 + (CTW + 32)-:((4 + (CTW + 32)) >= (CTW + 33) ? ((4 + (CTW + 32)) - (CTW + 33)) + 1 : ((CTW + 33) - (4 + (CTW + 32))) + 1)], w_head[1 + (AW + (4 + (CTW + 32)))]};
			assign w_aux_cmd = {w_cmd_cti, sv2v_cast_4(cmd_sel), cmd_we};
			assign w_adr_head = sv2v_cast_32(w_head[AW + (4 + (CTW + 32))-:((AW + (4 + (CTW + 32))) >= (4 + (CTW + 33)) ? ((AW + (4 + (CTW + 32))) - (4 + (CTW + 33))) + 1 : ((4 + (CTW + 33)) - (AW + (4 + (CTW + 32)))) + 1)]);
			assign w_adr_cmd = sv2v_cast_32(cmd_adr);
			always @(*) begin
				if (_sv2v_0)
					;
				w_fifo_wr_valid = 1'b0;
				w_fifo_wr_data = 1'sb0;
				if ((((cfg_error_enable && w_rsp_handshake) && w_is_err) && cfg_slverr_enable) && !w_q_empty) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeError, 8'h00, w_adr_head, w_aux_head};
				end
				else if ((cfg_error_enable && cfg_protocol_enable) && w_orphan) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeError, 8'h01, sv2v_cast_32(rsp_dat), 6'h00, rsp_status};
				end
				else if (cfg_error_enable && w_track_lost) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeError, 8'h02, w_adr_cmd, w_aux_cmd};
				end
				else if (w_cmd_timeout_fire) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeTimeout, 8'h00, w_adr_cmd, r_cmd_stall_timer[7:0]};
				end
				else if (w_rsp_timeout_fire) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeTimeout, 8'h01, w_adr_head, w_head_age[7:0]};
				end
				else if (((cfg_perf_enable && cfg_latency_enable) && w_pop) && (w_latency > cfg_latency_threshold)) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypePerf, (w_head[1 + (AW + (4 + (CTW + 32)))] ? 8'h01 : 8'h00), w_latency, w_aux_head};
				end
				else if ((cfg_debug_enable && cfg_trans_debug_enable) && (w_q_active_edge || w_q_idle_edge)) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeDebug, (w_q_active_edge ? 8'h00 : 8'h01), 24'h000000, sv2v_cast_8(r_count), 8'h00};
				end
				else if (w_pop && (w_is_ack || w_is_rty)) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data = {monitor_common_pkg_PktTypeCompletion, (w_is_rty ? 8'h03 : (w_head[1 + (AW + (4 + (CTW + 32)))] ? 8'h02 : 8'h01)), w_adr_head, w_aux_head};
				end
			end
			gaxi_fifo_sync #(
				.REGISTERED(0),
				.DATA_WIDTH(52),
				.DEPTH(MONITOR_FIFO_DEPTH),
				.ALMOST_WR_MARGIN(1),
				.ALMOST_RD_MARGIN(1)
			) monitor_fifo(
				.axi_aclk(aclk),
				.axi_aresetn(aresetn),
				.wr_valid(w_fifo_wr_valid),
				.wr_ready(w_fifo_wr_ready),
				.wr_data(w_fifo_wr_data),
				.rd_ready(w_fifo_rd_ready),
				.count(),
				.rd_valid(w_fifo_rd_valid),
				.rd_data(w_fifo_rd_data)
			);
			wire w_fifo_drop;
			assign w_fifo_drop = w_fifo_wr_valid && !w_fifo_wr_ready;
			reg w_monbus_pkt_valid;
			wire w_monbus_pkt_ready;
			reg [127:0] w_monbus_pkt_data;
			wire [127:0] w_fifo_pkt_data;
			reg [63:0] w_monbus_pkt_ts;
			assign w_fifo_pkt_data = monitor_common_pkg_create_monitor_packet(w_fifo_rd_data[51-:4], 4'h5, w_fifo_rd_data[47-:8], 9'h000, UNIT_ID, AGENT_ID, {24'h000000, w_fifo_rd_data[7-:8], w_fifo_rd_data[39-:32]});
			wire w_addr_pkt_valid;
			wire w_addr_pkt_ready;
			wire [127:0] w_addr_pkt_data;
			wire [63:0] w_addr_pkt_timestamp;
			if (N_ADDR_RANGES > 0) begin : gen_addr_check
				apb_monitor_addr_check #(
					.N_ADDR_RANGES(N_ADDR_RANGES),
					.ADDR_WIDTH(ADDR_WIDTH),
					.UNIT_ID(UNIT_ID),
					.AGENT_ID(AGENT_ID),
					.PROTOCOL(4'h5)
				) addr_check(
					.clk(aclk),
					.aresetn(aresetn),
					.i_mon_time(i_mon_time),
					.cmd_paddr(cmd_adr),
					.cmd_pwrite(cmd_we),
					.cmd_valid(cmd_valid),
					.cmd_ready(cmd_ready),
					.cfg_addr_check_enable(cfg_addr_check_enable),
					.cfg_addr_range_enable(cfg_addr_range_enable),
					.cfg_addr_range_low(cfg_addr_range_low),
					.cfg_addr_range_high(cfg_addr_range_high),
					.addr_pkt_valid(w_addr_pkt_valid),
					.addr_pkt_ready(w_addr_pkt_ready),
					.addr_pkt_data(w_addr_pkt_data),
					.addr_pkt_timestamp(w_addr_pkt_timestamp)
				);
			end
			else begin : gen_no_addr_check
				assign w_addr_pkt_valid = 1'b0;
				assign w_addr_pkt_data = 1'sb0;
				assign w_addr_pkt_timestamp = 1'sb0;
				wire w_unused_addr;
				assign w_unused_addr = ^{cfg_addr_check_enable, cfg_addr_range_enable, cfg_addr_range_low, cfg_addr_range_high, w_addr_pkt_ready};
			end
			always @(*) begin
				if (_sv2v_0)
					;
				if (w_fifo_rd_valid) begin
					w_monbus_pkt_valid = 1'b1;
					w_monbus_pkt_data = w_fifo_pkt_data;
					w_monbus_pkt_ts = i_mon_time;
				end
				else if (w_addr_pkt_valid) begin
					w_monbus_pkt_valid = 1'b1;
					w_monbus_pkt_data = w_addr_pkt_data;
					w_monbus_pkt_ts = w_addr_pkt_timestamp;
				end
				else begin
					w_monbus_pkt_valid = 1'b0;
					w_monbus_pkt_data = 1'sb0;
					w_monbus_pkt_ts = 1'sb0;
				end
			end
			assign w_fifo_rd_ready = w_monbus_pkt_ready && w_fifo_rd_valid;
			assign w_addr_pkt_ready = w_monbus_pkt_ready && !w_fifo_rd_valid;
			localparam signed [31:0] MONBUS_TOTAL_W = monitor_common_pkg_MONBUS_PKT_WIDTH + monitor_common_pkg_MONBUS_TS_WIDTH;
			wire [MONBUS_TOTAL_W - 1:0] w_skid_wr_data;
			wire [MONBUS_TOTAL_W - 1:0] w_skid_rd_data;
			assign w_skid_wr_data = {w_monbus_pkt_data, w_monbus_pkt_ts};
			gaxi_skid_buffer #(
				.DATA_WIDTH(MONBUS_TOTAL_W),
				.DEPTH(2)
			) monbus_skid_buffer(
				.axi_aclk(aclk),
				.axi_aresetn(aresetn),
				.wr_valid(w_monbus_pkt_valid),
				.wr_ready(w_monbus_pkt_ready),
				.wr_data(w_skid_wr_data),
				.rd_valid(monbus_valid),
				.rd_ready(monbus_ready),
				.rd_data(w_skid_rd_data),
				.count(),
				.rd_count()
			);
			assign monbus_packet = w_skid_rd_data[MONBUS_TOTAL_W - 1-:monitor_common_pkg_MONBUS_PKT_WIDTH];
			assign monbus_timestamp = w_skid_rd_data[63:0];
			wire w_unused;
			assign w_unused = ^{cfg_throughput_enable, cfg_debug_level, cfg_throughput_threshold, cmd_dat, rsp_dat[DW - 1:1], cmd_cti};
			reg f_past_valid;
			initial f_past_valid = 1'b0;
			always @(posedge aclk) f_past_valid <= 1'b1;
			always @(posedge aclk)
				if ((f_past_valid && aresetn) && $past(aresetn)) begin
					assert (sv2v_cast_32(r_count) <= MAX_TRANSACTIONS) ;
					assert (!w_pop || !w_q_empty) ;
					assert (!w_orphan || w_q_empty) ;
				end
		end
		else begin : gen_no_monitor
			assign monbus_valid = 1'b0;
			assign monbus_packet = 1'sb0;
			assign monbus_timestamp = 1'sb0;
			assign active_count = 8'h00;
			assign error_count = 16'h0000;
			assign transaction_count = 32'h00000000;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
