module monitor_trans_cam (
	clk,
	rst_n,
	clear,
	lookup_addr_id,
	lookup_data_id,
	lookup_resp_id,
	addr_match_oh,
	data_match_oh,
	resp_match_oh,
	data_match_first_oh,
	free_oh,
	addr_wants_alloc,
	data_wants_alloc,
	resp_wants_alloc,
	addr_alloc_oh,
	data_alloc_oh,
	resp_alloc_oh,
	entry_we,
	entry_valid_next,
	entry_id_next,
	entry_payload_next,
	entry_valid,
	entry_id,
	entry_payload
);
	reg _sv2v_0;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] PAYLOAD_WIDTH = 128;
	input wire clk;
	input wire rst_n;
	input wire clear;
	input wire [ID_WIDTH - 1:0] lookup_addr_id;
	input wire [ID_WIDTH - 1:0] lookup_data_id;
	input wire [ID_WIDTH - 1:0] lookup_resp_id;
	output wire [DEPTH - 1:0] addr_match_oh;
	output wire [DEPTH - 1:0] data_match_oh;
	output wire [DEPTH - 1:0] resp_match_oh;
	output reg [DEPTH - 1:0] data_match_first_oh;
	output wire [DEPTH - 1:0] free_oh;
	input wire addr_wants_alloc;
	input wire data_wants_alloc;
	input wire resp_wants_alloc;
	output reg [DEPTH - 1:0] addr_alloc_oh;
	output reg [DEPTH - 1:0] data_alloc_oh;
	output reg [DEPTH - 1:0] resp_alloc_oh;
	input wire [DEPTH - 1:0] entry_we;
	input wire [DEPTH - 1:0] entry_valid_next;
	input wire [(DEPTH * ID_WIDTH) - 1:0] entry_id_next;
	input wire [(DEPTH * PAYLOAD_WIDTH) - 1:0] entry_payload_next;
	output wire [DEPTH - 1:0] entry_valid;
	output wire [(DEPTH * ID_WIDTH) - 1:0] entry_id;
	output wire [(DEPTH * PAYLOAD_WIDTH) - 1:0] entry_payload;
	reg r_valid [0:DEPTH - 1];
	reg [ID_WIDTH - 1:0] r_id [0:DEPTH - 1];
	reg [PAYLOAD_WIDTH - 1:0] r_payload [0:DEPTH - 1];
	(* keep = "true" *) reg [DEPTH - 1:0] w_addr_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_data_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_resp_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_free_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				begin
					w_addr_match_oh[i] = r_valid[i] && (r_id[i] == lookup_addr_id);
					w_data_match_oh[i] = r_valid[i] && (r_id[i] == lookup_data_id);
					w_resp_match_oh[i] = r_valid[i] && (r_id[i] == lookup_resp_id);
					w_free_oh[i] = !r_valid[i];
				end
		end
	end
	assign addr_match_oh = w_addr_match_oh;
	assign data_match_oh = w_data_match_oh;
	assign resp_match_oh = w_resp_match_oh;
	assign free_oh = w_free_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		data_match_first_oh = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				if (w_data_match_oh[i] && (data_match_first_oh == {DEPTH {1'sb0}}))
					data_match_first_oh[i] = 1'b1;
		end
	end
	always @(*) begin : sv2v_autoblock_3
		reg [DEPTH - 1:0] remaining;
		reg taken;
		if (_sv2v_0)
			;
		addr_alloc_oh = 1'sb0;
		data_alloc_oh = 1'sb0;
		resp_alloc_oh = 1'sb0;
		taken = 1'b0;
		remaining = w_free_oh;
		if (addr_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					if (!taken && remaining[i]) begin
						addr_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
		if (data_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					if (!taken && remaining[i]) begin
						data_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
		if (resp_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					if (!taken && remaining[i]) begin
						resp_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
	end
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
			localparam gi = _gv_gi_1;
			always @(posedge clk)
				if (!rst_n) begin
					r_valid[gi] <= 1'b0;
					r_id[gi] <= 1'sb0;
					r_payload[gi] <= 1'sb0;
				end
				else if (clear)
					r_valid[gi] <= 1'b0;
				else if (entry_we[gi]) begin
					r_valid[gi] <= entry_valid_next[gi];
					r_id[gi] <= entry_id_next[((DEPTH - 1) - gi) * ID_WIDTH+:ID_WIDTH];
					r_payload[gi] <= entry_payload_next[((DEPTH - 1) - gi) * PAYLOAD_WIDTH+:PAYLOAD_WIDTH];
				end
			assign entry_valid[gi] = r_valid[gi];
			assign entry_id[((DEPTH - 1) - gi) * ID_WIDTH+:ID_WIDTH] = r_id[gi];
			assign entry_payload[((DEPTH - 1) - gi) * PAYLOAD_WIDTH+:PAYLOAD_WIDTH] = r_payload[gi];
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_trans_mgr (
	aclk,
	aresetn,
	clear,
	cmd_valid,
	cmd_ready,
	cmd_id,
	cmd_addr,
	cmd_len,
	cmd_size,
	cmd_burst,
	data_valid,
	data_ready,
	data_id,
	data_last,
	data_resp,
	resp_valid,
	resp_ready,
	resp_id,
	resp_code,
	timestamp,
	i_event_reported_flags,
	trans_table,
	active_count,
	state_change
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire clear;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire [IW - 1:0] cmd_id;
	input wire [AW - 1:0] cmd_addr;
	input wire [7:0] cmd_len;
	input wire [2:0] cmd_size;
	input wire [1:0] cmd_burst;
	input wire data_valid;
	input wire data_ready;
	input wire [IW - 1:0] data_id;
	input wire data_last;
	input wire [1:0] data_resp;
	input wire resp_valid;
	input wire resp_ready;
	input wire [IW - 1:0] resp_id;
	input wire [1:0] resp_code;
	input wire [31:0] timestamp;
	input wire [MAX_TRANSACTIONS - 1:0] i_event_reported_flags;
	output wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	localparam signed [31:0] N = MAX_TRANSACTIONS;
	localparam signed [31:0] PAYLOAD_W = 285;
	wire [N - 1:0] addr_match_oh;
	wire [N - 1:0] data_match_oh;
	wire [N - 1:0] resp_match_oh;
	wire [N - 1:0] cam_data_match_first_oh;
	wire [N - 1:0] free_oh;
	wire [N - 1:0] addr_alloc_oh;
	wire [N - 1:0] data_alloc_oh;
	wire [N - 1:0] resp_alloc_oh;
	wire [N - 1:0] cam_entry_valid;
	wire [(N * 285) - 1:0] cam_entry_payload;
	wire [N - 1:0] cam_entry_we;
	wire [N - 1:0] cam_entry_valid_next;
	wire [(N * IW) - 1:0] cam_entry_id_next;
	wire [(N * 285) - 1:0] cam_entry_payload_next;
	wire addr_wants_alloc;
	reg data_wants_alloc;
	reg resp_wants_alloc;
	monitor_trans_cam #(
		.DEPTH(N),
		.ID_WIDTH(IW),
		.PAYLOAD_WIDTH(PAYLOAD_W)
	) u_cam(
		.clk(aclk),
		.rst_n(aresetn),
		.clear(clear),
		.lookup_addr_id(cmd_id),
		.lookup_data_id(data_id),
		.lookup_resp_id(resp_id),
		.addr_match_oh(addr_match_oh),
		.data_match_oh(data_match_oh),
		.resp_match_oh(resp_match_oh),
		.data_match_first_oh(cam_data_match_first_oh),
		.free_oh(free_oh),
		.addr_wants_alloc(addr_wants_alloc),
		.data_wants_alloc(data_wants_alloc),
		.resp_wants_alloc(resp_wants_alloc),
		.addr_alloc_oh(addr_alloc_oh),
		.data_alloc_oh(data_alloc_oh),
		.resp_alloc_oh(resp_alloc_oh),
		.entry_we(cam_entry_we),
		.entry_valid_next(cam_entry_valid_next),
		.entry_id_next(cam_entry_id_next),
		.entry_payload_next(cam_entry_payload_next),
		.entry_valid(cam_entry_valid),
		.entry_id(),
		.entry_payload(cam_entry_payload)
	);
	(* keep = "true" *) reg [N - 1:0] w_data_state_pred_oh;
	reg [N - 1:0] w_data_state_first_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_data_state_first_oh = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_state_pred_oh[i] = ((cam_entry_valid[i] && ((cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1) || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h2))) && cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (w_data_state_pred_oh[i] && (w_data_state_first_oh == {N {1'sb0}}))
					w_data_state_first_oh[i] = 1'b1;
		end
	end
	wire addr_hit_any;
	wire data_hit_any;
	wire resp_hit_any;
	assign addr_hit_any = |addr_match_oh;
	assign resp_hit_any = |resp_match_oh;
	assign data_hit_any = (IS_READ ? |data_match_oh : |w_data_state_pred_oh);
	assign addr_wants_alloc = cmd_valid && !addr_hit_any;
	always @(*) begin
		if (_sv2v_0)
			;
		if (IS_READ)
			data_wants_alloc = (data_valid && data_ready) && !data_hit_any;
		else
			data_wants_alloc = ((data_valid && data_ready) && !IS_AXI) && !data_hit_any;
		resp_wants_alloc = ((!IS_READ && resp_valid) && resp_ready) && !resp_hit_any;
	end
	wire [N - 1:0] addr_update_oh;
	wire [N - 1:0] data_update_oh;
	wire [N - 1:0] resp_update_oh;
	assign addr_update_oh = addr_match_oh;
	assign data_update_oh = (IS_READ ? data_match_oh : w_data_state_first_oh);
	assign resp_update_oh = resp_match_oh;
	reg [N - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i])
					(* full_case, parallel_case *)
					case (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3])
						3'h3, 3'h4, 3'h5: w_can_cleanup[i] = cam_entry_payload[(((N - 1) - i) * 285) + 279];
						default: w_can_cleanup[i] = 1'b0;
					endcase
				else
					w_can_cleanup[i] = 1'b0;
		end
	end
	reg [5:0] w_addr_chan_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
	end
	wire cmd_handshake;
	assign cmd_handshake = cmd_valid && cmd_ready;
	genvar _gv_gi_2;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 8'h02;
	localparam [7:0] monitor_amba4_pkg_EVT_PROTOCOL = 8'h04;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_DECERR = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 8'h03;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 8'h00;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		for (_gv_gi_2 = 0; _gv_gi_2 < N; _gv_gi_2 = _gv_gi_2 + 1) begin : g_entry_next
			localparam gi = _gv_gi_2;
			reg [284:0] next;
			reg next_we;
			reg [IW - 1:0] next_id;
			always @(*) begin
				if (_sv2v_0)
					;
				next = cam_entry_payload[((N - 1) - gi) * 285+:285];
				next_we = 1'b0;
				next_id = cam_entry_payload[(((N - 1) - gi) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))];
				if (addr_alloc_oh[gi]) begin
					next[284] = 1'b1;
					next[277-:3] = 3'h1;
					next[242-:8] = 1'sb0;
					next[234 + IW:235] = cmd_id;
					next[274-:32] = sv2v_cast_32(cmd_addr);
					next[234-:8] = cmd_len;
					next[226-:3] = cmd_size;
					next[223-:2] = cmd_burst;
					next[283] = cmd_ready;
					next[215-:32] = 1'sb0;
					next[282] = 1'b0;
					next[281] = 1'b0;
					next[280] = 1'b0;
					next[7-:8] = 8'h00;
					next[279] = 1'b0;
					next[183-:32] = 1'sb0;
					next[151-:32] = 1'sb0;
					next[119-:32] = timestamp;
					next[23-:8] = (IS_AXI ? cmd_len + 8'h01 : 8'h01);
					next[15-:8] = 1'sb0;
					next[221-:6] = w_addr_chan_idx;
					next[278] = 1'b0;
					next_we = 1'b1;
					next_id = cmd_id;
				end
				if (addr_update_oh[gi] && cmd_handshake) begin
					next[283] = 1'b1;
					next[215-:32] = 1'sb0;
					next[119-:32] = timestamp;
					next_we = 1'b1;
				end
				if (data_valid && data_ready) begin
					if (data_update_oh[gi]) begin
						next[282] = 1'b1;
						next[15-:8] = cam_entry_payload[(((N - 1) - gi) * 285) + 15-:8] + 1'b1;
						next[183-:32] = 1'sb0;
						if (next[277-:3] != 3'h4)
							next[277-:3] = 3'h2;
						if (IS_READ) begin
							if (data_last) begin
								next[281] = 1'b1;
								next[87-:32] = timestamp;
							end
							if (data_resp[1]) begin
								next[277-:3] = 3'h4;
								next[7-:8] = (data_resp[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
							end
							else if (data_last)
								next[277-:3] = 3'h3;
						end
						else if (data_last || (next[15-:8] == cam_entry_payload[(((N - 1) - gi) * 285) + 23-:8])) begin
							next[281] = 1'b1;
							next[87-:32] = timestamp;
						end
						next_we = 1'b1;
					end
					else if (data_alloc_oh[gi]) begin
						next[284] = 1'b1;
						next[277-:3] = 3'h5;
						next[242-:8] = 1'sb0;
						if (IS_AXI) begin
							next[234 + IW:235] = data_id;
							next[221-:6] = {24'h000000, data_id} % 64;
							next[23-:8] = (IS_READ ? 8'h00 : 8'h01);
						end
						else begin
							next[23-:8] = 8'h01;
							next[221-:6] = 6'h00;
						end
						next[282] = 1'b1;
						next[281] = data_last;
						next[15-:8] = 8'h01;
						next[87-:32] = timestamp;
						next[7-:8] = monitor_amba4_pkg_EVT_DATA_ORPHAN;
						next_we = 1'b1;
						next_id = (IS_AXI ? data_id : {IW {1'sb0}});
					end
				end
				if ((!IS_READ && resp_valid) && resp_ready) begin
					if (resp_update_oh[gi]) begin
						next[280] = 1'b1;
						next[55-:32] = timestamp;
						next[151-:32] = 1'sb0;
						if (resp_code[1]) begin
							next[277-:3] = 3'h4;
							next[7-:8] = (resp_code[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
						end
						else if (cam_entry_payload[(((N - 1) - gi) * 285) + 281]) begin
							if (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)
								next[277-:3] = 3'h3;
						end
						else begin
							next[277-:3] = 3'h4;
							next[7-:8] = monitor_amba4_pkg_EVT_PROTOCOL;
						end
						next_we = 1'b1;
					end
					else if (resp_alloc_oh[gi]) begin
						next[284] = 1'b1;
						next[277-:3] = 3'h5;
						next[242-:8] = 1'sb0;
						if (IS_AXI) begin
							next[234 + IW:235] = resp_id;
							next[221-:6] = resp_id % 64;
						end
						else
							next[221-:6] = 6'h00;
						next[280] = 1'b1;
						next[55-:32] = timestamp;
						next[7-:8] = monitor_amba4_pkg_EVT_RESP_ORPHAN;
						next_we = 1'b1;
						next_id = (IS_AXI ? resp_id : {IW {1'sb0}});
					end
				end
				if (cam_entry_valid[gi] && w_can_cleanup[gi]) begin
					next[284] = 1'b0;
					next_we = 1'b1;
				end
				if (i_event_reported_flags[gi] && !cam_entry_payload[(((N - 1) - gi) * 285) + 279]) begin
					next[279] = 1'b1;
					next_we = 1'b1;
				end
			end
			assign cam_entry_we[gi] = next_we;
			assign cam_entry_valid_next[gi] = next[284];
			assign cam_entry_id_next[((N - 1) - gi) * IW+:IW] = next_id;
			assign cam_entry_payload_next[((N - 1) - gi) * 285+:285] = next;
		end
	endgenerate
	assign trans_table = cam_entry_payload;
	reg [7:0] r_active_count;
	reg [$clog2(N + 1) - 1:0] w_occupancy;
	always @(*) begin
		if (_sv2v_0)
			;
		w_occupancy = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_occupancy = w_occupancy + {{$clog2(N + 1) - 1 {1'b0}}, cam_entry_valid[i]};
		end
	end
	always @(posedge aclk)
		if (!aresetn)
			r_active_count <= 1'sb0;
		else if (clear)
			r_active_count <= 1'sb0;
		else
			r_active_count <= {{8 - $clog2(N + 1) {1'b0}}, w_occupancy};
	assign active_count = r_active_count;
	reg [(N * 285) - 1:0] r_trans_table_prev;
	reg [N - 1:0] r_state_change;
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_trans_table_prev[((N - 1) - i) * 285+:285] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= cam_entry_payload;
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_state_change[i] <= (cam_entry_payload[(((N - 1) - i) * 285) + 284] && r_trans_table_prev[(((N - 1) - i) * 285) + 284]) && (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] != r_trans_table_prev[(((N - 1) - i) * 285) + 277-:3]);
			end
		end
	assign state_change = r_state_change;
	initial _sv2v_0 = 0;
endmodule
