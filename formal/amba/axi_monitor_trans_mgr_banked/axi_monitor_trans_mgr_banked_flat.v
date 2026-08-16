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
	addr_alloc_mask,
	data_alloc_mask,
	resp_alloc_mask,
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
	input wire [DEPTH - 1:0] addr_alloc_mask;
	input wire [DEPTH - 1:0] data_alloc_mask;
	input wire [DEPTH - 1:0] resp_alloc_mask;
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
					if ((!taken && remaining[i]) && addr_alloc_mask[i]) begin
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
					if ((!taken && remaining[i]) && data_alloc_mask[i]) begin
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
					if ((!taken && remaining[i]) && resp_alloc_mask[i]) begin
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
	i_timeout_detected,
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
	parameter [0:0] USE_WDATA_ORDER_Q = 1'b0;
	parameter signed [31:0] NUM_BANKS = 1;
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
	input wire [MAX_TRANSACTIONS - 1:0] i_timeout_detected;
	output wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	localparam signed [31:0] N = MAX_TRANSACTIONS;
	localparam signed [31:0] PAYLOAD_W = 285;
	localparam signed [31:0] BANK_SLOTS = N / NUM_BANKS;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	function automatic signed [31:0] bank_of;
		input reg [IW - 1:0] id;
		bank_of = (NUM_BANKS > 1 ? sv2v_cast_32_signed(sv2v_cast_32(id) % NUM_BANKS) : 0);
	endfunction
	generate
		if ((NUM_BANKS < 1) || ((NUM_BANKS & (NUM_BANKS - 1)) != 0)) begin : gen_bad_banks
			initial $display("Error [elaboration] /tmp/formal_axi_monitor_trans_mgr_banked/axi_monitor_trans_mgr.sv:201:9 - axi_monitor_trans_mgr.gen_bad_banks\n msg: ", "axi_monitor_trans_mgr: NUM_BANKS=%0d must be a power of 2.", NUM_BANKS);
		end
		if ((NUM_BANKS > 1) && ((MAX_TRANSACTIONS % NUM_BANKS) != 0)) begin : gen_ragged_banks
			initial $display("Error [elaboration] /tmp/formal_axi_monitor_trans_mgr_banked/axi_monitor_trans_mgr.sv:204:9 - axi_monitor_trans_mgr.gen_ragged_banks\n msg: ", "axi_monitor_trans_mgr: MAX_TRANSACTIONS=%0d is not divisible by NUM_BANKS=%0d.", MAX_TRANSACTIONS, NUM_BANKS);
		end
		if (((NUM_BANKS > 1) && !IS_READ) && !USE_WDATA_ORDER_Q) begin : gen_banked_wr_needs_widq
			initial $display("Error [elaboration] /tmp/formal_axi_monitor_trans_mgr_banked/axi_monitor_trans_mgr.sv:220:9 - axi_monitor_trans_mgr.gen_banked_wr_needs_widq\n msg: ", "axi_monitor_trans_mgr: NUM_BANKS=%0d on a write monitor requires USE_WDATA_ORDER_Q=1 (the WID-less fallback double-counts one W beat across banks).", NUM_BANKS);
		end
		if (ID_WIDTH > 8) begin : gen_id_width_unsupported
			initial $display("Error [elaboration] /tmp/formal_axi_monitor_trans_mgr_banked/axi_monitor_trans_mgr.sv:257:9 - axi_monitor_trans_mgr.gen_id_width_unsupported\n msg: ", "axi_monitor_trans_mgr: ID_WIDTH=%0d exceeds the 8-bit id field in bus_transaction_t; the table and the CAM key would disagree. Widen bus_transaction_t.id or reduce ID_WIDTH.", ID_WIDTH);
		end
	endgenerate
	reg [N - 1:0] addr_match_oh;
	reg [N - 1:0] data_match_oh;
	reg [N - 1:0] resp_match_oh;
	reg [N - 1:0] cam_data_match_first_oh;
	reg [N - 1:0] free_oh;
	reg [N - 1:0] addr_alloc_oh;
	reg [N - 1:0] data_alloc_oh;
	reg [N - 1:0] resp_alloc_oh;
	reg [N - 1:0] cam_entry_valid;
	reg [(N * 285) - 1:0] cam_entry_payload;
	wire [N - 1:0] cam_entry_we;
	wire [N - 1:0] cam_entry_valid_next;
	wire [IW - 1:0] cam_entry_id_next [0:N - 1];
	wire [284:0] cam_entry_payload_next [0:N - 1];
	wire addr_wants_alloc;
	reg data_wants_alloc;
	reg resp_wants_alloc;
	reg [N - 1:0] w_addr_bank_mask;
	reg [N - 1:0] w_data_bank_mask;
	reg [N - 1:0] w_resp_bank_mask;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin
					w_addr_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(cmd_id));
					w_data_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(data_id));
					w_resp_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(resp_id));
				end
		end
	end
	wire [BANK_SLOTS - 1:0] wb_addr_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_resp_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_first [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_free [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_addr_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_resp_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_entry_valid [0:NUM_BANKS - 1];
	wire [(BANK_SLOTS * 285) - 1:0] wb_entry_payload [0:NUM_BANKS - 1];
	reg [BANK_SLOTS - 1:0] wb_entry_we [0:NUM_BANKS - 1];
	reg [BANK_SLOTS - 1:0] wb_valid_next [0:NUM_BANKS - 1];
	reg [(BANK_SLOTS * IW) - 1:0] wb_id_next [0:NUM_BANKS - 1];
	reg [(BANK_SLOTS * 285) - 1:0] wb_payload_next [0:NUM_BANKS - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < BANK_SLOTS; i = i + 1)
						begin
							wb_entry_we[b][i] = cam_entry_we[(b * BANK_SLOTS) + i];
							wb_valid_next[b][i] = cam_entry_valid_next[(b * BANK_SLOTS) + i];
							wb_id_next[b][((BANK_SLOTS - 1) - i) * IW+:IW] = cam_entry_id_next[(b * BANK_SLOTS) + i];
							wb_payload_next[b][((BANK_SLOTS - 1) - i) * 285+:285] = cam_entry_payload_next[(b * BANK_SLOTS) + i];
						end
				end
		end
	end
	genvar _gv_gb_1;
	generate
		for (_gv_gb_1 = 0; _gv_gb_1 < NUM_BANKS; _gv_gb_1 = _gv_gb_1 + 1) begin : g_cam_bank
			localparam gb = _gv_gb_1;
			monitor_trans_cam #(
				.DEPTH(BANK_SLOTS),
				.ID_WIDTH(IW),
				.PAYLOAD_WIDTH(PAYLOAD_W)
			) u_cam(
				.clk(aclk),
				.rst_n(aresetn),
				.clear(clear),
				.lookup_addr_id(cmd_id),
				.lookup_data_id(data_id),
				.lookup_resp_id(resp_id),
				.addr_match_oh(wb_addr_match[gb]),
				.data_match_oh(wb_data_match[gb]),
				.resp_match_oh(wb_resp_match[gb]),
				.data_match_first_oh(wb_data_first[gb]),
				.free_oh(wb_free[gb]),
				.addr_wants_alloc(addr_wants_alloc && (bank_of(cmd_id) == gb)),
				.data_wants_alloc(data_wants_alloc && (bank_of(data_id) == gb)),
				.resp_wants_alloc(resp_wants_alloc && (bank_of(resp_id) == gb)),
				.addr_alloc_mask({BANK_SLOTS {1'b1}}),
				.data_alloc_mask({BANK_SLOTS {1'b1}}),
				.resp_alloc_mask({BANK_SLOTS {1'b1}}),
				.addr_alloc_oh(wb_addr_alloc[gb]),
				.data_alloc_oh(wb_data_alloc[gb]),
				.resp_alloc_oh(wb_resp_alloc[gb]),
				.entry_we(wb_entry_we[gb]),
				.entry_valid_next(wb_valid_next[gb]),
				.entry_id_next(wb_id_next[gb]),
				.entry_payload_next(wb_payload_next[gb]),
				.entry_valid(wb_entry_valid[gb]),
				.entry_id(),
				.entry_payload(wb_entry_payload[gb])
			);
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				begin : sv2v_autoblock_5
					reg signed [31:0] i;
					for (i = 0; i < BANK_SLOTS; i = i + 1)
						begin
							addr_match_oh[(b * BANK_SLOTS) + i] = wb_addr_match[b][i];
							data_match_oh[(b * BANK_SLOTS) + i] = wb_data_match[b][i];
							resp_match_oh[(b * BANK_SLOTS) + i] = wb_resp_match[b][i];
							cam_data_match_first_oh[(b * BANK_SLOTS) + i] = wb_data_first[b][i];
							free_oh[(b * BANK_SLOTS) + i] = wb_free[b][i];
							addr_alloc_oh[(b * BANK_SLOTS) + i] = wb_addr_alloc[b][i];
							data_alloc_oh[(b * BANK_SLOTS) + i] = wb_data_alloc[b][i];
							resp_alloc_oh[(b * BANK_SLOTS) + i] = wb_resp_alloc[b][i];
							cam_entry_valid[(b * BANK_SLOTS) + i] = wb_entry_valid[b][i];
							cam_entry_payload[((N - 1) - ((b * BANK_SLOTS) + i)) * 285+:285] = wb_entry_payload[b][((BANK_SLOTS - 1) - i) * 285+:285];
						end
				end
		end
	end
	localparam signed [31:0] AGEW = (N > 1 ? $clog2(N) : 1);
	reg [AGEW - 1:0] r_age [0:N - 1];
	reg [(N * AGEW) - 1:0] w_age_flat;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_age_flat[i * AGEW+:AGEW] = r_age[i];
		end
	end
	function automatic [N - 1:0] pick_oldest;
		input reg [N - 1:0] cand;
		input reg [(N * AGEW) - 1:0] ages;
		reg [N - 1:0] res;
		reg lose;
		begin
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					begin
						lose = 1'b0;
						begin : sv2v_autoblock_8
							reg signed [31:0] j;
							for (j = 0; j < N; j = j + 1)
								if (((((i / BANK_SLOTS) == (j / BANK_SLOTS)) && (j != i)) && cand[j]) && ((ages[j * AGEW+:AGEW] < ages[i * AGEW+:AGEW]) || ((ages[j * AGEW+:AGEW] == ages[i * AGEW+:AGEW]) && (j < i))))
									lose = 1'b1;
						end
						res[i] = cand[i] && !lose;
					end
			end
			pick_oldest = res;
		end
	endfunction
	(* keep = "true" *) reg [N - 1:0] w_data_state_pred_oh;
	wire [N - 1:0] w_data_state_first_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_9
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_state_pred_oh[i] = ((cam_entry_valid[i] && ((cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1) || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h2))) && cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
		end
	end
	localparam signed [31:0] SLOTW = (N > 1 ? $clog2(N) : 1);
	localparam signed [31:0] WQW = (N > 1 ? $clog2(N + 1) : 1);
	reg [IW - 1:0] r_widq [0:N - 1];
	reg [WQW - 1:0] r_widq_count;
	wire [IW - 1:0] w_widq_head;
	reg [N - 1:0] w_widq_cand_oh;
	wire w_widq_push;
	wire w_widq_pop;
	wire w_widq_head_dead;
	wire w_widq_bypass;
	assign w_widq_push = ((!IS_READ && USE_WDATA_ORDER_Q) && cmd_valid) && cmd_ready;
	assign w_widq_bypass = (r_widq_count == {WQW {1'sb0}}) && w_widq_push;
	assign w_widq_head = (w_widq_bypass ? cmd_id : r_widq[0]);
	reg [N - 1:0] w_freeing_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_widq_cand_oh = 1'sb0;
		if ((!IS_READ && USE_WDATA_ORDER_Q) && ((r_widq_count != {WQW {1'sb0}}) || w_widq_bypass)) begin : sv2v_autoblock_10
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_widq_cand_oh[i] = (w_data_state_pred_oh[i] && (cam_entry_payload[(((N - 1) - i) * 285) + 242-:8] == w_widq_head)) && !w_freeing_oh[i];
		end
	end
	assign w_widq_head_dead = (r_widq_count != {WQW {1'sb0}}) && !(|w_widq_cand_oh);
	assign w_widq_pop = (r_widq_count != {WQW {1'sb0}}) && (((data_valid && data_ready) && data_last) || w_widq_head_dead);
	assign w_data_state_first_oh = (USE_WDATA_ORDER_Q ? pick_oldest(w_widq_cand_oh, w_age_flat) : pick_oldest(w_data_state_pred_oh, w_age_flat));
	function automatic signed [WQW - 1:0] sv2v_cast_6C857_signed;
		input reg signed [WQW - 1:0] inp;
		sv2v_cast_6C857_signed = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_widq_count <= 1'sb0;
			begin : sv2v_autoblock_11
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_widq[i] <= 1'sb0;
			end
		end
		else if (clear) begin
			r_widq_count <= 1'sb0;
			begin : sv2v_autoblock_12
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_widq[i] <= 1'sb0;
			end
		end
		else if (!IS_READ && USE_WDATA_ORDER_Q) begin : sv2v_autoblock_13
			reg [WQW - 1:0] v_cnt;
			v_cnt = r_widq_count;
			if (w_widq_pop && (v_cnt != {WQW {1'sb0}})) begin
				begin : sv2v_autoblock_14
					reg signed [31:0] i;
					for (i = 0; i < (N - 1); i = i + 1)
						r_widq[i] <= r_widq[i + 1];
				end
				v_cnt = v_cnt - 1'b1;
			end
			if (w_widq_push && (v_cnt < sv2v_cast_6C857_signed(N))) begin
				r_widq[v_cnt[SLOTW - 1:0]] <= cmd_id;
				v_cnt = v_cnt + 1'b1;
			end
			r_widq_count <= v_cnt;
		end
	reg [N - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_15
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
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_16
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_freeing_oh[i] = cam_entry_valid[i] && w_can_cleanup[i];
		end
	end
	reg [N - 1:0] w_addr_pend_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_17
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_addr_pend_oh[i] = (addr_match_oh[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !w_freeing_oh[i];
		end
	end
	reg [N - 1:0] w_addr_alloc_mirror_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_alloc_mirror_oh = 1'sb0;
		if (addr_wants_alloc) begin : sv2v_autoblock_18
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (((w_addr_alloc_mirror_oh == {N {1'sb0}}) && free_oh[i]) && w_addr_bank_mask[i])
					w_addr_alloc_mirror_oh[i] = 1'b1;
		end
	end
	wire [N - 1:0] addr_update_oh;
	wire [N - 1:0] data_update_oh;
	wire [N - 1:0] resp_update_oh;
	reg [N - 1:0] w_data_cmd_bypass_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_data_cmd_bypass_oh = 1'sb0;
		if (((!IS_READ && data_valid) && data_ready) && !(|w_data_state_pred_oh)) begin : sv2v_autoblock_19
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_cmd_bypass_oh[i] = w_addr_alloc_mirror_oh[i] || ((cmd_valid && addr_update_oh[i]) && (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1));
		end
	end
	wire addr_hit_any;
	wire data_hit_any;
	wire resp_hit_any;
	assign addr_hit_any = |w_addr_pend_oh;
	assign resp_hit_any = |resp_match_oh;
	assign data_hit_any = (IS_READ ? |data_match_oh : |w_data_state_pred_oh || |w_data_cmd_bypass_oh);
	function automatic signed [31:0] monitor_common_pkg_cmd_entry_reserve;
		input reg signed [31:0] max_transactions;
		monitor_common_pkg_cmd_entry_reserve = (max_transactions >= 16 ? 2 : 0);
	endfunction
	localparam signed [31:0] CMD_ENTRY_RESERVE = monitor_common_pkg_cmd_entry_reserve(N);
	reg [$clog2(N + 1) - 1:0] w_cmd_entry_count;
	function automatic signed [$clog2(N + 1) - 1:0] sv2v_cast_54CAC_signed;
		input reg signed [$clog2(N + 1) - 1:0] inp;
		sv2v_cast_54CAC_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_cmd_entry_count = 1'sb0;
		begin : sv2v_autoblock_20
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i] && (cam_entry_payload[(((N - 1) - i) * 285) + 283] || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1)))
					w_cmd_entry_count = w_cmd_entry_count + sv2v_cast_54CAC_signed(1);
		end
	end
	wire w_cmd_headroom;
	assign w_cmd_headroom = (CMD_ENTRY_RESERVE == 0) || (w_cmd_entry_count < sv2v_cast_54CAC_signed(N - CMD_ENTRY_RESERVE));
	assign addr_wants_alloc = (cmd_valid && !addr_hit_any) && w_cmd_headroom;
	always @(*) begin
		if (_sv2v_0)
			;
		if (IS_READ)
			data_wants_alloc = (data_valid && data_ready) && !data_hit_any;
		else
			data_wants_alloc = ((data_valid && data_ready) && !IS_AXI) && !data_hit_any;
		resp_wants_alloc = ((!IS_READ && resp_valid) && resp_ready) && !resp_hit_any;
	end
	reg [N - 1:0] w_data_cand_open;
	reg [N - 1:0] w_data_cand_any;
	reg [N - 1:0] w_resp_cand_open;
	reg [N - 1:0] w_resp_cand_any;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_21
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin
					w_data_cand_any[i] = data_match_oh[i] && !w_freeing_oh[i];
					w_data_cand_open[i] = w_data_cand_any[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
					w_resp_cand_any[i] = resp_match_oh[i] && !w_freeing_oh[i];
					w_resp_cand_open[i] = w_resp_cand_any[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 280];
				end
		end
	end
	assign addr_update_oh = pick_oldest(w_addr_pend_oh, w_age_flat);
	assign data_update_oh = (IS_READ ? (|w_data_cand_open ? pick_oldest(w_data_cand_open, w_age_flat) : (data_last ? pick_oldest(w_data_cand_any, w_age_flat) : {N {1'sb0}})) : w_data_state_first_oh | w_data_cmd_bypass_oh);
	assign resp_update_oh = (|w_resp_cand_open ? pick_oldest(w_resp_cand_open, w_age_flat) : pick_oldest(w_resp_cand_any, w_age_flat));
	reg [5:0] w_addr_chan_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
	end
	wire cmd_handshake;
	assign cmd_handshake = cmd_valid && cmd_ready;
	reg [N - 1:0] r_rpt_stale_mask;
	always @(posedge aclk)
		if (!aresetn)
			r_rpt_stale_mask <= 1'sb0;
		else if (clear)
			r_rpt_stale_mask <= 1'sb0;
		else begin : sv2v_autoblock_22
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (w_freeing_oh[i])
					r_rpt_stale_mask[i] <= 1'b1;
				else if (!i_event_reported_flags[i])
					r_rpt_stale_mask[i] <= 1'b0;
		end
	wire w_addr_alloc_fire;
	wire w_data_alloc_fire;
	wire w_resp_alloc_fire;
	assign w_addr_alloc_fire = |addr_alloc_oh;
	assign w_data_alloc_fire = |data_alloc_oh;
	assign w_resp_alloc_fire = |resp_alloc_oh;
	reg [AGEW - 1:0] w_age_addr_new;
	reg [AGEW - 1:0] w_age_data_new;
	reg [AGEW - 1:0] w_age_resp_new;
	function automatic [AGEW - 1:0] sv2v_cast_D1065;
		input reg [AGEW - 1:0] inp;
		sv2v_cast_D1065 = inp;
	endfunction
	always @(*) begin : sv2v_autoblock_23
		reg signed [31:0] surv_bank [0:NUM_BANKS - 1];
		reg signed [31:0] ab;
		reg signed [31:0] db;
		reg signed [31:0] rb;
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_24
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				surv_bank[b] = 0;
		end
		begin : sv2v_autoblock_25
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i] && !w_freeing_oh[i])
					surv_bank[i / BANK_SLOTS] = surv_bank[i / BANK_SLOTS] + 1;
		end
		ab = bank_of(cmd_id);
		db = bank_of(data_id);
		rb = bank_of(resp_id);
		w_age_addr_new = sv2v_cast_D1065(surv_bank[ab]);
		w_age_data_new = sv2v_cast_D1065(surv_bank[db] + (w_addr_alloc_fire && (ab == db) ? 1 : 0));
		w_age_resp_new = sv2v_cast_D1065((surv_bank[rb] + (w_addr_alloc_fire && (ab == rb) ? 1 : 0)) + (w_data_alloc_fire && (db == rb) ? 1 : 0));
	end
	reg [AGEW - 1:0] w_age_next [0:N - 1];
	function automatic signed [AGEW - 1:0] sv2v_cast_D1065_signed;
		input reg signed [AGEW - 1:0] inp;
		sv2v_cast_D1065_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_26
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin : sv2v_autoblock_27
					reg signed [31:0] dec;
					dec = 0;
					w_age_next[i] = r_age[i];
					if (addr_alloc_oh[i])
						w_age_next[i] = w_age_addr_new;
					else if (data_alloc_oh[i])
						w_age_next[i] = w_age_data_new;
					else if (resp_alloc_oh[i])
						w_age_next[i] = w_age_resp_new;
					else if (cam_entry_valid[i] && !w_freeing_oh[i]) begin
						begin : sv2v_autoblock_28
							reg signed [31:0] j;
							for (j = 0; j < N; j = j + 1)
								if ((((i / BANK_SLOTS) == (j / BANK_SLOTS)) && w_freeing_oh[j]) && (r_age[j] < r_age[i]))
									dec = dec + 1;
						end
						w_age_next[i] = r_age[i] - sv2v_cast_D1065_signed(dec);
					end
				end
		end
	end
	genvar _gv_ga_1;
	generate
		for (_gv_ga_1 = 0; _gv_ga_1 < N; _gv_ga_1 = _gv_ga_1 + 1) begin : g_age
			localparam ga = _gv_ga_1;
			always @(posedge aclk)
				if (!aresetn)
					r_age[ga] <= 1'sb0;
				else if (clear)
					r_age[ga] <= 1'sb0;
				else
					r_age[ga] <= w_age_next[ga];
		end
	endgenerate
	genvar _gv_gi_2;
	localparam [7:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 8'h02;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_PROTOCOL = 8'h04;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_DECERR = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 8'h03;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 8'h02;
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
						next[15-:8] = next[15-:8] + 1'b1;
						next[183-:32] = 1'sb0;
						if (next[277-:3] != 3'h4) begin
							if ((IS_READ || next[283]) || (next[277-:3] != 3'h1))
								next[277-:3] = 3'h2;
						end
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
						else if (data_last || (next[15-:8] == next[23-:8])) begin
							next[281] = 1'b1;
							next[87-:32] = timestamp;
						end
						next_we = 1'b1;
					end
					else if (data_alloc_oh[gi]) begin
						next[284] = 1'b1;
						next[283] = 1'b0;
						next[279] = 1'b0;
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
						next[283] = 1'b0;
						next[279] = 1'b0;
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
				if ((((i_timeout_detected[gi] && cam_entry_valid[gi]) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h3)) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h5)) begin
					next[277-:3] = 3'h4;
					if (!cam_entry_payload[(((N - 1) - gi) * 285) + 283])
						next[7-:8] = monitor_amba4_pkg_EVT_CMD_TIMEOUT;
					else if (cam_entry_payload[(((N - 1) - gi) * 285) + 281] && !cam_entry_payload[(((N - 1) - gi) * 285) + 280])
						next[7-:8] = monitor_amba4_pkg_EVT_RESP_TIMEOUT;
					else
						next[7-:8] = monitor_amba4_pkg_EVT_DATA_TIMEOUT;
					next_we = 1'b1;
				end
				if (cam_entry_valid[gi] && w_can_cleanup[gi]) begin
					next[284] = 1'b0;
					next_we = 1'b1;
				end
				if ((((i_event_reported_flags[gi] && !r_rpt_stale_mask[gi]) && cam_entry_valid[gi]) && !w_can_cleanup[gi]) && !cam_entry_payload[(((N - 1) - gi) * 285) + 279]) begin
					next[279] = 1'b1;
					next_we = 1'b1;
				end
			end
			assign cam_entry_we[gi] = next_we;
			assign cam_entry_valid_next[gi] = next[284];
			assign cam_entry_id_next[gi] = next_id;
			assign cam_entry_payload_next[gi] = next;
		end
	endgenerate
	assign trans_table = cam_entry_payload;
	reg [7:0] r_active_count;
	reg [$clog2(N + 1) - 1:0] w_occupancy;
	always @(*) begin
		if (_sv2v_0)
			;
		w_occupancy = 1'sb0;
		begin : sv2v_autoblock_29
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
			begin : sv2v_autoblock_30
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_trans_table_prev[((N - 1) - i) * 285+:285] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= cam_entry_payload;
			begin : sv2v_autoblock_31
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_state_change[i] <= (cam_entry_payload[(((N - 1) - i) * 285) + 284] && r_trans_table_prev[(((N - 1) - i) * 285) + 284]) && (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] != r_trans_table_prev[(((N - 1) - i) * 285) + 277-:3]);
			end
		end
	assign state_change = r_state_change;
	reg f_past_ok;
	initial f_past_ok = 1'b0;
	always @(posedge aclk) f_past_ok <= aresetn;
	always @(posedge aclk)
		if ((IS_READ && aresetn) && f_past_ok) begin : sv2v_autoblock_32
			reg signed [31:0] fi;
			for (fi = 0; fi < N; fi = fi + 1)
				if (cam_entry_valid[fi]) begin : ap_no_reopened_complete
					assert (!((cam_entry_payload[(((N - 1) - fi) * 285) + 277-:3] == 3'h2) && cam_entry_payload[(((N - 1) - fi) * 285) + 281])) ;
				end
		end
	always @(posedge aclk)
		if ((!IS_READ && aresetn) && f_past_ok) begin : sv2v_autoblock_33
			reg signed [31:0] fi;
			for (fi = 0; fi < N; fi = fi + 1)
				if (cam_entry_valid[fi]) begin : ap_wr_data_phase_has_cmd
					assert (!((cam_entry_payload[(((N - 1) - fi) * 285) + 277-:3] == 3'h2) && !cam_entry_payload[(((N - 1) - fi) * 285) + 283])) ;
				end
		end
	always @(posedge aclk)
		if (aresetn && f_past_ok) begin : ap_bypass_alloc_mirror
			assert (w_addr_alloc_mirror_oh == addr_alloc_oh) ;
		end
	always @(posedge aclk)
		if ((aresetn && f_past_ok) && (CMD_ENTRY_RESERVE > 0)) begin : ap_cmd_entry_cap
			assert (w_cmd_entry_count <= sv2v_cast_54CAC_signed(N - CMD_ENTRY_RESERVE)) ;
		end
	initial _sv2v_0 = 0;
endmodule
