module scoria_global_timers (
	mc_clk,
	mc_rst_n,
	t_faw_i,
	t_rrd_i,
	t_wtr_global_i,
	t_rtw_i,
	t_ccd_i,
	evt_act_i,
	evt_act_rank_i,
	evt_rd_i,
	evt_wr_i,
	tfaw_window_ok_o,
	trrd_window_ok_o,
	twtr_global_ok_o,
	trtw_window_ok_o,
	tccd_window_ok_o,
	obs_faw_nz_o,
	obs_trrd_nz_o,
	obs_twtr_nz_o,
	obs_trtw_nz_o,
	obs_tccd_nz_o
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_RANKS = 1;
	parameter signed [31:0] NUM_BANKS = 8;
	parameter signed [31:0] RKW = (NUM_RANKS > 1 ? $clog2(NUM_RANKS) : 1);
	parameter signed [31:0] BKW = $clog2(NUM_BANKS);
	input wire mc_clk;
	input wire mc_rst_n;
	input wire [7:0] t_faw_i;
	input wire [7:0] t_rrd_i;
	input wire [7:0] t_wtr_global_i;
	input wire [7:0] t_rtw_i;
	input wire [7:0] t_ccd_i;
	input wire evt_act_i;
	input wire [RKW - 1:0] evt_act_rank_i;
	input wire evt_rd_i;
	input wire evt_wr_i;
	output reg [NUM_RANKS - 1:0] tfaw_window_ok_o;
	output reg [NUM_RANKS - 1:0] trrd_window_ok_o;
	output reg twtr_global_ok_o;
	output reg trtw_window_ok_o;
	output reg tccd_window_ok_o;
	output reg [NUM_RANKS - 1:0] obs_faw_nz_o;
	output reg [NUM_RANKS - 1:0] obs_trrd_nz_o;
	output reg obs_twtr_nz_o;
	output reg obs_trtw_nz_o;
	output reg obs_tccd_nz_o;
	reg [((NUM_RANKS * 4) * 8) - 1:0] r_faw_slots;
	reg [(NUM_RANKS * 8) - 1:0] r_trrd_cnt;
	reg [7:0] r_twtr_cnt;
	reg [7:0] r_trtw_cnt;
	reg [7:0] r_tccd_cnt;
	reg [(NUM_RANKS * 2) - 1:0] w_slot_pick;
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	always @(*) begin : sv2v_autoblock_1
		reg [7:0] slot_min;
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				begin
					slot_min = 8'hff;
					w_slot_pick[k * 2+:2] = 2'd0;
					begin : sv2v_autoblock_3
						reg [31:0] i;
						for (i = 0; i < 4; i = i + 1)
							if (r_faw_slots[((k * 4) + i) * 8+:8] < slot_min) begin
								slot_min = r_faw_slots[((k * 4) + i) * 8+:8];
								w_slot_pick[k * 2+:2] = sv2v_cast_2(i);
							end
					end
				end
		end
	end
	reg [NUM_RANKS - 1:0] w_act_rank;
	wire w_evt_col;
	function automatic [RKW - 1:0] sv2v_cast_6B7F8;
		input reg [RKW - 1:0] inp;
		sv2v_cast_6B7F8 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				w_act_rank[k] = evt_act_i && (sv2v_cast_6B7F8(k) == evt_act_rank_i);
		end
	end
	assign w_evt_col = evt_rd_i || evt_wr_i;
	reg [((NUM_RANKS * 4) * 8) - 1:0] w_faw_nxt;
	reg [(NUM_RANKS * 8) - 1:0] w_trrd_nxt;
	reg [7:0] w_twtr_nxt;
	reg [7:0] w_trtw_nxt;
	reg [7:0] w_tccd_nxt;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				begin
					begin : sv2v_autoblock_6
						reg [31:0] i;
						for (i = 0; i < 4; i = i + 1)
							w_faw_nxt[((k * 4) + i) * 8+:8] = (r_faw_slots[((k * 4) + i) * 8+:8] > 8'd0 ? r_faw_slots[((k * 4) + i) * 8+:8] - 8'd1 : 8'd0);
					end
					if (w_act_rank[k])
						w_faw_nxt[((k * 4) + w_slot_pick[k * 2+:2]) * 8+:8] = t_faw_i;
					w_trrd_nxt[k * 8+:8] = (w_act_rank[k] ? t_rrd_i : (r_trrd_cnt[k * 8+:8] > 8'd0 ? r_trrd_cnt[k * 8+:8] - 8'd1 : 8'd0));
				end
		end
		w_twtr_nxt = (evt_wr_i ? t_wtr_global_i : (r_twtr_cnt > 8'd0 ? r_twtr_cnt - 8'd1 : 8'd0));
		w_trtw_nxt = (evt_rd_i ? t_rtw_i : (r_trtw_cnt > 8'd0 ? r_trtw_cnt - 8'd1 : 8'd0));
		w_tccd_nxt = (w_evt_col ? t_ccd_i : (r_tccd_cnt > 8'd0 ? r_tccd_cnt - 8'd1 : 8'd0));
	end
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n) begin
			r_faw_slots <= 1'sb0;
			r_trrd_cnt <= 1'sb0;
			r_twtr_cnt <= 8'd0;
			r_trtw_cnt <= 8'd0;
			r_tccd_cnt <= 8'd0;
		end
		else begin
			r_faw_slots <= w_faw_nxt;
			r_trrd_cnt <= w_trrd_nxt;
			r_twtr_cnt <= w_twtr_nxt;
			r_trtw_cnt <= w_trtw_nxt;
			r_tccd_cnt <= w_tccd_nxt;
		end
	reg [NUM_RANKS - 1:0] w_tfaw_ok_nxt;
	reg [NUM_RANKS - 1:0] w_trrd_ok_nxt;
	reg w_twtr_ok_nxt;
	reg w_trtw_ok_nxt;
	reg w_tccd_ok_nxt;
	always @(*) begin : sv2v_autoblock_7
		reg any_free_all;
		reg any_free_other;
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				begin
					any_free_all = 1'b0;
					any_free_other = 1'b0;
					begin : sv2v_autoblock_9
						reg [31:0] i;
						for (i = 0; i < 4; i = i + 1)
							if (r_faw_slots[((k * 4) + i) * 8+:8] <= 8'd1) begin
								any_free_all = 1'b1;
								if (sv2v_cast_2(i) != w_slot_pick[k * 2+:2])
									any_free_other = 1'b1;
							end
					end
					w_tfaw_ok_nxt[k] = (w_act_rank[k] ? any_free_other || (t_faw_i == 8'd0) : any_free_all);
					w_trrd_ok_nxt[k] = (w_act_rank[k] ? t_rrd_i == 8'd0 : r_trrd_cnt[k * 8+:8] <= 8'd1);
				end
		end
		w_twtr_ok_nxt = (evt_wr_i ? t_wtr_global_i == 8'd0 : r_twtr_cnt <= 8'd1);
		w_trtw_ok_nxt = (evt_rd_i ? t_rtw_i == 8'd0 : r_trtw_cnt <= 8'd1);
		w_tccd_ok_nxt = (w_evt_col ? t_ccd_i == 8'd0 : r_tccd_cnt <= 8'd1);
	end
	reg [NUM_RANKS - 1:0] w_tfaw_ok;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_10
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				begin
					w_tfaw_ok[k] = 1'b0;
					begin : sv2v_autoblock_11
						reg [31:0] i;
						for (i = 0; i < 4; i = i + 1)
							if (r_faw_slots[((k * 4) + i) * 8+:8] == 8'd0)
								w_tfaw_ok[k] = 1'b1;
					end
				end
		end
	end
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n) begin
			tfaw_window_ok_o <= 1'sb1;
			trrd_window_ok_o <= 1'sb1;
			twtr_global_ok_o <= 1'b1;
			trtw_window_ok_o <= 1'b1;
			tccd_window_ok_o <= 1'b1;
		end
		else begin
			tfaw_window_ok_o <= w_tfaw_ok_nxt;
			trrd_window_ok_o <= w_trrd_ok_nxt;
			twtr_global_ok_o <= w_twtr_ok_nxt;
			trtw_window_ok_o <= w_trtw_ok_nxt;
			tccd_window_ok_o <= w_tccd_ok_nxt;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_12
			reg [31:0] k;
			for (k = 0; k < NUM_RANKS; k = k + 1)
				begin
					obs_faw_nz_o[k] = !w_tfaw_ok[k];
					obs_trrd_nz_o[k] = r_trrd_cnt[k * 8+:8] != 8'd0;
				end
		end
		obs_twtr_nz_o = r_twtr_cnt != 8'd0;
		obs_trtw_nz_o = r_trtw_cnt != 8'd0;
		obs_tccd_nz_o = r_tccd_cnt != 8'd0;
	end
	initial _sv2v_0 = 0;
endmodule
module scoria_cmd_arbiter (
	aclk,
	aresetn,
	page_policy_i,
	sched_order_mode_i,
	sched_row_sel_i,
	sched_col_sel_i,
	sched_access_pref_i,
	sched_wr_high_wm_i,
	sched_wr_batch_max_i,
	sched_wr_low_wm_i,
	sched_prio_sub_i,
	sched_qos_en_i,
	rd_sch_qos_i,
	wr_sch_qos_i,
	rd_sch_age_exceed_i,
	wr_sch_age_exceed_i,
	rd_sch_head_rel_i,
	wr_sch_head_rel_i,
	ap_mode_en_i,
	ap_close_i,
	timeout_pre_req_i,
	timeout_pre_bank_i,
	init_done_i,
	init_cmd_valid_i,
	init_cmd_op_i,
	init_cmd_bank_i,
	init_cmd_row_i,
	refresh_req_i,
	refresh_drain_i,
	refresh_kind_i,
	refresh_bank_i,
	refresh_grant_o,
	t_rfc_i,
	zq_req_i,
	zq_grant_o,
	t_zqcs_i,
	t_rfc_pb_i,
	bank_act_ready_i,
	bank_rdwr_ready_i,
	bank_pre_ready_i,
	bank_act_ready_la_i,
	bank_rdwr_ready_la_i,
	bank_pre_ready_la_i,
	bank_row_active_i,
	bank_open_row_i,
	tfaw_ok_i,
	trrd_ok_i,
	twtr_ok_i,
	trtw_ok_i,
	tccd_ok_i,
	t_ccd_i,
	wr_sch_valid_i,
	wr_sch_bank_i,
	wr_sch_row_i,
	wr_sch_col_i,
	wr_sch_older_i,
	wr_commit_ready_i,
	wr_commit_valid_o,
	wr_commit_slot_o,
	rd_sch_valid_i,
	rd_sch_bank_i,
	rd_sch_row_i,
	rd_sch_col_i,
	rd_sch_older_i,
	rd_issue_ready_i,
	rd_issue_valid_o,
	rd_issue_slot_o,
	evt_act_o,
	evt_rd_o,
	evt_wr_o,
	evt_pre_o,
	evt_ap_o,
	evt_rank_o,
	evt_bank_o,
	evt_row_o,
	cmd_valid_o,
	cmd_ready_i,
	cmd_op_o,
	cmd_rank_o,
	cmd_bank_o,
	cmd_row_o,
	cmd_col_o,
	cmd_ap_o,
	stall_bp_o,
	stall_refresh_o,
	stall_turnaround_o,
	stall_tccd_o,
	stall_actlimit_o,
	stall_banktimer_o,
	stall_noreq_o,
	stall_zq_o
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_RANKS = 1;
	parameter signed [31:0] NUM_BANKS = 8;
	parameter signed [31:0] ROW_WIDTH = 14;
	parameter signed [31:0] COL_WIDTH = 10;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] NUM_ENTRIES = 8;
	parameter signed [31:0] AGE_WIDTH = 16;
	parameter signed [31:0] RKW = (NUM_RANKS > 1 ? $clog2(NUM_RANKS) : 1);
	parameter signed [31:0] BKW = $clog2(NUM_BANKS);
	parameter signed [31:0] PTRW = $clog2(NUM_ENTRIES);
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [1:0] page_policy_i;
	input wire [1:0] sched_order_mode_i;
	input wire [1:0] sched_row_sel_i;
	input wire [1:0] sched_col_sel_i;
	input wire [1:0] sched_access_pref_i;
	input wire [7:0] sched_wr_high_wm_i;
	input wire [7:0] sched_wr_batch_max_i;
	input wire [7:0] sched_wr_low_wm_i;
	input wire [1:0] sched_prio_sub_i;
	input wire sched_qos_en_i;
	input wire [(NUM_ENTRIES * 4) - 1:0] rd_sch_qos_i;
	input wire [(NUM_ENTRIES * 4) - 1:0] wr_sch_qos_i;
	input wire [NUM_ENTRIES - 1:0] rd_sch_age_exceed_i;
	input wire [NUM_ENTRIES - 1:0] wr_sch_age_exceed_i;
	input wire [AGE_WIDTH - 1:0] rd_sch_head_rel_i;
	input wire [AGE_WIDTH - 1:0] wr_sch_head_rel_i;
	input wire ap_mode_en_i;
	input wire [NUM_BANKS - 1:0] ap_close_i;
	input wire timeout_pre_req_i;
	input wire [BKW - 1:0] timeout_pre_bank_i;
	input wire init_done_i;
	input wire init_cmd_valid_i;
	input wire [3:0] init_cmd_op_i;
	input wire [BKW - 1:0] init_cmd_bank_i;
	input wire [ROW_WIDTH - 1:0] init_cmd_row_i;
	input wire refresh_req_i;
	input wire refresh_drain_i;
	input wire refresh_kind_i;
	input wire [BKW - 1:0] refresh_bank_i;
	output wire refresh_grant_o;
	input wire [15:0] t_rfc_i;
	input wire zq_req_i;
	output wire zq_grant_o;
	input wire [15:0] t_zqcs_i;
	input wire [7:0] t_rfc_pb_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_act_ready_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_rdwr_ready_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_pre_ready_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_act_ready_la_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_rdwr_ready_la_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_pre_ready_la_i;
	input wire [(NUM_RANKS * NUM_BANKS) - 1:0] bank_row_active_i;
	input wire [((NUM_RANKS * NUM_BANKS) * ROW_WIDTH) - 1:0] bank_open_row_i;
	input wire [NUM_RANKS - 1:0] tfaw_ok_i;
	input wire [NUM_RANKS - 1:0] trrd_ok_i;
	input wire twtr_ok_i;
	input wire trtw_ok_i;
	input wire tccd_ok_i;
	input wire [7:0] t_ccd_i;
	input wire [NUM_ENTRIES - 1:0] wr_sch_valid_i;
	input wire [(NUM_ENTRIES * BKW) - 1:0] wr_sch_bank_i;
	input wire [(NUM_ENTRIES * ROW_WIDTH) - 1:0] wr_sch_row_i;
	input wire [(NUM_ENTRIES * COL_WIDTH) - 1:0] wr_sch_col_i;
	input wire [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] wr_sch_older_i;
	input wire wr_commit_ready_i;
	output wire wr_commit_valid_o;
	output wire [PTRW - 1:0] wr_commit_slot_o;
	input wire [NUM_ENTRIES - 1:0] rd_sch_valid_i;
	input wire [(NUM_ENTRIES * BKW) - 1:0] rd_sch_bank_i;
	input wire [(NUM_ENTRIES * ROW_WIDTH) - 1:0] rd_sch_row_i;
	input wire [(NUM_ENTRIES * COL_WIDTH) - 1:0] rd_sch_col_i;
	input wire [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] rd_sch_older_i;
	input wire rd_issue_ready_i;
	output wire rd_issue_valid_o;
	output wire [PTRW - 1:0] rd_issue_slot_o;
	output wire evt_act_o;
	output wire evt_rd_o;
	output wire evt_wr_o;
	output wire evt_pre_o;
	output wire evt_ap_o;
	output wire [RKW - 1:0] evt_rank_o;
	output wire [BKW - 1:0] evt_bank_o;
	output wire [ROW_WIDTH - 1:0] evt_row_o;
	output wire cmd_valid_o;
	input wire cmd_ready_i;
	output wire [3:0] cmd_op_o;
	output wire [RKW - 1:0] cmd_rank_o;
	output wire [BKW - 1:0] cmd_bank_o;
	output wire [ROW_WIDTH - 1:0] cmd_row_o;
	output wire [COL_WIDTH - 1:0] cmd_col_o;
	output wire cmd_ap_o;
	output reg [31:0] stall_bp_o;
	output reg [31:0] stall_refresh_o;
	output reg [31:0] stall_turnaround_o;
	output reg [31:0] stall_tccd_o;
	output reg [31:0] stall_actlimit_o;
	output reg [31:0] stall_banktimer_o;
	output reg [31:0] stall_noreq_o;
	output reg [31:0] stall_zq_o;
	localparam signed [31:0] RK0 = 0;
	wire w_ap;
	assign w_ap = page_policy_i == 2'h1;
	function automatic f_ap;
		input reg [BKW - 1:0] b;
		f_ap = (ap_mode_en_i ? ap_close_i[b] : w_ap);
	endfunction
	reg [NUM_BANKS - 1:0] r_guard0;
	reg [NUM_BANKS - 1:0] r_guard1;
	reg r_pick_valid;
	reg [3:0] r_op;
	reg [BKW - 1:0] r_bank;
	reg [ROW_WIDTH - 1:0] r_row;
	reg [COL_WIDTH - 1:0] r_col_out;
	reg r_ap_out;
	reg r_do_act;
	reg r_do_rd;
	reg r_do_wr;
	reg r_do_pre;
	reg r_grant;
	reg r_zq_grant;
	reg r_wr_commit;
	reg r_rd_issue;
	reg [PTRW - 1:0] r_commit_slot;
	reg [PTRW - 1:0] r_issue_slot;
	reg rd_col_f;
	reg wr_col_f;
	reg rd_act_f;
	reg wr_act_f;
	reg rd_pre_f;
	reg wr_pre_f;
	reg [PTRW - 1:0] rd_col_s;
	reg [PTRW - 1:0] wr_col_s;
	reg [PTRW - 1:0] rd_act_s;
	reg [PTRW - 1:0] wr_act_s;
	reg [PTRW - 1:0] rd_pre_s;
	reg [PTRW - 1:0] wr_pre_s;
	reg rd_col_ap;
	reg wr_col_ap;
	reg [BKW - 1:0] rd_col_bank;
	reg [BKW - 1:0] wr_col_bank;
	reg [BKW - 1:0] rd_act_bank;
	reg [BKW - 1:0] wr_act_bank;
	reg [BKW - 1:0] rd_pre_bank;
	reg [BKW - 1:0] wr_pre_bank;
	reg [COL_WIDTH - 1:0] rd_col_col;
	reg [COL_WIDTH - 1:0] wr_col_col;
	reg [ROW_WIDTH - 1:0] rd_act_row;
	reg [ROW_WIDTH - 1:0] wr_act_row;
	reg w_sel_rd_col_f;
	reg w_sel_wr_col_f;
	reg w_sel_rd_act_f;
	reg w_sel_wr_act_f;
	reg w_sel_rd_pre_f;
	reg w_sel_wr_pre_f;
	reg [PTRW - 1:0] w_sel_rd_col_s;
	reg [PTRW - 1:0] w_sel_wr_col_s;
	reg [PTRW - 1:0] w_sel_rd_act_s;
	reg [PTRW - 1:0] w_sel_wr_act_s;
	reg [PTRW - 1:0] w_sel_rd_pre_s;
	reg [PTRW - 1:0] w_sel_wr_pre_s;
	wire w_out_ready;
	wire w_fire_out;
	reg [15:0] r_zqcs_cnt;
	wire w_zq_busy;
	assign w_zq_busy = r_zqcs_cnt != 16'd0;
	reg w_out_safe;
	wire w_out_reject;
	always @(*) begin
		if (_sv2v_0)
			;
		w_out_safe = 1'b1;
		if (r_do_act)
			w_out_safe = ((bank_act_ready_i[(RK0 * NUM_BANKS) + r_bank] && tfaw_ok_i[RK0]) && trrd_ok_i[RK0]) && !w_zq_busy;
		else if (r_do_rd || r_do_wr)
			w_out_safe = bank_rdwr_ready_i[(RK0 * NUM_BANKS) + r_bank] && !w_zq_busy;
		else if (r_do_pre)
			w_out_safe = bank_pre_ready_i[(RK0 * NUM_BANKS) + r_bank] && !w_zq_busy;
	end
	assign w_out_reject = r_pick_valid && !w_out_safe;
	assign w_out_ready = (!r_pick_valid || cmd_ready_i) || w_out_reject;
	assign w_fire_out = (r_pick_valid && cmd_ready_i) && w_out_safe;
	wire w_prepick_col;
	wire w_prepick_preact;
	assign w_prepick_col = ((w_sel_rd_col_f || w_sel_wr_col_f) || rd_col_f) || wr_col_f;
	assign w_prepick_preact = ((((((w_sel_rd_act_f || w_sel_wr_act_f) || w_sel_rd_pre_f) || w_sel_wr_pre_f) || rd_act_f) || wr_act_f) || rd_pre_f) || wr_pre_f;
	wire w_inflight_col;
	wire w_inflight_preact;
	assign w_inflight_col = r_pick_valid && (r_do_rd || r_do_wr);
	assign w_inflight_preact = r_pick_valid && (r_do_act || r_do_pre);
	wire [NUM_BANKS - 1:0] w_guarded;
	reg [NUM_BANKS - 1:0] w_if_preact_sel;
	reg [NUM_BANKS - 1:0] w_if_preact_pre;
	reg [NUM_BANKS - 1:0] w_if_preact_out;
	reg [NUM_BANKS - 1:0] w_if_col_sel;
	reg [NUM_BANKS - 1:0] w_if_col_pre;
	reg [NUM_BANKS - 1:0] w_if_col_out;
	function automatic [BKW - 1:0] f_bank;
		input reg [(NUM_ENTRIES * BKW) - 1:0] v;
		input reg [PTRW - 1:0] e;
		f_bank = v[e * BKW+:BKW];
	endfunction
	function automatic signed [NUM_BANKS - 1:0] sv2v_cast_A03D0_signed;
		input reg signed [NUM_BANKS - 1:0] inp;
		sv2v_cast_A03D0_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_if_preact_sel = 1'sb0;
		if (w_sel_rd_act_f)
			w_if_preact_sel = w_if_preact_sel | (sv2v_cast_A03D0_signed(1) << f_bank(rd_sch_bank_i, w_sel_rd_act_s));
		if (w_sel_wr_act_f)
			w_if_preact_sel = w_if_preact_sel | (sv2v_cast_A03D0_signed(1) << f_bank(wr_sch_bank_i, w_sel_wr_act_s));
		if (w_sel_rd_pre_f)
			w_if_preact_sel = w_if_preact_sel | (sv2v_cast_A03D0_signed(1) << f_bank(rd_sch_bank_i, w_sel_rd_pre_s));
		if (w_sel_wr_pre_f)
			w_if_preact_sel = w_if_preact_sel | (sv2v_cast_A03D0_signed(1) << f_bank(wr_sch_bank_i, w_sel_wr_pre_s));
		w_if_preact_pre = 1'sb0;
		if (rd_act_f)
			w_if_preact_pre = w_if_preact_pre | (sv2v_cast_A03D0_signed(1) << rd_act_bank);
		if (wr_act_f)
			w_if_preact_pre = w_if_preact_pre | (sv2v_cast_A03D0_signed(1) << wr_act_bank);
		if (rd_pre_f)
			w_if_preact_pre = w_if_preact_pre | (sv2v_cast_A03D0_signed(1) << rd_pre_bank);
		if (wr_pre_f)
			w_if_preact_pre = w_if_preact_pre | (sv2v_cast_A03D0_signed(1) << wr_pre_bank);
		w_if_preact_out = (w_inflight_preact ? sv2v_cast_A03D0_signed(1) << r_bank : {NUM_BANKS {1'sb0}});
		w_if_col_sel = 1'sb0;
		if (w_sel_rd_col_f)
			w_if_col_sel = w_if_col_sel | (sv2v_cast_A03D0_signed(1) << f_bank(rd_sch_bank_i, w_sel_rd_col_s));
		if (w_sel_wr_col_f)
			w_if_col_sel = w_if_col_sel | (sv2v_cast_A03D0_signed(1) << f_bank(wr_sch_bank_i, w_sel_wr_col_s));
		w_if_col_pre = 1'sb0;
		if (rd_col_f)
			w_if_col_pre = w_if_col_pre | (sv2v_cast_A03D0_signed(1) << rd_col_bank);
		if (wr_col_f)
			w_if_col_pre = w_if_col_pre | (sv2v_cast_A03D0_signed(1) << wr_col_bank);
		w_if_col_out = (w_inflight_col ? sv2v_cast_A03D0_signed(1) << r_bank : {NUM_BANKS {1'sb0}});
	end
	wire [NUM_BANKS - 1:0] w_prepick_guard;
	assign w_prepick_guard = w_if_preact_sel | w_if_preact_pre;
	wire [NUM_BANKS - 1:0] w_col_inflight_guard;
	assign w_col_inflight_guard = w_if_col_sel | w_if_col_pre;
	reg [NUM_ENTRIES - 1:0] w_rd_col_inflight_ent;
	reg [NUM_ENTRIES - 1:0] w_wr_col_inflight_ent;
	always @(*) begin
		if (_sv2v_0)
			;
		w_rd_col_inflight_ent = 1'sb0;
		w_wr_col_inflight_ent = 1'sb0;
		if (w_sel_rd_col_f)
			w_rd_col_inflight_ent[w_sel_rd_col_s] = 1'b1;
		if (w_sel_wr_col_f)
			w_wr_col_inflight_ent[w_sel_wr_col_s] = 1'b1;
		if (rd_col_f)
			w_rd_col_inflight_ent[rd_col_s] = 1'b1;
		if (wr_col_f)
			w_wr_col_inflight_ent[wr_col_s] = 1'b1;
		if (r_pick_valid && r_do_rd)
			w_rd_col_inflight_ent[r_issue_slot] = 1'b1;
		if (r_pick_valid && r_do_wr)
			w_wr_col_inflight_ent[r_commit_slot] = 1'b1;
	end
	wire w_act_classify_gate;
	assign w_act_classify_gate = (sched_access_pref_i == 2'd2 ? tfaw_ok_i[RK0] && trrd_ok_i[RK0] : 1'b1);
	wire [NUM_BANKS - 1:0] w_col_inflight_bank;
	assign w_col_inflight_bank = w_col_inflight_guard | (w_inflight_col ? sv2v_cast_A03D0_signed(1) << r_bank : {NUM_BANKS {1'sb0}});
	reg [NUM_BANKS - 1:0] w_ref_col_block;
	function automatic signed [BKW - 1:0] sv2v_cast_1D528_signed;
		input reg signed [BKW - 1:0] inp;
		sv2v_cast_1D528_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				w_ref_col_block[b] = (refresh_req_i || refresh_drain_i) && (!refresh_kind_i || (sv2v_cast_1D528_signed(b) == refresh_bank_i));
		end
	end
	reg [7:0] r_tccd_fwd;
	wire w_col_sel_now;
	wire w_tccd_fwd_ok;
	assign w_col_sel_now = w_sel_rd_col_f || w_sel_wr_col_f;
	assign w_tccd_fwd_ok = (r_tccd_fwd <= 8'd1) && !(w_col_sel_now && (t_ccd_i > 8'd1));
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_tccd_fwd <= 1'sb0;
		else if (w_col_sel_now)
			r_tccd_fwd <= (t_ccd_i > 8'd1 ? t_ccd_i - 8'd1 : 8'd0);
		else if (r_tccd_fwd != 8'd0)
			r_tccd_fwd <= r_tccd_fwd - 8'd1;
	reg [NUM_BANKS - 1:0] r_ap_closing;
	wire [NUM_BANKS - 1:0] w_ap_fire_bank;
	assign w_ap_fire_bank = ((w_fire_out && (r_do_rd || r_do_wr)) && r_ap_out ? sv2v_cast_A03D0_signed(1) << r_bank : {NUM_BANKS {1'sb0}});
	assign w_guarded = ((((r_guard0 | r_guard1) | w_prepick_guard) | w_col_inflight_guard) | w_if_preact_out) | w_if_col_out;
	wire [NUM_BANKS - 1:0] w_preact_bank_guard;
	assign w_preact_bank_guard = w_prepick_guard | w_if_preact_out;
	reg r_wrfire0;
	reg r_wrfire1;
	reg r_rdfire0;
	reg r_rdfire1;
	wire w_rd_turn_block;
	wire w_wr_turn_block;
	assign w_rd_turn_block = r_wrfire0 || r_wrfire1;
	assign w_wr_turn_block = r_rdfire0 || r_rdfire1;
	reg [NUM_BANKS - 1:0] r_apguard0;
	reg [NUM_BANKS - 1:0] r_apguard1;
	wire [NUM_BANKS - 1:0] w_ap_col_guard;
	assign w_ap_col_guard = r_apguard0 | r_apguard1;
	reg [NUM_BANKS - 1:0] r_preguard0;
	reg [NUM_BANKS - 1:0] r_preguard1;
	reg [NUM_BANKS - 1:0] r_preguard2;
	wire [NUM_BANKS - 1:0] w_pre_col_guard;
	assign w_pre_col_guard = (r_preguard0 | r_preguard1) | r_preguard2;
	reg [15:0] r_rfc_cnt;
	wire w_rfc_busy;
	assign w_rfc_busy = r_rfc_cnt != 16'd0;
	reg [(NUM_RANKS * NUM_BANKS) - 1:0] r_bank_act_ready;
	reg [(NUM_RANKS * NUM_BANKS) - 1:0] r_bank_rdwr_ready;
	reg [(NUM_RANKS * NUM_BANKS) - 1:0] r_bank_pre_ready;
	reg [(NUM_RANKS * NUM_BANKS) - 1:0] r_bank_row_active;
	reg [((NUM_RANKS * NUM_BANKS) * ROW_WIDTH) - 1:0] r_bank_open_row;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_bank_act_ready <= 1'sb0;
			r_bank_rdwr_ready <= 1'sb0;
			r_bank_pre_ready <= 1'sb0;
			r_bank_row_active <= 1'sb0;
			r_bank_open_row <= 1'sb0;
		end
		else begin
			r_bank_act_ready <= bank_act_ready_la_i;
			r_bank_rdwr_ready <= bank_rdwr_ready_la_i;
			r_bank_pre_ready <= bank_pre_ready_la_i;
			r_bank_row_active <= bank_row_active_i;
			r_bank_open_row <= bank_open_row_i;
		end
	function automatic [ROW_WIDTH - 1:0] f_row;
		input reg [(NUM_ENTRIES * ROW_WIDTH) - 1:0] v;
		input reg [PTRW - 1:0] e;
		f_row = v[e * ROW_WIDTH+:ROW_WIDTH];
	endfunction
	function automatic [COL_WIDTH - 1:0] f_col;
		input reg [(NUM_ENTRIES * COL_WIDTH) - 1:0] v;
		input reg [PTRW - 1:0] e;
		f_col = v[e * COL_WIDTH+:COL_WIDTH];
	endfunction
	reg [NUM_ENTRIES - 1:0] rd_col_m;
	reg [NUM_ENTRIES - 1:0] rd_act_m;
	reg [NUM_ENTRIES - 1:0] rd_pre_m;
	reg [NUM_ENTRIES - 1:0] wr_col_m;
	reg [NUM_ENTRIES - 1:0] wr_act_m;
	reg [NUM_ENTRIES - 1:0] wr_pre_m;
	function automatic signed [PTRW - 1:0] sv2v_cast_E6D00_signed;
		input reg signed [PTRW - 1:0] inp;
		sv2v_cast_E6D00_signed = inp;
	endfunction
	always @(r_bank_pre_ready[RK0 * NUM_BANKS+:NUM_BANKS] or w_guarded or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or w_rfc_busy or w_act_classify_gate or r_bank_act_ready[RK0 * NUM_BANKS+:NUM_BANKS] or w_guarded or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or w_preact_bank_guard or w_pre_col_guard or w_ap_col_guard or w_wr_turn_block or w_ref_col_block or w_wr_col_inflight_ent or r_ap_closing or w_col_inflight_bank or w_ap or ap_close_i or ap_mode_en_i or wr_commit_ready_i or trtw_ok_i or w_tccd_fwd_ok or r_bank_rdwr_ready[RK0 * NUM_BANKS+:NUM_BANKS] or wr_sch_valid_i or r_bank_pre_ready[RK0 * NUM_BANKS+:NUM_BANKS] or w_guarded or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or w_rfc_busy or w_act_classify_gate or r_bank_act_ready[RK0 * NUM_BANKS+:NUM_BANKS] or w_guarded or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or w_preact_bank_guard or w_pre_col_guard or w_ap_col_guard or w_rd_turn_block or w_ref_col_block or w_rd_col_inflight_ent or r_ap_closing or w_col_inflight_bank or w_ap or ap_close_i or ap_mode_en_i or rd_issue_ready_i or twtr_ok_i or w_tccd_fwd_ok or r_bank_rdwr_ready[RK0 * NUM_BANKS+:NUM_BANKS] or rd_sch_valid_i or r_bank_open_row[ROW_WIDTH * (RK0 * NUM_BANKS)+:ROW_WIDTH * NUM_BANKS] or wr_sch_row_i or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or r_bank_open_row[ROW_WIDTH * (RK0 * NUM_BANKS)+:ROW_WIDTH * NUM_BANKS] or rd_sch_row_i or r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS] or wr_sch_bank_i or rd_sch_bank_i or _sv2v_0) begin
		if (_sv2v_0)
			;
		rd_col_m = 1'sb0;
		rd_act_m = 1'sb0;
		rd_pre_m = 1'sb0;
		wr_col_m = 1'sb0;
		wr_act_m = 1'sb0;
		wr_pre_m = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] e;
			for (e = 0; e < NUM_ENTRIES; e = e + 1)
				begin : sv2v_autoblock_3
					reg [PTRW - 1:0] ei;
					reg [BKW - 1:0] rb;
					reg [BKW - 1:0] wb;
					reg rhit;
					reg whit;
					ei = sv2v_cast_E6D00_signed(e);
					rb = f_bank(rd_sch_bank_i, ei);
					wb = f_bank(wr_sch_bank_i, ei);
					rhit = r_bank_row_active[(RK0 * NUM_BANKS) + rb] && (f_row(rd_sch_row_i, ei) == r_bank_open_row[((RK0 * NUM_BANKS) + rb) * ROW_WIDTH+:ROW_WIDTH]);
					whit = r_bank_row_active[(RK0 * NUM_BANKS) + wb] && (f_row(wr_sch_row_i, ei) == r_bank_open_row[((RK0 * NUM_BANKS) + wb) * ROW_WIDTH+:ROW_WIDTH]);
					if (rd_sch_valid_i[e]) begin
						rd_col_m[e] = (((((((((((rhit && r_bank_rdwr_ready[(RK0 * NUM_BANKS) + rb]) && w_tccd_fwd_ok) && twtr_ok_i) && rd_issue_ready_i) && !(f_ap(rb) && w_col_inflight_bank[rb])) && !r_ap_closing[rb]) && !w_rd_col_inflight_ent[e]) && !w_ref_col_block[rb]) && !w_rd_turn_block) && !w_ap_col_guard[rb]) && !w_pre_col_guard[rb]) && !w_preact_bank_guard[rb];
						rd_act_m[e] = (((!r_bank_row_active[(RK0 * NUM_BANKS) + rb] && !w_guarded[rb]) && r_bank_act_ready[(RK0 * NUM_BANKS) + rb]) && w_act_classify_gate) && !w_rfc_busy;
						rd_pre_m[e] = ((r_bank_row_active[(RK0 * NUM_BANKS) + rb] && !w_guarded[rb]) && !rhit) && r_bank_pre_ready[(RK0 * NUM_BANKS) + rb];
					end
					if (wr_sch_valid_i[e]) begin
						wr_col_m[e] = (((((((((((whit && r_bank_rdwr_ready[(RK0 * NUM_BANKS) + wb]) && w_tccd_fwd_ok) && trtw_ok_i) && wr_commit_ready_i) && !(f_ap(wb) && w_col_inflight_bank[wb])) && !r_ap_closing[wb]) && !w_wr_col_inflight_ent[e]) && !w_ref_col_block[wb]) && !w_wr_turn_block) && !w_ap_col_guard[wb]) && !w_pre_col_guard[wb]) && !w_preact_bank_guard[wb];
						wr_act_m[e] = (((!r_bank_row_active[(RK0 * NUM_BANKS) + wb] && !w_guarded[wb]) && r_bank_act_ready[(RK0 * NUM_BANKS) + wb]) && w_act_classify_gate) && !w_rfc_busy;
						wr_pre_m[e] = ((r_bank_row_active[(RK0 * NUM_BANKS) + wb] && !w_guarded[wb]) && !whit) && r_bank_pre_ready[(RK0 * NUM_BANKS) + wb];
					end
				end
		end
	end
	function automatic [PTRW:0] arg_oldest;
		input reg [NUM_ENTRIES - 1:0] mask;
		input reg [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] older;
		reg found;
		reg [PTRW - 1:0] slot;
		reg [NUM_ENTRIES - 1:0] is_old;
		begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					begin : sv2v_autoblock_5
						reg [NUM_ENTRIES - 1:0] orow;
						reg ge_all;
						orow = older[i * NUM_ENTRIES+:NUM_ENTRIES];
						ge_all = 1'b1;
						begin : sv2v_autoblock_6
							reg signed [31:0] j;
							for (j = 0; j < NUM_ENTRIES; j = j + 1)
								if (((j != i) && mask[j]) && !orow[j])
									ge_all = 1'b0;
						end
						is_old[i] = mask[i] && ge_all;
					end
			end
			found = |is_old;
			slot = 1'sb0;
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = NUM_ENTRIES - 1; i >= 0; i = i - 1)
					if (is_old[i])
						slot = sv2v_cast_E6D00_signed(i);
			end
			arg_oldest = {found, slot};
		end
	endfunction
	localparam [1:0] ORDER_IN_ORDER = 2'd1;
	localparam [1:0] ORDER_AGE_THR = 2'd3;
	localparam [0:0] SUPPORT_GLOBAL_ORDER = 1'b0;
	reg [NUM_ENTRIES - 1:0] w_rd_head;
	reg [NUM_ENTRIES - 1:0] w_wr_head;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				begin : sv2v_autoblock_9
					reg older_rd;
					reg older_wr;
					older_rd = 1'b0;
					older_wr = 1'b0;
					begin : sv2v_autoblock_10
						reg signed [31:0] j;
						for (j = 0; j < NUM_ENTRIES; j = j + 1)
							begin
								if (((j != i) && rd_sch_valid_i[j]) && rd_sch_older_i[(j * NUM_ENTRIES) + i])
									older_rd = 1'b1;
								if (((j != i) && wr_sch_valid_i[j]) && wr_sch_older_i[(j * NUM_ENTRIES) + i])
									older_wr = 1'b1;
							end
					end
					w_rd_head[i] = rd_sch_valid_i[i] && !older_rd;
					w_wr_head[i] = wr_sch_valid_i[i] && !older_wr;
				end
		end
	end
	wire w_rd_head_wins;
	assign w_rd_head_wins = !(|wr_sch_valid_i) || (|rd_sch_valid_i && (rd_sch_head_rel_i >= wr_sch_head_rel_i));
	wire w_boost_any;
	assign w_boost_any = |rd_sch_age_exceed_i || |wr_sch_age_exceed_i;
	reg [NUM_ENTRIES - 1:0] rd_col_me;
	reg [NUM_ENTRIES - 1:0] rd_act_me;
	reg [NUM_ENTRIES - 1:0] rd_pre_me;
	reg [NUM_ENTRIES - 1:0] wr_col_me;
	reg [NUM_ENTRIES - 1:0] wr_act_me;
	reg [NUM_ENTRIES - 1:0] wr_pre_me;
	always @(*) begin
		if (_sv2v_0)
			;
		rd_col_me = rd_col_m;
		rd_act_me = rd_act_m;
		rd_pre_me = rd_pre_m;
		wr_col_me = wr_col_m;
		wr_act_me = wr_act_m;
		wr_pre_me = wr_pre_m;
		if (sched_order_mode_i == ORDER_IN_ORDER) begin
			rd_col_me = rd_col_me & w_rd_head;
			rd_act_me = rd_act_me & w_rd_head;
			rd_pre_me = rd_pre_me & w_rd_head;
			wr_col_me = wr_col_me & w_wr_head;
			wr_act_me = wr_act_me & w_wr_head;
			wr_pre_me = wr_pre_me & w_wr_head;
			if (SUPPORT_GLOBAL_ORDER) begin
				if (w_rd_head_wins) begin
					wr_col_me = 1'sb0;
					wr_act_me = 1'sb0;
					wr_pre_me = 1'sb0;
				end
				else begin
					rd_col_me = 1'sb0;
					rd_act_me = 1'sb0;
					rd_pre_me = 1'sb0;
				end
			end
		end
		else if ((sched_order_mode_i == ORDER_AGE_THR) && w_boost_any) begin
			rd_col_me = rd_col_me & rd_sch_age_exceed_i;
			rd_act_me = rd_act_me & rd_sch_age_exceed_i;
			rd_pre_me = rd_pre_me & rd_sch_age_exceed_i;
			wr_col_me = wr_col_me & wr_sch_age_exceed_i;
			wr_act_me = wr_act_me & wr_sch_age_exceed_i;
			wr_pre_me = wr_pre_me & wr_sch_age_exceed_i;
		end
	end
	localparam signed [31:0] POPW = $clog2(NUM_ENTRIES + 1);
	reg [POPW - 1:0] rd_pop [0:NUM_ENTRIES - 1];
	reg [POPW - 1:0] wr_pop [0:NUM_ENTRIES - 1];
	function automatic signed [POPW - 1:0] sv2v_cast_15CC9_signed;
		input reg signed [POPW - 1:0] inp;
		sv2v_cast_15CC9_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_11
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				begin
					rd_pop[i] = 1'sb0;
					wr_pop[i] = 1'sb0;
					begin : sv2v_autoblock_12
						reg signed [31:0] j;
						for (j = 0; j < NUM_ENTRIES; j = j + 1)
							begin
								if ((rd_sch_valid_i[j] && (f_bank(rd_sch_bank_i, sv2v_cast_E6D00_signed(j)) == f_bank(rd_sch_bank_i, sv2v_cast_E6D00_signed(i)))) && (f_row(rd_sch_row_i, sv2v_cast_E6D00_signed(j)) == f_row(rd_sch_row_i, sv2v_cast_E6D00_signed(i))))
									rd_pop[i] = rd_pop[i] + sv2v_cast_15CC9_signed(1);
								if ((wr_sch_valid_i[j] && (f_bank(wr_sch_bank_i, sv2v_cast_E6D00_signed(j)) == f_bank(wr_sch_bank_i, sv2v_cast_E6D00_signed(i)))) && (f_row(wr_sch_row_i, sv2v_cast_E6D00_signed(j)) == f_row(wr_sch_row_i, sv2v_cast_E6D00_signed(i))))
									wr_pop[i] = wr_pop[i] + sv2v_cast_15CC9_signed(1);
							end
					end
				end
		end
	end
	function automatic [PTRW:0] arg_sel;
		input reg [1:0] sel;
		input reg [NUM_ENTRIES - 1:0] mask;
		input reg [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] older;
		input reg [(NUM_ENTRIES * POPW) - 1:0] pops;
		reg found;
		reg [PTRW - 1:0] slot;
		reg [NUM_ENTRIES - 1:0] is_best;
		begin
			begin : sv2v_autoblock_13
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					begin : sv2v_autoblock_14
						reg [NUM_ENTRIES - 1:0] orow;
						reg best;
						orow = older[i * NUM_ENTRIES+:NUM_ENTRIES];
						best = 1'b1;
						begin : sv2v_autoblock_15
							reg signed [31:0] j;
							for (j = 0; j < NUM_ENTRIES; j = j + 1)
								if ((j != i) && mask[j]) begin : sv2v_autoblock_16
									reg j_pop_wins;
									reg pop_tie;
									j_pop_wins = (sel == 2'd1 ? pops[((NUM_ENTRIES - 1) - j) * POPW+:POPW] > pops[((NUM_ENTRIES - 1) - i) * POPW+:POPW] : (sel == 2'd2 ? pops[((NUM_ENTRIES - 1) - j) * POPW+:POPW] < pops[((NUM_ENTRIES - 1) - i) * POPW+:POPW] : 1'b0));
									pop_tie = (sel == 2'd0) || (pops[((NUM_ENTRIES - 1) - j) * POPW+:POPW] == pops[((NUM_ENTRIES - 1) - i) * POPW+:POPW]);
									if (j_pop_wins || (pop_tie && !orow[j]))
										best = 1'b0;
								end
						end
						is_best[i] = mask[i] && best;
					end
			end
			found = |is_best;
			slot = 1'sb0;
			begin : sv2v_autoblock_17
				reg signed [31:0] i;
				for (i = NUM_ENTRIES - 1; i >= 0; i = i - 1)
					if (is_best[i])
						slot = sv2v_cast_E6D00_signed(i);
			end
			arg_sel = {found, slot};
		end
	endfunction
	function automatic [NUM_ENTRIES - 1:0] qos_top;
		input reg [NUM_ENTRIES - 1:0] mask;
		input reg [(NUM_ENTRIES * 4) - 1:0] qosv;
		reg [3:0] best;
		reg [NUM_ENTRIES - 1:0] out;
		begin
			best = 1'sb0;
			begin : sv2v_autoblock_18
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					if (mask[i] && (qosv[i * 4+:4] > best))
						best = qosv[i * 4+:4];
			end
			begin : sv2v_autoblock_19
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					out[i] = mask[i] && (qosv[i * 4+:4] == best);
			end
			qos_top = out;
		end
	endfunction
	reg [NUM_ENTRIES - 1:0] rd_col_q;
	reg [NUM_ENTRIES - 1:0] rd_act_q;
	reg [NUM_ENTRIES - 1:0] rd_pre_q;
	reg [NUM_ENTRIES - 1:0] wr_col_q;
	reg [NUM_ENTRIES - 1:0] wr_act_q;
	reg [NUM_ENTRIES - 1:0] wr_pre_q;
	always @(*) begin
		if (_sv2v_0)
			;
		rd_col_q = (sched_qos_en_i ? qos_top(rd_col_me, rd_sch_qos_i) : rd_col_me);
		rd_act_q = (sched_qos_en_i ? qos_top(rd_act_me, rd_sch_qos_i) : rd_act_me);
		rd_pre_q = (sched_qos_en_i ? qos_top(rd_pre_me, rd_sch_qos_i) : rd_pre_me);
		wr_col_q = (sched_qos_en_i ? qos_top(wr_col_me, wr_sch_qos_i) : wr_col_me);
		wr_act_q = (sched_qos_en_i ? qos_top(wr_act_me, wr_sch_qos_i) : wr_act_me);
		wr_pre_q = (sched_qos_en_i ? qos_top(wr_pre_me, wr_sch_qos_i) : wr_pre_me);
	end
	reg [NUM_ENTRIES - 1:0] r_rd_col_q;
	reg [NUM_ENTRIES - 1:0] r_rd_act_q;
	reg [NUM_ENTRIES - 1:0] r_rd_pre_q;
	reg [NUM_ENTRIES - 1:0] r_wr_col_q;
	reg [NUM_ENTRIES - 1:0] r_wr_act_q;
	reg [NUM_ENTRIES - 1:0] r_wr_pre_q;
	reg [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] r_rd_older;
	reg [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] r_wr_older;
	reg [(NUM_ENTRIES * POPW) - 1:0] r_rd_pop;
	reg [(NUM_ENTRIES * POPW) - 1:0] r_wr_pop;
	reg [1:0] r_col_sel;
	reg [1:0] r_row_sel;
	reg [NUM_BANKS - 1:0] r_ap_snap;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_rd_col_q <= 1'sb0;
			r_rd_act_q <= 1'sb0;
			r_rd_pre_q <= 1'sb0;
			r_wr_col_q <= 1'sb0;
			r_wr_act_q <= 1'sb0;
			r_wr_pre_q <= 1'sb0;
			r_rd_older <= 1'sb0;
			r_wr_older <= 1'sb0;
			r_col_sel <= 1'sb0;
			r_row_sel <= 1'sb0;
			r_ap_snap <= 1'sb0;
			begin : sv2v_autoblock_20
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					begin
						r_rd_pop[((NUM_ENTRIES - 1) - i) * POPW+:POPW] <= 1'sb0;
						r_wr_pop[((NUM_ENTRIES - 1) - i) * POPW+:POPW] <= 1'sb0;
					end
			end
		end
		else if (w_out_ready) begin
			r_rd_col_q <= rd_col_q;
			r_rd_act_q <= rd_act_q;
			r_rd_pre_q <= rd_pre_q;
			r_wr_col_q <= wr_col_q;
			r_wr_act_q <= wr_act_q;
			r_wr_pre_q <= wr_pre_q;
			r_rd_older <= rd_sch_older_i;
			r_wr_older <= wr_sch_older_i;
			r_col_sel <= sched_col_sel_i;
			r_row_sel <= sched_row_sel_i;
			begin : sv2v_autoblock_21
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					begin
						r_rd_pop[((NUM_ENTRIES - 1) - i) * POPW+:POPW] <= rd_pop[i];
						r_wr_pop[((NUM_ENTRIES - 1) - i) * POPW+:POPW] <= wr_pop[i];
					end
			end
			begin : sv2v_autoblock_22
				reg signed [31:0] b;
				for (b = 0; b < NUM_BANKS; b = b + 1)
					r_ap_snap[b] <= f_ap(sv2v_cast_1D528_signed(b));
			end
		end
	wire w_act_gate_live;
	assign w_act_gate_live = (!w_rfc_busy && tfaw_ok_i[RK0]) && trrd_ok_i[RK0];
	wire w_rd_turn_live;
	wire w_wr_turn_live;
	assign w_rd_turn_live = (twtr_ok_i && !w_rd_turn_block) && !(w_fire_out && r_do_wr);
	assign w_wr_turn_live = (trtw_ok_i && !w_wr_turn_block) && !(w_fire_out && r_do_rd);
	always @(*) begin
		if (_sv2v_0)
			;
		{w_sel_rd_col_f, w_sel_rd_col_s} = arg_sel(r_col_sel, r_rd_col_q & rd_sch_valid_i, r_rd_older, r_rd_pop);
		{w_sel_wr_col_f, w_sel_wr_col_s} = arg_sel(r_col_sel, r_wr_col_q & wr_sch_valid_i, r_wr_older, r_wr_pop);
		{w_sel_rd_act_f, w_sel_rd_act_s} = arg_sel(r_row_sel, r_rd_act_q & rd_sch_valid_i, r_rd_older, r_rd_pop);
		{w_sel_wr_act_f, w_sel_wr_act_s} = arg_sel(r_row_sel, r_wr_act_q & wr_sch_valid_i, r_wr_older, r_wr_pop);
		{w_sel_rd_pre_f, w_sel_rd_pre_s} = arg_oldest(r_rd_pre_q & rd_sch_valid_i, r_rd_older);
		{w_sel_wr_pre_f, w_sel_wr_pre_s} = arg_oldest(r_wr_pre_q & wr_sch_valid_i, r_wr_older);
		if (!w_act_gate_live) begin
			w_sel_rd_act_f = 1'b0;
			w_sel_wr_act_f = 1'b0;
		end
	end
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			rd_col_f <= 1'b0;
			wr_col_f <= 1'b0;
			rd_act_f <= 1'b0;
			wr_act_f <= 1'b0;
			rd_pre_f <= 1'b0;
			wr_pre_f <= 1'b0;
			rd_col_ap <= 1'b0;
			wr_col_ap <= 1'b0;
		end
		else if (w_out_ready) begin
			rd_col_f <= w_sel_rd_col_f;
			rd_col_s <= w_sel_rd_col_s;
			wr_col_f <= w_sel_wr_col_f;
			wr_col_s <= w_sel_wr_col_s;
			rd_col_ap <= r_ap_snap[f_bank(rd_sch_bank_i, w_sel_rd_col_s)];
			wr_col_ap <= r_ap_snap[f_bank(wr_sch_bank_i, w_sel_wr_col_s)];
			rd_act_f <= w_sel_rd_act_f;
			rd_act_s <= w_sel_rd_act_s;
			wr_act_f <= w_sel_wr_act_f;
			wr_act_s <= w_sel_wr_act_s;
			rd_pre_f <= w_sel_rd_pre_f;
			rd_pre_s <= w_sel_rd_pre_s;
			wr_pre_f <= w_sel_wr_pre_f;
			wr_pre_s <= w_sel_wr_pre_s;
			rd_col_bank <= f_bank(rd_sch_bank_i, w_sel_rd_col_s);
			rd_col_col <= f_col(rd_sch_col_i, w_sel_rd_col_s);
			wr_col_bank <= f_bank(wr_sch_bank_i, w_sel_wr_col_s);
			wr_col_col <= f_col(wr_sch_col_i, w_sel_wr_col_s);
			rd_act_bank <= f_bank(rd_sch_bank_i, w_sel_rd_act_s);
			rd_act_row <= f_row(rd_sch_row_i, w_sel_rd_act_s);
			wr_act_bank <= f_bank(wr_sch_bank_i, w_sel_wr_act_s);
			wr_act_row <= f_row(wr_sch_row_i, w_sel_wr_act_s);
			rd_pre_bank <= f_bank(rd_sch_bank_i, w_sel_rd_pre_s);
			wr_pre_bank <= f_bank(wr_sch_bank_i, w_sel_wr_pre_s);
		end
	localparam signed [31:0] OCCW = $clog2(NUM_ENTRIES + 1);
	reg [OCCW - 1:0] w_wr_occ;
	function automatic signed [OCCW - 1:0] sv2v_cast_002A9_signed;
		input reg signed [OCCW - 1:0] inp;
		sv2v_cast_002A9_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_wr_occ = 1'sb0;
		begin : sv2v_autoblock_23
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				if (wr_sch_valid_i[i])
					w_wr_occ = w_wr_occ + sv2v_cast_002A9_signed(1);
		end
	end
	reg r_dir_rr;
	localparam signed [31:0] WR_BATCH_W = 8;
	reg r_wr_drain;
	reg [7:0] r_wr_batch_cnt;
	reg r_rd_owed;
	wire w_wr_col_fire;
	wire w_rd_col_fire;
	wire w_batch_done;
	assign w_wr_col_fire = w_fire_out && r_do_wr;
	assign w_rd_col_fire = w_fire_out && r_do_rd;
	assign w_batch_done = ((r_wr_drain && w_wr_col_fire) && (sched_wr_batch_max_i != 8'd0)) && (r_wr_batch_cnt >= (sched_wr_batch_max_i - 8'd1));
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_wr_drain <= 1'b0;
			r_wr_batch_cnt <= 1'sb0;
			r_rd_owed <= 1'b0;
		end
		else begin
			if (w_rd_col_fire)
				r_rd_owed <= 1'b0;
			if (sched_wr_high_wm_i == 8'd0) begin
				r_wr_drain <= 1'b0;
				r_wr_batch_cnt <= 1'sb0;
				r_rd_owed <= 1'b0;
			end
			else if (w_batch_done) begin
				r_wr_drain <= 1'b0;
				r_wr_batch_cnt <= 1'sb0;
				r_rd_owed <= 1'b1;
			end
			else if (sv2v_cast_8(w_wr_occ) <= sched_wr_low_wm_i) begin
				r_wr_drain <= 1'b0;
				r_wr_batch_cnt <= 1'sb0;
			end
			else if ((sv2v_cast_8(w_wr_occ) >= sched_wr_high_wm_i) && !r_rd_owed) begin
				r_wr_drain <= 1'b1;
				if (w_wr_col_fire)
					r_wr_batch_cnt <= r_wr_batch_cnt + 1'b1;
			end
			else if (r_wr_drain && w_wr_col_fire)
				r_wr_batch_cnt <= r_wr_batch_cnt + 1'b1;
		end
	wire w_any_pending;
	wire w_stalled;
	assign w_any_pending = |rd_sch_valid_i || |wr_sch_valid_i;
	assign w_stalled = !w_fire_out;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			stall_bp_o <= 32'h00000000;
			stall_refresh_o <= 32'h00000000;
			stall_turnaround_o <= 32'h00000000;
			stall_tccd_o <= 32'h00000000;
			stall_actlimit_o <= 32'h00000000;
			stall_banktimer_o <= 32'h00000000;
			stall_noreq_o <= 32'h00000000;
			stall_zq_o <= 32'h00000000;
		end
		else if (w_stalled) begin
			if (w_out_reject)
				stall_banktimer_o <= stall_banktimer_o + 32'h00000001;
			else if (r_pick_valid)
				stall_bp_o <= stall_bp_o + 32'h00000001;
			else if (w_zq_busy || zq_req_i)
				stall_zq_o <= stall_zq_o + 32'h00000001;
			else if (refresh_req_i || refresh_drain_i)
				stall_refresh_o <= stall_refresh_o + 32'h00000001;
			else if (!w_any_pending)
				stall_noreq_o <= stall_noreq_o + 32'h00000001;
			else if (!twtr_ok_i || !trtw_ok_i)
				stall_turnaround_o <= stall_turnaround_o + 32'h00000001;
			else if (!tccd_ok_i)
				stall_tccd_o <= stall_tccd_o + 32'h00000001;
			else if (!tfaw_ok_i[RK0] || !trrd_ok_i[RK0])
				stall_actlimit_o <= stall_actlimit_o + 32'h00000001;
			else
				stall_banktimer_o <= stall_banktimer_o + 32'h00000001;
		end
	reg w_col_wrf;
	reg w_act_wrf;
	reg w_pre_wrf;
	always @(*) begin : sv2v_autoblock_24
		reg rr;
		rr = (sched_prio_sub_i == 2'd1) && r_dir_rr;
		if (_sv2v_0)
			;
		w_col_wrf = (r_wr_drain || rr) || (((sched_prio_sub_i == 2'd3) && wr_sch_age_exceed_i[wr_col_s]) && !rd_sch_age_exceed_i[rd_col_s]);
		w_act_wrf = (r_wr_drain || rr) || (((sched_prio_sub_i == 2'd3) && wr_sch_age_exceed_i[wr_act_s]) && !rd_sch_age_exceed_i[rd_act_s]);
		w_pre_wrf = (r_wr_drain || rr) || (((sched_prio_sub_i == 2'd3) && wr_sch_age_exceed_i[wr_pre_s]) && !rd_sch_age_exceed_i[rd_pre_s]);
	end
	reg w_c_col;
	reg w_c_act;
	reg w_c_pre;
	reg [1:0] w_pick_class;
	always @(*) begin
		if (_sv2v_0)
			;
		w_c_col = rd_col_f || wr_col_f;
		w_c_act = (rd_act_f || wr_act_f) && w_act_gate_live;
		w_c_pre = rd_pre_f || wr_pre_f;
		(* full_case, parallel_case *)
		case (sched_access_pref_i)
			2'd2: w_pick_class = (w_c_act ? 2'd2 : (w_c_col ? 2'd1 : (w_c_pre ? 2'd3 : 2'd0)));
			2'd3: w_pick_class = (w_c_pre ? 2'd3 : (w_c_col ? 2'd1 : (w_c_act ? 2'd2 : 2'd0)));
			default: w_pick_class = (w_c_col ? 2'd1 : (w_c_act ? 2'd2 : (w_c_pre ? 2'd3 : 2'd0)));
		endcase
	end
	reg w_any_active;
	reg w_rfsh_pre_found;
	wire w_ref_safe;
	reg [BKW - 1:0] w_rfsh_pre_bank;
	always @(*) begin
		if (_sv2v_0)
			;
		w_any_active = |r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS];
		w_rfsh_pre_found = 1'b0;
		w_rfsh_pre_bank = 1'sb0;
		begin : sv2v_autoblock_25
			reg signed [31:0] j;
			for (j = NUM_BANKS - 1; j >= 0; j = j - 1)
				if ((r_bank_row_active[(RK0 * NUM_BANKS) + j] && r_bank_pre_ready[(RK0 * NUM_BANKS) + j]) && !w_guarded[j]) begin
					w_rfsh_pre_found = 1'b1;
					w_rfsh_pre_bank = sv2v_cast_1D528_signed(j);
				end
		end
	end
	assign w_ref_safe = (((((!w_any_active && !w_inflight_preact) && (r_guard0 == {NUM_BANKS {1'sb0}})) && (r_guard1 == {NUM_BANKS {1'sb0}})) && !w_rfc_busy) && !r_grant) && !r_zq_grant;
	wire w_refpb_safe;
	assign w_refpb_safe = ((((!r_bank_row_active[(RK0 * NUM_BANKS) + refresh_bank_i] && !w_inflight_preact) && (r_guard0 == {NUM_BANKS {1'sb0}})) && (r_guard1 == {NUM_BANKS {1'sb0}})) && !w_rfc_busy) && !r_grant;
	wire w_zq_safe;
	assign w_zq_safe = ((((((!w_any_active && !w_inflight_preact) && (r_guard0 == {NUM_BANKS {1'sb0}})) && (r_guard1 == {NUM_BANKS {1'sb0}})) && !w_rfc_busy) && !w_zq_busy) && !r_grant) && !r_zq_grant;
	reg [3:0] w_op;
	reg [BKW - 1:0] w_bank;
	reg [ROW_WIDTH - 1:0] w_row;
	reg [COL_WIDTH - 1:0] w_col;
	reg w_ap_out;
	reg w_valid;
	reg w_do_act;
	reg w_do_rd;
	reg w_do_wr;
	reg w_do_pre;
	reg w_grant;
	reg w_zq_grant;
	reg w_wr_commit;
	reg w_rd_issue;
	reg [PTRW - 1:0] w_commit_slot;
	reg [PTRW - 1:0] w_issue_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		w_op = 4'h0;
		w_bank = 1'sb0;
		w_row = 1'sb0;
		w_col = 1'sb0;
		w_ap_out = 1'b0;
		w_valid = 1'b0;
		w_do_act = 1'b0;
		w_do_rd = 1'b0;
		w_do_wr = 1'b0;
		w_do_pre = 1'b0;
		w_grant = 1'b0;
		w_zq_grant = 1'b0;
		w_wr_commit = 1'b0;
		w_rd_issue = 1'b0;
		w_commit_slot = 1'sb0;
		w_issue_slot = 1'sb0;
		if (!init_done_i) begin
			if (init_cmd_valid_i) begin
				w_valid = 1'b1;
				w_op = init_cmd_op_i;
				w_bank = init_cmd_bank_i;
				w_row = init_cmd_row_i;
			end
		end
		else if (w_zq_busy)
			w_valid = 1'b0;
		else if (refresh_req_i || refresh_drain_i) begin
			if (refresh_kind_i) begin
				if (r_bank_row_active[(RK0 * NUM_BANKS) + refresh_bank_i]) begin
					if (r_bank_pre_ready[(RK0 * NUM_BANKS) + refresh_bank_i] && !w_guarded[refresh_bank_i]) begin
						w_valid = 1'b1;
						w_op = 4'h6;
						w_bank = refresh_bank_i;
						w_do_pre = 1'b1;
					end
				end
				else if (w_refpb_safe) begin
					w_valid = 1'b1;
					w_op = 4'h9;
					w_bank = refresh_bank_i;
					w_grant = 1'b1;
				end
			end
			else if (w_any_active) begin
				if (w_rfsh_pre_found) begin
					w_valid = 1'b1;
					w_op = 4'h6;
					w_bank = w_rfsh_pre_bank;
					w_do_pre = 1'b1;
				end
			end
			else if (w_ref_safe) begin
				w_valid = 1'b1;
				w_op = 4'h8;
				w_grant = 1'b1;
			end
		end
		else if (zq_req_i) begin
			if (w_any_active) begin
				if (w_rfsh_pre_found) begin
					w_valid = 1'b1;
					w_op = 4'h6;
					w_bank = w_rfsh_pre_bank;
					w_do_pre = 1'b1;
				end
			end
			else if (w_zq_safe) begin
				w_valid = 1'b1;
				w_op = 4'hb;
				w_zq_grant = 1'b1;
			end
		end
		else if (((((w_pick_class == 2'd1) && rd_col_f) && rd_issue_ready_i) && w_rd_turn_live) && !(((w_col_wrf && wr_col_f) && wr_commit_ready_i) && w_wr_turn_live)) begin
			w_bank = rd_col_bank;
			w_col = rd_col_col;
			w_valid = 1'b1;
			w_op = (rd_col_ap ? 4'h3 : 4'h2);
			w_ap_out = rd_col_ap;
			w_do_rd = 1'b1;
			w_rd_issue = 1'b1;
			w_issue_slot = rd_col_s;
		end
		else if ((((w_pick_class == 2'd1) && wr_col_f) && wr_commit_ready_i) && w_wr_turn_live) begin
			w_bank = wr_col_bank;
			w_col = wr_col_col;
			w_valid = 1'b1;
			w_op = (wr_col_ap ? 4'h5 : 4'h4);
			w_ap_out = wr_col_ap;
			w_do_wr = 1'b1;
			w_wr_commit = 1'b1;
			w_commit_slot = wr_col_s;
		end
		else if ((((w_pick_class == 2'd2) && rd_act_f) && w_act_gate_live) && !(w_act_wrf && wr_act_f)) begin
			w_valid = 1'b1;
			w_op = 4'h1;
			w_bank = rd_act_bank;
			w_row = rd_act_row;
			w_do_act = 1'b1;
		end
		else if (((w_pick_class == 2'd2) && wr_act_f) && w_act_gate_live) begin
			w_valid = 1'b1;
			w_op = 4'h1;
			w_bank = wr_act_bank;
			w_row = wr_act_row;
			w_do_act = 1'b1;
		end
		else if (((w_pick_class == 2'd3) && rd_pre_f) && !(w_pre_wrf && wr_pre_f)) begin
			w_valid = 1'b1;
			w_op = 4'h6;
			w_bank = rd_pre_bank;
			w_do_pre = 1'b1;
		end
		else if ((w_pick_class == 2'd3) && wr_pre_f) begin
			w_valid = 1'b1;
			w_op = 4'h6;
			w_bank = wr_pre_bank;
			w_do_pre = 1'b1;
		end
		else if (((timeout_pre_req_i && r_bank_row_active[(RK0 * NUM_BANKS) + timeout_pre_bank_i]) && r_bank_pre_ready[(RK0 * NUM_BANKS) + timeout_pre_bank_i]) && !w_guarded[timeout_pre_bank_i]) begin
			w_valid = 1'b1;
			w_op = 4'h6;
			w_bank = timeout_pre_bank_i;
			w_do_pre = 1'b1;
		end
	end
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_dir_rr <= 1'b0;
		else if (w_fire_out && (((r_do_rd || r_do_wr) || r_do_act) || r_do_pre))
			r_dir_rr <= ~r_dir_rr;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_pick_valid <= 1'b0;
			r_do_act <= 1'b0;
			r_do_rd <= 1'b0;
			r_do_wr <= 1'b0;
			r_do_pre <= 1'b0;
			r_grant <= 1'b0;
			r_wr_commit <= 1'b0;
			r_rd_issue <= 1'b0;
			r_zq_grant <= 1'b0;
		end
		else if (w_out_ready) begin
			r_pick_valid <= w_valid;
			r_op <= w_op;
			r_bank <= w_bank;
			r_row <= w_row;
			r_col_out <= w_col;
			r_ap_out <= w_ap_out;
			r_do_act <= w_do_act;
			r_do_rd <= w_do_rd;
			r_do_wr <= w_do_wr;
			r_do_pre <= w_do_pre;
			r_grant <= w_grant;
			r_zq_grant <= w_zq_grant;
			r_wr_commit <= w_wr_commit;
			r_commit_slot <= w_commit_slot;
			r_rd_issue <= w_rd_issue;
			r_issue_slot <= w_issue_slot;
		end
	assign cmd_valid_o = r_pick_valid && w_out_safe;
	assign cmd_op_o = r_op;
	function automatic signed [RKW - 1:0] sv2v_cast_6B7F8_signed;
		input reg signed [RKW - 1:0] inp;
		sv2v_cast_6B7F8_signed = inp;
	endfunction
	assign cmd_rank_o = sv2v_cast_6B7F8_signed(RK0);
	assign cmd_bank_o = r_bank;
	assign cmd_row_o = r_row;
	assign cmd_col_o = r_col_out;
	assign cmd_ap_o = r_ap_out;
	assign evt_act_o = w_fire_out && r_do_act;
	assign evt_rd_o = w_fire_out && r_do_rd;
	assign evt_wr_o = w_fire_out && r_do_wr;
	assign evt_pre_o = w_fire_out && r_do_pre;
	assign evt_ap_o = r_ap_out;
	assign evt_rank_o = sv2v_cast_6B7F8_signed(RK0);
	assign evt_bank_o = r_bank;
	assign evt_row_o = r_row;
	assign wr_commit_valid_o = w_fire_out && r_wr_commit;
	assign wr_commit_slot_o = r_commit_slot;
	assign rd_issue_valid_o = w_fire_out && r_rd_issue;
	assign rd_issue_slot_o = r_issue_slot;
	assign refresh_grant_o = w_fire_out && r_grant;
	assign zq_grant_o = w_fire_out && r_zq_grant;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_guard0 <= 1'sb0;
			r_guard1 <= 1'sb0;
			r_ap_closing <= 1'sb0;
			r_wrfire0 <= 1'b0;
			r_wrfire1 <= 1'b0;
			r_rdfire0 <= 1'b0;
			r_rdfire1 <= 1'b0;
			r_apguard0 <= 1'sb0;
			r_apguard1 <= 1'sb0;
			r_preguard0 <= 1'sb0;
			r_preguard1 <= 1'sb0;
			r_preguard2 <= 1'sb0;
		end
		else begin
			r_guard1 <= r_guard0;
			r_guard0 <= 1'sb0;
			r_ap_closing <= w_ap_fire_bank | (r_ap_closing & r_bank_row_active[RK0 * NUM_BANKS+:NUM_BANKS]);
			if (w_fire_out && (((r_do_act || r_do_pre) || r_do_rd) || r_do_wr))
				r_guard0 <= sv2v_cast_A03D0_signed(1) << r_bank;
			r_preguard2 <= r_preguard1;
			r_preguard1 <= r_preguard0;
			r_preguard0 <= (w_fire_out && r_do_pre ? sv2v_cast_A03D0_signed(1) << r_bank : {NUM_BANKS {1'sb0}});
			r_wrfire1 <= r_wrfire0;
			r_wrfire0 <= w_fire_out && r_do_wr;
			r_rdfire1 <= r_rdfire0;
			r_rdfire0 <= w_fire_out && r_do_rd;
			r_apguard1 <= r_apguard0;
			r_apguard0 <= 1'sb0;
			if ((w_fire_out && (r_do_rd || r_do_wr)) && r_ap_out)
				r_apguard0 <= sv2v_cast_A03D0_signed(1) << r_bank;
		end
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_rfc_cnt <= 1'sb0;
		else if (w_fire_out && r_grant)
			r_rfc_cnt <= ((r_op == 4'h9) && (t_rfc_pb_i != 8'd0) ? {8'h00, t_rfc_pb_i} : t_rfc_i);
		else if (w_rfc_busy)
			r_rfc_cnt <= r_rfc_cnt - 16'd1;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_zqcs_cnt <= 1'sb0;
		else if (w_fire_out && r_zq_grant)
			r_zqcs_cnt <= t_zqcs_i;
		else if (w_zq_busy)
			r_zqcs_cnt <= r_zqcs_cnt - 16'd1;
	initial _sv2v_0 = 0;
endmodule
