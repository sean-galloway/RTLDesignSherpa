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
