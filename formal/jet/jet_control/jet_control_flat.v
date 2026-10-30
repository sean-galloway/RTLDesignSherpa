module jet_mshr (
	clk,
	rst_n,
	alloc_i,
	alloc_line_i,
	alloc_set_i,
	alloc_cls_i,
	alloc_install_i,
	alloc_victim_way_i,
	alloc_wb_slot_i,
	alloc_wb_valid_i,
	alloc_seq_i,
	alloc_gnt_o,
	alloc_idx_o,
	full_o,
	set_full_o,
	lkup_line_i,
	lkup_match_o,
	lkup_reg_match_o,
	lkup_reg_match_idx_o,
	lkup_reg_match_cls_o,
	lkup_match_idx_o,
	lkup_match_cls_o,
	sn_line_i,
	sn_match_o,
	sn_match_idx_o,
	sn_beats_rcvd_o,
	sn_install_o,
	merge_i,
	merge_idx_i,
	merge_seq_i,
	beat_i,
	beat_idx_i,
	beat_num_i,
	sn_eff_i,
	sn_eff_idx_i,
	sn_eff_value_i,
	retire_i,
	retire_idx_i,
	cpl_idx_i,
	cpl_line_o,
	cpl_install_o,
	cpl_pend_eff_o,
	cpl_merge_seqs_o,
	cpl_merge_count_o,
	cpl_wb_slot_o,
	cpl_wb_valid_o,
	occupancy_o,
	alloc_o,
	alloc_set_o,
	alloc_cls_o,
	merge_o,
	merge_idx_o,
	merge_depth_o,
	retire_o,
	retire_idx_o
);
	reg _sv2v_0;
	localparam signed [31:0] jet_pkg_MSHR_COUNT = 8;
	parameter signed [31:0] MSHR_COUNT = jet_pkg_MSHR_COUNT;
	localparam signed [31:0] l1_pkg_AMBER_SETS = 128;
	parameter signed [31:0] SETS = l1_pkg_AMBER_SETS;
	localparam signed [31:0] l1_pkg_AMBER_WAYS = 4;
	parameter signed [31:0] WAYS = l1_pkg_AMBER_WAYS;
	localparam signed [31:0] l1_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] l1_pkg_AMBER_LINE_BYTES = 64;
	parameter signed [31:0] LINE_W = 26;
	localparam signed [31:0] jet_pkg_RSP_DEPTH = 10;
	localparam signed [31:0] jet_pkg_SEQ_W = 4;
	parameter signed [31:0] SEQ_W = jet_pkg_SEQ_W;
	localparam signed [31:0] jet_pkg_VICTIM_DEPTH = 2;
	parameter signed [31:0] VICTIM_DEPTH = jet_pkg_VICTIM_DEPTH;
	localparam signed [31:0] SET_W = $clog2(SETS);
	localparam signed [31:0] WAY_W = $clog2(WAYS);
	localparam signed [31:0] MW = $clog2(MSHR_COUNT);
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] l1_pkg_AMBER_FILL_BEATS = 8;
	localparam signed [31:0] FILL_BEATS = l1_pkg_AMBER_FILL_BEATS;
	localparam signed [31:0] BEAT_W = 3;
	localparam signed [31:0] WB_W = (VICTIM_DEPTH <= 2 ? 1 : $clog2(VICTIM_DEPTH));
	localparam signed [31:0] CLAIM_W = $clog2(WAYS + 1);
	input wire clk;
	input wire rst_n;
	input wire alloc_i;
	input wire [LINE_W - 1:0] alloc_line_i;
	input wire [SET_W - 1:0] alloc_set_i;
	input wire [1:0] alloc_cls_i;
	input wire alloc_install_i;
	input wire [WAY_W - 1:0] alloc_victim_way_i;
	input wire [WB_W - 1:0] alloc_wb_slot_i;
	input wire alloc_wb_valid_i;
	input wire [SEQ_W - 1:0] alloc_seq_i;
	output wire alloc_gnt_o;
	output wire [MW - 1:0] alloc_idx_o;
	output wire full_o;
	output wire set_full_o;
	input wire [LINE_W - 1:0] lkup_line_i;
	output reg lkup_match_o;
	output wire lkup_reg_match_o;
	output reg [MW - 1:0] lkup_reg_match_idx_o;
	output wire [1:0] lkup_reg_match_cls_o;
	output reg [MW - 1:0] lkup_match_idx_o;
	output wire [1:0] lkup_match_cls_o;
	input wire [LINE_W - 1:0] sn_line_i;
	output reg sn_match_o;
	output reg [MW - 1:0] sn_match_idx_o;
	output wire [7:0] sn_beats_rcvd_o;
	output wire sn_install_o;
	input wire merge_i;
	input wire [MW - 1:0] merge_idx_i;
	input wire [SEQ_W - 1:0] merge_seq_i;
	input wire beat_i;
	input wire [MW - 1:0] beat_idx_i;
	input wire [2:0] beat_num_i;
	input wire sn_eff_i;
	input wire [MW - 1:0] sn_eff_idx_i;
	input wire [1:0] sn_eff_value_i;
	input wire retire_i;
	input wire [MW - 1:0] retire_idx_i;
	input wire [MW - 1:0] cpl_idx_i;
	output reg [LINE_W - 1:0] cpl_line_o;
	output reg cpl_install_o;
	output reg [1:0] cpl_pend_eff_o;
	output reg [(MSHR_COUNT * SEQ_W) - 1:0] cpl_merge_seqs_o;
	output reg [MW:0] cpl_merge_count_o;
	output reg [WB_W - 1:0] cpl_wb_slot_o;
	output reg cpl_wb_valid_o;
	output reg [MW:0] occupancy_o;
	output wire alloc_o;
	output wire [SET_W - 1:0] alloc_set_o;
	output wire [1:0] alloc_cls_o;
	output wire merge_o;
	output wire [MW - 1:0] merge_idx_o;
	output wire [MW:0] merge_depth_o;
	output wire retire_o;
	output wire [MW - 1:0] retire_idx_o;
	initial begin
		if ((MSHR_COUNT < 2) || (MSHR_COUNT > 16))
			$display("Error [%0t] .flat_build/prep/jet_mshr.sv:224:13 - jet_mshr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_mshr: MSHR_COUNT must be in 2..16 (J1)");
		if ((SETS & (SETS - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_mshr.sv:226:13 - jet_mshr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_mshr: SETS must be a power of two");
		if (((WAYS & (WAYS - 1)) != 0) || (WAYS < 2))
			$display("Error [%0t] .flat_build/prep/jet_mshr.sv:228:13 - jet_mshr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_mshr: WAYS must be a power of two >= 2");
		if (LINE_W <= SET_W)
			$display("Error [%0t] .flat_build/prep/jet_mshr.sv:230:13 - jet_mshr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_mshr: LINE_W must exceed the set-index width");
	end
	reg [MSHR_COUNT - 1:0] r_valid;
	reg [LINE_W - 1:0] r_line [0:MSHR_COUNT - 1];
	reg [1:0] r_cls [0:MSHR_COUNT - 1];
	reg r_install [0:MSHR_COUNT - 1];
	reg [WAY_W - 1:0] r_victim_way [0:MSHR_COUNT - 1];
	reg [WB_W - 1:0] r_wb_slot [0:MSHR_COUNT - 1];
	reg r_wb_valid [0:MSHR_COUNT - 1];
	reg [SEQ_W - 1:0] r_merge [0:(MSHR_COUNT * MSHR_COUNT) - 1];
	reg [MW:0] r_merge_count [0:MSHR_COUNT - 1];
	reg [7:0] r_beats_rcvd [0:MSHR_COUNT - 1];
	reg [1:0] r_pend_eff [0:MSHR_COUNT - 1];
	reg [SEQ_W - 1:0] r_seq [0:MSHR_COUNT - 1];
	reg [CLAIM_W - 1:0] r_set_claims [0:SETS - 1];
	reg w_any_free;
	reg [MW - 1:0] w_free_sel;
	function automatic signed [MW - 1:0] sv2v_cast_73DDD_signed;
		input reg signed [MW - 1:0] inp;
		sv2v_cast_73DDD_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_any_free = 1'b0;
		w_free_sel = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] e;
			for (e = MSHR_COUNT - 1; e >= 0; e = e - 1)
				if (!r_valid[e]) begin
					w_any_free = 1'b1;
					w_free_sel = sv2v_cast_73DDD_signed(e);
				end
		end
	end
	assign full_o = ~w_any_free;
	function automatic signed [CLAIM_W - 1:0] sv2v_cast_699E0_signed;
		input reg signed [CLAIM_W - 1:0] inp;
		sv2v_cast_699E0_signed = inp;
	endfunction
	assign set_full_o = r_set_claims[alloc_set_i] == sv2v_cast_699E0_signed(WAYS);
	assign alloc_gnt_o = (alloc_i & w_any_free) & ~set_full_o;
	assign alloc_idx_o = w_free_sel;
	reg [MSHR_COUNT - 1:0] w_lkup_hits;
	reg [MSHR_COUNT - 1:0] w_sn_hits;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] e;
			for (e = 0; e < MSHR_COUNT; e = e + 1)
				begin
					w_lkup_hits[e] = r_valid[e] & (r_line[e] == lkup_line_i);
					w_sn_hits[e] = r_valid[e] & (r_line[e] == sn_line_i);
				end
		end
	end
	wire w_lkup_alloc_hit = alloc_gnt_o & (alloc_line_i == lkup_line_i);
	wire w_sn_alloc_hit = alloc_gnt_o & (alloc_line_i == sn_line_i);
	always @(*) begin
		if (_sv2v_0)
			;
		lkup_match_o = 1'b0;
		lkup_match_idx_o = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] e;
			for (e = MSHR_COUNT - 1; e >= 0; e = e - 1)
				if (w_lkup_hits[e]) begin
					lkup_match_o = 1'b1;
					lkup_match_idx_o = sv2v_cast_73DDD_signed(e);
				end
		end
		if (!lkup_match_o && w_lkup_alloc_hit) begin
			lkup_match_o = 1'b1;
			lkup_match_idx_o = w_free_sel;
		end
	end
	assign lkup_match_cls_o = (|w_lkup_hits ? r_cls[lkup_match_idx_o] : alloc_cls_i);
	assign lkup_reg_match_o = |w_lkup_hits;
	always @(*) begin
		if (_sv2v_0)
			;
		lkup_reg_match_idx_o = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] e;
			for (e = MSHR_COUNT - 1; e >= 0; e = e - 1)
				if (w_lkup_hits[e])
					lkup_reg_match_idx_o = sv2v_cast_73DDD_signed(e);
		end
	end
	assign lkup_reg_match_cls_o = r_cls[lkup_reg_match_idx_o];
	always @(*) begin
		if (_sv2v_0)
			;
		sn_match_o = 1'b0;
		sn_match_idx_o = 1'sb0;
		begin : sv2v_autoblock_5
			reg signed [31:0] e;
			for (e = MSHR_COUNT - 1; e >= 0; e = e - 1)
				if (w_sn_hits[e]) begin
					sn_match_o = 1'b1;
					sn_match_idx_o = sv2v_cast_73DDD_signed(e);
				end
		end
		if (!sn_match_o && w_sn_alloc_hit) begin
			sn_match_o = 1'b1;
			sn_match_idx_o = w_free_sel;
		end
	end
	assign sn_beats_rcvd_o = (|w_sn_hits ? r_beats_rcvd[sn_match_idx_o] : {8 {1'sb0}});
	assign sn_install_o = (|w_sn_hits ? r_install[sn_match_idx_o] : w_sn_alloc_hit & alloc_install_i);
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		cpl_line_o = r_line[cpl_idx_i];
		cpl_install_o = r_install[cpl_idx_i];
		cpl_pend_eff_o = r_pend_eff[cpl_idx_i];
		cpl_merge_count_o = r_merge_count[cpl_idx_i];
		cpl_wb_slot_o = r_wb_slot[cpl_idx_i];
		cpl_wb_valid_o = r_wb_valid[cpl_idx_i];
		begin : sv2v_autoblock_6
			reg signed [31:0] k;
			for (k = 0; k < MSHR_COUNT; k = k + 1)
				cpl_merge_seqs_o[k * SEQ_W+:SEQ_W] = r_merge[(sv2v_cast_32(cpl_idx_i) * MSHR_COUNT) + k];
		end
	end
	function automatic [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] sv2v_cast_5C329;
		input reg [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] inp;
		sv2v_cast_5C329 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		occupancy_o = 1'sb0;
		begin : sv2v_autoblock_7
			reg signed [31:0] e;
			for (e = 0; e < MSHR_COUNT; e = e + 1)
				occupancy_o = occupancy_o + sv2v_cast_5C329(r_valid[e]);
		end
	end
	wire w_retire_live = retire_i & r_valid[retire_idx_i];
	assign alloc_o = alloc_gnt_o;
	assign alloc_set_o = alloc_set_i;
	assign alloc_cls_o = alloc_cls_i;
	function automatic signed [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] sv2v_cast_5C329_signed;
		input reg signed [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] inp;
		sv2v_cast_5C329_signed = inp;
	endfunction
	assign merge_o = merge_i & (r_merge_count[merge_idx_i] < sv2v_cast_5C329_signed(MSHR_COUNT));
	assign merge_idx_o = merge_idx_i;
	assign merge_depth_o = r_merge_count[merge_idx_i] + 1'b1;
	assign retire_o = w_retire_live;
	assign retire_idx_o = retire_idx_i;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_valid <= 1'sb0;
			begin : sv2v_autoblock_8
				reg signed [31:0] e;
				for (e = 0; e < MSHR_COUNT; e = e + 1)
					begin
						r_line[e] <= 1'sb0;
						r_cls[e] <= 1'sb0;
						r_install[e] <= 1'b0;
						r_victim_way[e] <= 1'sb0;
						r_wb_slot[e] <= 1'sb0;
						r_wb_valid[e] <= 1'b0;
						r_merge_count[e] <= 1'sb0;
						r_beats_rcvd[e] <= 1'sb0;
						r_pend_eff[e] <= 1'sb0;
						r_seq[e] <= 1'sb0;
					end
			end
			begin : sv2v_autoblock_9
				reg signed [31:0] k;
				for (k = 0; k < (MSHR_COUNT * MSHR_COUNT); k = k + 1)
					r_merge[k] <= 1'sb0;
			end
		end
		else begin
			if (merge_i && (r_merge_count[merge_idx_i] < sv2v_cast_5C329_signed(MSHR_COUNT))) begin
				r_merge[(sv2v_cast_32(merge_idx_i) * MSHR_COUNT) + sv2v_cast_32(r_merge_count[merge_idx_i])] <= merge_seq_i;
				r_merge_count[merge_idx_i] <= r_merge_count[merge_idx_i] + 1'b1;
			end
			if (beat_i)
				r_beats_rcvd[beat_idx_i][beat_num_i] <= 1'b1;
			if (sn_eff_i)
				r_pend_eff[sn_eff_idx_i] <= sn_eff_value_i;
			if (retire_i)
				r_valid[retire_idx_i] <= 1'b0;
			if (alloc_gnt_o) begin
				r_valid[w_free_sel] <= 1'b1;
				r_line[w_free_sel] <= alloc_line_i;
				r_cls[w_free_sel] <= alloc_cls_i;
				r_install[w_free_sel] <= alloc_install_i;
				r_victim_way[w_free_sel] <= alloc_victim_way_i;
				r_wb_slot[w_free_sel] <= alloc_wb_slot_i;
				r_wb_valid[w_free_sel] <= alloc_wb_valid_i;
				r_merge[sv2v_cast_32(w_free_sel) * MSHR_COUNT] <= alloc_seq_i;
				r_merge_count[w_free_sel] <= {{MW {1'b0}}, 1'b1};
				r_beats_rcvd[w_free_sel] <= 1'sb0;
				r_pend_eff[w_free_sel] <= 1'sb0;
				r_seq[w_free_sel] <= alloc_seq_i;
			end
		end
	wire [SET_W - 1:0] w_retire_set = r_line[retire_idx_i][SET_W - 1:0];
	function automatic signed [SET_W - 1:0] sv2v_cast_DCA8A_signed;
		input reg signed [SET_W - 1:0] inp;
		sv2v_cast_DCA8A_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin : sv2v_autoblock_10
			reg signed [31:0] s;
			for (s = 0; s < SETS; s = s + 1)
				r_set_claims[s] <= 1'sb0;
		end
		else begin : sv2v_autoblock_11
			reg signed [31:0] s;
			for (s = 0; s < SETS; s = s + 1)
				case ({alloc_gnt_o & (alloc_set_i == sv2v_cast_DCA8A_signed(s)), w_retire_live & (w_retire_set == sv2v_cast_DCA8A_signed(s))})
					2'b10: r_set_claims[s] <= r_set_claims[s] + 1'b1;
					2'b01: r_set_claims[s] <= r_set_claims[s] - 1'b1;
					default:
						;
				endcase
		end
	initial _sv2v_0 = 0;
endmodule
module jet_wb_buffer (
	clk,
	rst_n,
	cap_i,
	cap_line_i,
	cap_beat_i,
	cap_beat_data_i,
	cap_gnt_o,
	cap_slot_o,
	wb_full_o,
	drain_valid_o,
	drain_addr_o,
	drain_data_o,
	drain_done_i,
	sn_line_i,
	sn_hit_o,
	sn_data_o,
	sn_bresp_cycle_o,
	sn_eff_i,
	wb_occupancy_o
);
	reg _sv2v_0;
	localparam signed [31:0] jet_pkg_VICTIM_DEPTH = 2;
	parameter signed [31:0] VICTIM_DEPTH = jet_pkg_VICTIM_DEPTH;
	localparam signed [31:0] l1_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] l1_pkg_AMBER_LINE_BYTES = 64;
	parameter signed [31:0] LINE_W = 26;
	parameter signed [31:0] ADDR_WIDTH = l1_pkg_AMBER_ADDR_WIDTH;
	parameter signed [31:0] LINE_BYTES = l1_pkg_AMBER_LINE_BYTES;
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	parameter signed [31:0] BUS_WIDTH = l1_pkg_AMBER_BUS_WIDTH;
	localparam signed [31:0] STRB_W = BUS_WIDTH / 8;
	localparam signed [31:0] FILL_BEATS = LINE_BYTES / STRB_W;
	localparam signed [31:0] BEAT_W = $clog2(FILL_BEATS);
	localparam signed [31:0] LINE_WIDTH = LINE_BYTES * 8;
	localparam signed [31:0] OFFSET_W = $clog2(LINE_BYTES);
	localparam signed [31:0] SLOT_W = (VICTIM_DEPTH <= 2 ? 1 : $clog2(VICTIM_DEPTH));
	localparam signed [31:0] OCC_W = $clog2(VICTIM_DEPTH + 1);
	input wire clk;
	input wire rst_n;
	input wire cap_i;
	input wire [LINE_W - 1:0] cap_line_i;
	input wire cap_beat_i;
	input wire [BUS_WIDTH - 1:0] cap_beat_data_i;
	output wire cap_gnt_o;
	output wire [SLOT_W - 1:0] cap_slot_o;
	output wire wb_full_o;
	output wire drain_valid_o;
	output wire [ADDR_WIDTH - 1:0] drain_addr_o;
	output wire [LINE_WIDTH - 1:0] drain_data_o;
	input wire drain_done_i;
	input wire [LINE_W - 1:0] sn_line_i;
	output wire sn_hit_o;
	output wire [LINE_WIDTH - 1:0] sn_data_o;
	output wire sn_bresp_cycle_o;
	input wire [1:0] sn_eff_i;
	output reg [OCC_W - 1:0] wb_occupancy_o;
	initial if ((LINE_W + OFFSET_W) != ADDR_WIDTH)
		$display("Error [%0t] .flat_build/prep/jet_wb_buffer.sv:149:13 - jet_wb_buffer.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_wb_buffer: LINE_W + $clog2(LINE_BYTES) must equal ADDR_WIDTH");
	initial begin
		if ((VICTIM_DEPTH < 1) || (VICTIM_DEPTH > 4))
			$display("Error [%0t] .flat_build/prep/jet_wb_buffer.sv:159:13 - jet_wb_buffer.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_wb_buffer: VICTIM_DEPTH must be in 1..4 (J5)");
		if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_wb_buffer.sv:161:13 - jet_wb_buffer.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_wb_buffer: LINE_BYTES must be a power of two");
		if ((BUS_WIDTH % 8) != 0)
			$display("Error [%0t] .flat_build/prep/jet_wb_buffer.sv:163:13 - jet_wb_buffer.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_wb_buffer: BUS_WIDTH must be a multiple of 8");
		if (FILL_BEATS < 2)
			$display("Error [%0t] .flat_build/prep/jet_wb_buffer.sv:165:13 - jet_wb_buffer.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_wb_buffer: LINE_BYTES / BUS_WIDTH*8 must be >= 2");
	end
	reg [VICTIM_DEPTH - 1:0] r_valid;
	reg [VICTIM_DEPTH - 1:0] r_allocated;
	reg [LINE_W - 1:0] r_line [0:VICTIM_DEPTH - 1];
	reg [LINE_WIDTH - 1:0] r_data [0:VICTIM_DEPTH - 1];
	reg [BEAT_W - 1:0] r_beats_rcvd [0:VICTIM_DEPTH - 1];
	reg [1:0] r_eff [0:VICTIM_DEPTH - 1];
	reg [SLOT_W - 1:0] r_head;
	reg [SLOT_W - 1:0] r_tail;
	reg [SLOT_W - 1:0] r_open_slot;
	reg r_open;
	wire w_any_free;
	assign w_any_free = ~(&r_allocated);
	assign wb_full_o = ~w_any_free;
	assign cap_gnt_o = cap_i & (r_open | w_any_free);
	assign cap_slot_o = (r_open ? r_open_slot : r_tail);
	wire [SLOT_W - 1:0] w_head_idx;
	assign w_head_idx = r_head;
	assign drain_valid_o = r_valid[w_head_idx];
	function automatic [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5;
		input reg [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5 = inp;
	endfunction
	assign drain_addr_o = sv2v_cast_A5DC5({r_line[w_head_idx], {OFFSET_W {1'b0}}});
	assign drain_data_o = r_data[w_head_idx];
	reg [SLOT_W - 1:0] w_sn_match_idx;
	reg w_sn_match;
	function automatic signed [SLOT_W - 1:0] sv2v_cast_7C1AF_signed;
		input reg signed [SLOT_W - 1:0] inp;
		sv2v_cast_7C1AF_signed = inp;
	endfunction
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_sn_match = 1'b0;
		w_sn_match_idx = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] offset;
			for (offset = 0; offset < VICTIM_DEPTH; offset = offset + 1)
				begin : sv2v_autoblock_2
					reg signed [31:0] s;
					s = (sv2v_cast_32_signed(r_head) + offset) % VICTIM_DEPTH;
					if ((!w_sn_match && r_valid[s]) && (r_line[s] == sn_line_i)) begin
						w_sn_match = 1'b1;
						w_sn_match_idx = sv2v_cast_7C1AF_signed(s);
					end
				end
		end
	end
	assign sn_hit_o = w_sn_match;
	assign sn_data_o = r_data[w_sn_match_idx];
	assign sn_bresp_cycle_o = (w_sn_match & drain_done_i) & (w_sn_match_idx == w_head_idx);
	function automatic [OCC_W - 1:0] sv2v_cast_8F697;
		input reg [OCC_W - 1:0] inp;
		sv2v_cast_8F697 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		wb_occupancy_o = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] s;
			for (s = 0; s < VICTIM_DEPTH; s = s + 1)
				wb_occupancy_o = wb_occupancy_o + sv2v_cast_8F697(r_valid[s]);
		end
	end
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic signed [BEAT_W - 1:0] sv2v_cast_6E789_signed;
		input reg signed [BEAT_W - 1:0] inp;
		sv2v_cast_6E789_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_valid <= 1'sb0;
			r_allocated <= 1'sb0;
			r_head <= 1'sb0;
			r_tail <= 1'sb0;
			r_open <= 1'b0;
			r_open_slot <= 1'sb0;
			begin : sv2v_autoblock_4
				reg signed [31:0] s;
				for (s = 0; s < VICTIM_DEPTH; s = s + 1)
					begin
						r_line[s] <= 1'sb0;
						r_data[s] <= 1'sb0;
						r_beats_rcvd[s] <= 1'sb0;
						r_eff[s] <= 1'sb0;
					end
			end
		end
		else begin
			if ((cap_i && !r_open) && w_any_free) begin
				r_open <= 1'b1;
				r_open_slot <= r_tail;
				r_allocated[r_tail] <= 1'b1;
				r_valid[r_tail] <= 1'b0;
				r_line[r_tail] <= cap_line_i;
				r_beats_rcvd[r_tail] <= 1'sb0;
				r_eff[r_tail] <= 2'b00;
				r_tail <= sv2v_cast_7C1AF_signed((sv2v_cast_32_signed(r_tail) + 1) % VICTIM_DEPTH);
			end
			if (r_open && cap_beat_i) begin : sv2v_autoblock_5
				reg [BEAT_W - 1:0] b;
				b = r_beats_rcvd[r_open_slot];
				r_data[r_open_slot][sv2v_cast_32(b) * BUS_WIDTH+:BUS_WIDTH] <= cap_beat_data_i;
				r_beats_rcvd[r_open_slot] <= b + 1'b1;
				if (b == sv2v_cast_6E789_signed(FILL_BEATS - 1)) begin
					r_valid[r_open_slot] <= 1'b1;
					r_open <= 1'b0;
				end
			end
			if (w_sn_match && (sn_eff_i != 2'b00))
				r_eff[w_sn_match_idx] <= sn_eff_i;
			if (drain_done_i && r_allocated[w_head_idx]) begin
				r_valid[w_head_idx] <= 1'b0;
				r_allocated[w_head_idx] <= 1'b0;
				r_head <= sv2v_cast_7C1AF_signed((sv2v_cast_32_signed(r_head) + 1) % VICTIM_DEPTH);
			end
		end
	initial _sv2v_0 = 0;
endmodule
module jet_rsp_seq (
	clk,
	rst_n,
	tag_req_i,
	tag_gnt_o,
	tag_o,
	cpl_i,
	cpl_tag_i,
	cpl_data_i,
	rsp_valid_o,
	rsp_data_o,
	rsp_ready_i
);
	localparam signed [31:0] jet_pkg_MSHR_COUNT = 8;
	localparam signed [31:0] jet_pkg_RSP_DEPTH = 10;
	parameter signed [31:0] RSP_DEPTH = jet_pkg_RSP_DEPTH;
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	parameter signed [31:0] BUS_WIDTH = l1_pkg_AMBER_BUS_WIDTH;
	localparam signed [31:0] jet_pkg_SEQ_W = 4;
	parameter signed [31:0] SEQ_W = jet_pkg_SEQ_W;
	localparam signed [31:0] OCC_W = $clog2(RSP_DEPTH + 1);
	input wire clk;
	input wire rst_n;
	input wire tag_req_i;
	output wire tag_gnt_o;
	output wire [SEQ_W - 1:0] tag_o;
	input wire cpl_i;
	input wire [SEQ_W - 1:0] cpl_tag_i;
	input wire [BUS_WIDTH - 1:0] cpl_data_i;
	output wire rsp_valid_o;
	output wire [BUS_WIDTH - 1:0] rsp_data_o;
	input wire rsp_ready_i;
	initial begin
		if ((RSP_DEPTH < 2) || (RSP_DEPTH > 32))
			$display("Error [%0t] .flat_build/prep/jet_rsp_seq.sv:122:13 - jet_rsp_seq.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_rsp_seq: RSP_DEPTH must be in 2..32 (J4)");
		if ((BUS_WIDTH < 8) || (BUS_WIDTH > 512))
			$display("Error [%0t] .flat_build/prep/jet_rsp_seq.sv:124:13 - jet_rsp_seq.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_rsp_seq: BUS_WIDTH out of supported range");
	end
	reg [RSP_DEPTH - 1:0] r_valid;
	reg [BUS_WIDTH - 1:0] r_data [0:RSP_DEPTH - 1];
	reg [SEQ_W - 1:0] r_alloc_tag;
	reg [SEQ_W - 1:0] r_rel_tag;
	reg [OCC_W - 1:0] r_occupancy;
	wire w_release;
	assign w_release = rsp_ready_i & rsp_valid_o;
	assign rsp_valid_o = r_valid[r_rel_tag];
	assign rsp_data_o = r_data[r_rel_tag];
	function automatic signed [OCC_W - 1:0] sv2v_cast_8F697_signed;
		input reg signed [OCC_W - 1:0] inp;
		sv2v_cast_8F697_signed = inp;
	endfunction
	assign tag_gnt_o = tag_req_i & ((r_occupancy < sv2v_cast_8F697_signed(RSP_DEPTH)) | w_release);
	assign tag_o = r_alloc_tag;
	function automatic signed [SEQ_W - 1:0] sv2v_cast_A6A5F_signed;
		input reg signed [SEQ_W - 1:0] inp;
		sv2v_cast_A6A5F_signed = inp;
	endfunction
	function automatic [OCC_W - 1:0] sv2v_cast_8F697;
		input reg [OCC_W - 1:0] inp;
		sv2v_cast_8F697 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_valid <= 1'sb0;
			r_alloc_tag <= 1'sb0;
			r_rel_tag <= 1'sb0;
			r_occupancy <= 1'sb0;
			begin : sv2v_autoblock_1
				reg signed [31:0] s;
				for (s = 0; s < RSP_DEPTH; s = s + 1)
					r_data[s] <= 1'sb0;
			end
		end
		else begin
			if (w_release) begin
				r_valid[r_rel_tag] <= 1'b0;
				if (r_rel_tag == sv2v_cast_A6A5F_signed(RSP_DEPTH - 1))
					r_rel_tag <= 1'sb0;
				else
					r_rel_tag <= r_rel_tag + 1'b1;
			end
			if (cpl_i) begin
				r_valid[cpl_tag_i] <= 1'b1;
				r_data[cpl_tag_i] <= cpl_data_i;
			end
			if (tag_req_i && tag_gnt_o) begin
				if (r_alloc_tag == sv2v_cast_A6A5F_signed(RSP_DEPTH - 1))
					r_alloc_tag <= 1'sb0;
				else
					r_alloc_tag <= r_alloc_tag + 1'b1;
			end
			r_occupancy <= (r_occupancy + sv2v_cast_8F697(tag_req_i & tag_gnt_o)) - sv2v_cast_8F697(w_release);
		end
endmodule
module jet_control (
	clk,
	rst_n,
	init_busy_o,
	lkup_valid_i,
	lkup_addr_i,
	lkup_we_i,
	lkup_be_i,
	lkup_wdata_i,
	lkup_ready_o,
	lkup_hit_o,
	lkup_merge_o,
	lkup_miss_alloc_o,
	lkup_upgrade_o,
	lkup_stall_o,
	lkup_stall_reason_o,
	lkup_wr_yield_o,
	cap_busy_o,
	tag_req_o,
	tag_gnt_i,
	tag_i,
	cpl_valid_o,
	cpl_tag_o,
	cpl_data_o,
	tag_a_set_o,
	tag_a_tag_state_i,
	tag_a_wr_en_o,
	tag_a_wr_way_onehot_o,
	tag_a_wr_set_o,
	tag_a_wr_tag_state_o,
	dat_a_addr_o,
	dat_a_way_o,
	dat_a_rdata_i,
	dat_a_wr_en_o,
	dat_a_wr_way_onehot_o,
	dat_a_wr_addr_o,
	dat_a_wr_wdata_o,
	dat_a_wr_be_o,
	dat_b_addr_o,
	dat_b_way_o,
	dat_b_rdata_i,
	repl_req_o,
	repl_set_o,
	repl_victim_way_i,
	repl_hit_o,
	repl_update_o,
	repl_hit_way_o,
	mshr_alloc_o,
	mshr_alloc_line_o,
	mshr_alloc_set_o,
	mshr_alloc_cls_o,
	mshr_alloc_install_o,
	mshr_alloc_victim_way_o,
	mshr_alloc_wb_slot_o,
	mshr_alloc_wb_valid_o,
	mshr_alloc_seq_o,
	mshr_alloc_gnt_i,
	mshr_alloc_idx_i,
	mshr_full_i,
	mshr_set_full_i,
	mshr_lkup_line_o,
	mshr_lkup_reg_match_i,
	mshr_lkup_reg_match_idx_i,
	mshr_lkup_reg_match_cls_i,
	mshr_cpl_idx_o,
	mshr_cpl_merge_count_i,
	mshr_cpl_line_i,
	mshr_cpl_pend_eff_i,
	mshr_cpl_merge_seqs_i,
	mshr_merge_o,
	mshr_merge_idx_o,
	mshr_merge_seq_o,
	mshr_beat_o,
	mshr_beat_idx_o,
	mshr_beat_num_o,
	mshr_retire_o,
	mshr_retire_idx_o,
	wb_cap_o,
	wb_cap_line_o,
	wb_cap_beat_o,
	wb_cap_beat_data_o,
	wb_cap_gnt_i,
	wb_cap_slot_i,
	wb_full_i,
	wb_sn_line_o,
	wb_sn_hit_i,
	wb_sn_eff_o,
	wb_sn_data_i,
	wb_sn_bresp_cycle_i,
	wb_drain_valid_i,
	drain_start_o,
	drain_done_i,
	tag_b_req_o,
	tag_b_set_o,
	tag_b_tag_state_i,
	mshr_sn_line_o,
	mshr_sn_match_i,
	mshr_sn_match_idx_i,
	mshr_sn_beats_rcvd_i,
	mshr_sn_install_i,
	mshr_sn_eff_o,
	mshr_sn_eff_idx_o,
	mshr_sn_eff_value_o,
	sn_req_i,
	sn_want_i,
	sn_addr_i,
	sn_type_i,
	sn_ready_o,
	sn_safe_o,
	sn_crresp_o,
	sn_cddata_o,
	sn_cdlast_o,
	sn_cdvalid_o,
	sn_cdready_i,
	fill_start_o,
	fill_addr_o,
	fill_cls_o,
	fill_accept_i,
	fill_pass_dirty_i,
	fill_beat_valid_i,
	fill_beat_idx_i,
	fill_beat_num_i,
	fill_done_i,
	fill_ar_done_i,
	cmt_busy_o,
	ctrl_error_o
);
	reg _sv2v_0;
	localparam signed [31:0] l1_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] l1_pkg_AMBER_SETS = 128;
	localparam signed [31:0] l1_pkg_AMBER_WAYS = 4;
	localparam signed [31:0] l1_pkg_AMBER_LINE_BYTES = 64;
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] jet_pkg_MSHR_COUNT = 8;
	localparam signed [31:0] jet_pkg_VICTIM_DEPTH = 2;
	localparam signed [31:0] SET_W = $clog2(16);
	localparam signed [31:0] OFF_W = $clog2(64);
	localparam signed [31:0] TAG_W = (32 - SET_W) - OFF_W;
	localparam signed [31:0] TSW = TAG_W + 3;
	localparam signed [31:0] STRB_W = 64 / 8;
	localparam signed [31:0] FILL_BEATS = 64 / STRB_W;
	localparam signed [31:0] BEAT_W = $clog2(FILL_BEATS);
	localparam signed [31:0] WAY_W = $clog2(2);
	localparam signed [31:0] MEM_ADDR_W = SET_W + BEAT_W;
	localparam signed [31:0] LINE_W = 32 - OFF_W;
	localparam signed [31:0] MW = $clog2(2);
	localparam signed [31:0] RSP_DEPTH = 2 + 2;
	localparam signed [31:0] SEQ_W = $clog2(RSP_DEPTH);
	localparam signed [31:0] WB_W = (2 <= 2 ? 1 : $clog2(2));
	localparam signed [31:0] LINE_BITS = 64 * 8;
	input wire clk;
	input wire rst_n;
	output wire init_busy_o;
	input wire lkup_valid_i;
	input wire [32 - 1:0] lkup_addr_i;
	input wire lkup_we_i;
	input wire [STRB_W - 1:0] lkup_be_i;
	input wire [64 - 1:0] lkup_wdata_i;
	output wire lkup_ready_o;
	output wire lkup_hit_o;
	output wire lkup_merge_o;
	output wire lkup_miss_alloc_o;
	output wire lkup_upgrade_o;
	output wire lkup_stall_o;
	output wire [2:0] lkup_stall_reason_o;
	output wire lkup_wr_yield_o;
	output wire cap_busy_o;
	output wire tag_req_o;
	input wire tag_gnt_i;
	input wire [SEQ_W - 1:0] tag_i;
	output wire cpl_valid_o;
	output wire [SEQ_W - 1:0] cpl_tag_o;
	output wire [64 - 1:0] cpl_data_o;
	output wire [SET_W - 1:0] tag_a_set_o;
	input wire [(2 * TSW) - 1:0] tag_a_tag_state_i;
	output wire tag_a_wr_en_o;
	output wire [2 - 1:0] tag_a_wr_way_onehot_o;
	output wire [SET_W - 1:0] tag_a_wr_set_o;
	output wire [TSW - 1:0] tag_a_wr_tag_state_o;
	output wire [MEM_ADDR_W - 1:0] dat_a_addr_o;
	output wire [WAY_W - 1:0] dat_a_way_o;
	input wire [64 - 1:0] dat_a_rdata_i;
	output wire dat_a_wr_en_o;
	output wire [2 - 1:0] dat_a_wr_way_onehot_o;
	output wire [MEM_ADDR_W - 1:0] dat_a_wr_addr_o;
	output wire [64 - 1:0] dat_a_wr_wdata_o;
	output wire [STRB_W - 1:0] dat_a_wr_be_o;
	output wire [MEM_ADDR_W - 1:0] dat_b_addr_o;
	output wire [WAY_W - 1:0] dat_b_way_o;
	input wire [64 - 1:0] dat_b_rdata_i;
	output wire repl_req_o;
	output wire [SET_W - 1:0] repl_set_o;
	input wire [WAY_W - 1:0] repl_victim_way_i;
	output wire repl_hit_o;
	output wire repl_update_o;
	output wire [WAY_W - 1:0] repl_hit_way_o;
	output wire mshr_alloc_o;
	output wire [LINE_W - 1:0] mshr_alloc_line_o;
	output wire [SET_W - 1:0] mshr_alloc_set_o;
	output wire [1:0] mshr_alloc_cls_o;
	output wire mshr_alloc_install_o;
	output wire [WAY_W - 1:0] mshr_alloc_victim_way_o;
	output wire [WB_W - 1:0] mshr_alloc_wb_slot_o;
	output wire mshr_alloc_wb_valid_o;
	output wire [SEQ_W - 1:0] mshr_alloc_seq_o;
	input wire mshr_alloc_gnt_i;
	input wire [MW - 1:0] mshr_alloc_idx_i;
	input wire mshr_full_i;
	input wire mshr_set_full_i;
	output wire [LINE_W - 1:0] mshr_lkup_line_o;
	input wire mshr_lkup_reg_match_i;
	input wire [MW - 1:0] mshr_lkup_reg_match_idx_i;
	input wire [1:0] mshr_lkup_reg_match_cls_i;
	output wire [MW - 1:0] mshr_cpl_idx_o;
	input wire [MW:0] mshr_cpl_merge_count_i;
	input wire [LINE_W - 1:0] mshr_cpl_line_i;
	input wire [1:0] mshr_cpl_pend_eff_i;
	input wire [(2 * SEQ_W) - 1:0] mshr_cpl_merge_seqs_i;
	output wire mshr_merge_o;
	output wire [MW - 1:0] mshr_merge_idx_o;
	output wire [SEQ_W - 1:0] mshr_merge_seq_o;
	output wire mshr_beat_o;
	output wire [MW - 1:0] mshr_beat_idx_o;
	output wire [BEAT_W - 1:0] mshr_beat_num_o;
	output wire mshr_retire_o;
	output wire [MW - 1:0] mshr_retire_idx_o;
	output wire wb_cap_o;
	output wire [LINE_W - 1:0] wb_cap_line_o;
	output wire wb_cap_beat_o;
	output wire [64 - 1:0] wb_cap_beat_data_o;
	input wire wb_cap_gnt_i;
	input wire [WB_W - 1:0] wb_cap_slot_i;
	input wire wb_full_i;
	output wire [LINE_W - 1:0] wb_sn_line_o;
	input wire wb_sn_hit_i;
	output wire [1:0] wb_sn_eff_o;
	input wire [LINE_BITS - 1:0] wb_sn_data_i;
	input wire wb_sn_bresp_cycle_i;
	input wire wb_drain_valid_i;
	output wire drain_start_o;
	input wire drain_done_i;
	output wire tag_b_req_o;
	output wire [SET_W - 1:0] tag_b_set_o;
	input wire [(2 * TSW) - 1:0] tag_b_tag_state_i;
	output wire [LINE_W - 1:0] mshr_sn_line_o;
	input wire mshr_sn_match_i;
	input wire [MW - 1:0] mshr_sn_match_idx_i;
	input wire [FILL_BEATS - 1:0] mshr_sn_beats_rcvd_i;
	input wire mshr_sn_install_i;
	output wire mshr_sn_eff_o;
	output wire [MW - 1:0] mshr_sn_eff_idx_o;
	output wire [1:0] mshr_sn_eff_value_o;
	input wire sn_req_i;
	input wire sn_want_i;
	input wire [32 - 1:0] sn_addr_i;
	input wire [2:0] sn_type_i;
	output wire sn_ready_o;
	output wire sn_safe_o;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_WIDTH = 5;
	output wire [4:0] sn_crresp_o;
	output wire [64 - 1:0] sn_cddata_o;
	output wire sn_cdlast_o;
	output wire sn_cdvalid_o;
	input wire sn_cdready_i;
	output wire fill_start_o;
	output wire [32 - 1:0] fill_addr_o;
	output wire [1:0] fill_cls_o;
	input wire fill_accept_i;
	input wire fill_pass_dirty_i;
	input wire fill_beat_valid_i;
	input wire [MW - 1:0] fill_beat_idx_i;
	input wire [BEAT_W - 1:0] fill_beat_num_i;
	input wire fill_done_i;
	input wire fill_ar_done_i;
	output wire cmt_busy_o;
	output wire ctrl_error_o;
	initial begin
		if ((16 & (16 - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_control.sv:428:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 16 must be a power of two");
		if ((64 & (64 - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_control.sv:430:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 64 must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_control.sv:432:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 64 / 64*8 must be a power of two");
		if ((64 % 8) != 0)
			$display("Error [%0t] .flat_build/prep/jet_control.sv:434:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 64 must be a multiple of 8");
		if (2 < 2)
			$display("Error [%0t] .flat_build/prep/jet_control.sv:436:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 2 must be >= 2");
		if ((2 < 2) || (2 > 16))
			$display("Error [%0t] .flat_build/prep/jet_control.sv:438:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 2 must be in 2..16 (J1)");
		if ((2 < 1) || (2 > 4))
			$display("Error [%0t] .flat_build/prep/jet_control.sv:440:13 - jet_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_control: 2 must be in 1..4 (J5)");
	end
	localparam [2:0] STALL_NONE = 3'd0;
	localparam [2:0] STALL_MSHR_FULL = 3'd1;
	localparam [2:0] STALL_WB = 3'd2;
	localparam [2:0] STALL_SET_OVERSUB = 3'd3;
	localparam [2:0] STALL_XCLASS = 3'd4;
	localparam [2:0] STALL_TAG_FULL = 3'd5;
	localparam [2:0] STALL_COMMIT = 3'd6;
	localparam [3:0] C_IDLE = 4'd0;
	localparam [3:0] C_MERGE = 4'd1;
	localparam [3:0] C_INSTALL = 4'd2;
	localparam [3:0] C_PEND = 4'd3;
	localparam [3:0] C_DEPOSIT = 4'd4;
	localparam [3:0] C_RETIRE = 4'd5;
	localparam [3:0] C_CU_MERGE = 4'd6;
	localparam [3:0] C_CU_INSTALL = 4'd7;
	localparam [3:0] C_CU_DEPOSIT = 4'd8;
	localparam signed [31:0] FQ_DEPTH = 2 + 1;
	localparam signed [31:0] FQ_W = $clog2(FQ_DEPTH);
	localparam [1:0] SN_IDLE = 2'd0;
	localparam [1:0] SN_DATA = 2'd1;
	localparam [1:0] SN_EFFECT = 2'd2;
	localparam [1:0] SRC_NONE = 2'd0;
	localparam [1:0] SRC_WB = 2'd1;
	localparam [1:0] SRC_MSHR = 2'd2;
	localparam [1:0] SRC_ARRAY = 2'd3;
	localparam [4:0] CRRESP_NO_DT = 5'b11000;
	reg r_init_busy;
	reg [SET_W - 1:0] r_init_cnt;
	reg r_cap_busy;
	reg [SET_W - 1:0] r_cap_set;
	reg [WAY_W - 1:0] r_cap_way;
	reg [LINE_W - 1:0] r_cap_line;
	reg [BEAT_W - 1:0] r_cap_beat;
	reg r_fill_pend;
	reg [32 - 1:0] r_fill_addr;
	reg [1:0] r_fill_cls;
	reg [MW - 1:0] r_fill_idx;
	reg r_ar_done;
	reg r_drain_busy;
	reg r_upgr_valid;
	reg [LINE_W - 1:0] r_upgr_line;
	reg [SET_W - 1:0] r_upgr_set;
	reg [WAY_W - 1:0] r_upgr_way;
	reg [SEQ_W - 1:0] r_upgr_seq;
	reg [BEAT_W - 1:0] r_upgr_beat;
	reg [STRB_W - 1:0] r_upgr_be;
	reg [64 - 1:0] r_upgr_wdata;
	reg r_upgr_killed;
	reg r_ctrl_err;
	reg [2 - 1:0] r_claim_vld;
	reg [SET_W - 1:0] r_claim_set [0:2 - 1];
	reg [WAY_W - 1:0] r_claim_way [0:2 - 1];
	reg [2 - 1:0] r_efill_done;
	reg [FQ_W - 1:0] r_fq_head;
	reg [FQ_W - 1:0] r_fq_tail;
	reg [FQ_W - 1:0] r_fq_done_ptr;
	reg [FQ_W:0] r_fq_cnt;
	reg [FQ_W:0] r_fq_undone;
	reg [MW - 1:0] r_fq_idx [0:FQ_DEPTH - 1];
	reg [1:0] r_fq_cls [0:FQ_DEPTH - 1];
	reg r_fq_pd [0:FQ_DEPTH - 1];
	reg r_fq_done [0:FQ_DEPTH - 1];
	reg r_req_we [0:(2 * 2) - 1];
	reg [BEAT_W - 1:0] r_req_beat [0:(2 * 2) - 1];
	reg [STRB_W - 1:0] r_req_be [0:(2 * 2) - 1];
	reg [64 - 1:0] r_req_wdata [0:(2 * 2) - 1];
	reg [3:0] r_cmt_state;
	reg [MW - 1:0] r_cmt_idx;
	reg [LINE_W - 1:0] r_cmt_line;
	reg [1:0] r_cmt_cls;
	reg r_cmt_pd;
	reg [1:0] r_cmt_pend;
	reg [WAY_W - 1:0] r_cmt_way;
	reg [MW:0] r_cmt_count;
	reg [SEQ_W - 1:0] r_cmt_seqs [0:2 - 1];
	reg [MW:0] r_cmt_k;
	reg [64 - 1:0] r_cmt_rdata [0:2 - 1];
	reg [1:0] r_sn_state;
	reg [LINE_W - 1:0] r_sn_line;
	reg [SET_W - 1:0] r_sn_set;
	reg [TAG_W - 1:0] r_sn_tag;
	reg [1:0] r_sn_src;
	reg r_sn_allb;
	reg [WAY_W - 1:0] r_sn_way;
	reg [MW - 1:0] r_sn_idx;
	reg [2:0] r_sn_ref;
	reg [2:0] r_sn_nxt;
	reg [BEAT_W - 1:0] r_sn_beat;
	reg [LINE_BITS - 1:0] r_sn_wb_data;
	reg [1:0] r_sn_pend [0:2 - 1];
	wire [TAG_W - 1:0] w_req_tag;
	wire [SET_W - 1:0] w_req_set;
	wire [BEAT_W - 1:0] w_req_beat;
	wire [LINE_W - 1:0] w_req_line;
	assign w_req_tag = lkup_addr_i[32 - 1-:TAG_W];
	assign w_req_set = lkup_addr_i[OFF_W+:SET_W];
	assign w_req_beat = lkup_addr_i[OFF_W - 1-:BEAT_W];
	assign w_req_line = lkup_addr_i[32 - 1:OFF_W];
	reg w_hit;
	reg [WAY_W - 1:0] w_hit_way;
	reg [2:0] w_hit_state;
	reg [2 - 1:0] w_hit_way_onehot;
	reg w_hit_claimed;
	function automatic signed [WAY_W - 1:0] sv2v_cast_19C97_signed;
		input reg signed [WAY_W - 1:0] inp;
		sv2v_cast_19C97_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_hit = 1'b0;
		w_hit_way = 1'sb0;
		w_hit_state = 3'b000;
		begin : sv2v_autoblock_1
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				if ((!w_hit && (tag_a_tag_state_i[(w * TSW) + (TSW - 1)-:TAG_W] == w_req_tag)) && (((tag_a_tag_state_i[(w * TSW) + 2-:3] == 3'b001) || (tag_a_tag_state_i[(w * TSW) + 2-:3] == 3'b010)) || (tag_a_tag_state_i[(w * TSW) + 2-:3] == 3'b011))) begin
					w_hit = 1'b1;
					w_hit_way = sv2v_cast_19C97_signed(w);
					w_hit_state = tag_a_tag_state_i[(w * TSW) + 2-:3];
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				w_hit_way_onehot[w] = w_hit_way == sv2v_cast_19C97_signed(w);
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_hit_claimed = 1'b0;
		begin : sv2v_autoblock_3
			reg signed [31:0] e;
			for (e = 0; e < 2; e = e + 1)
				if ((r_claim_vld[e] && (r_claim_set[e] == w_req_set)) && (r_claim_way[e] == w_hit_way))
					w_hit_claimed = 1'b1;
		end
	end
	wire w_serve_hit;
	wire w_hit_rd;
	wire w_hit_wr;
	wire w_hit_upgr;
	wire w_xclass;
	wire w_merge_room;
	wire [2:0] w_victim_state;
	wire [TAG_W - 1:0] w_victim_tag;
	wire w_victim_dirty;
	reg w_victim_claimed;
	wire w_wb_race;
	wire w_wb_block;
	wire w_upgr_victim_block;
	wire w_upgr_line_stall;
	assign w_serve_hit = w_hit & ~w_hit_claimed;
	assign w_hit_rd = w_serve_hit & ~lkup_we_i;
	assign w_hit_wr = (w_serve_hit & lkup_we_i) & (w_hit_state != 3'b001);
	assign w_hit_upgr = (w_serve_hit & lkup_we_i) & (w_hit_state == 3'b001);
	assign w_xclass = (mshr_lkup_reg_match_i & lkup_we_i) & (mshr_lkup_reg_match_cls_i == 2'b00);
	function automatic signed [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] sv2v_cast_5C329_signed;
		input reg signed [((MW + 0) >= 0 ? MW + 1 : 1 - (MW + 0)) - 1:0] inp;
		sv2v_cast_5C329_signed = inp;
	endfunction
	assign w_merge_room = mshr_cpl_merge_count_i < sv2v_cast_5C329_signed(2);
	assign w_victim_state = tag_a_tag_state_i[(repl_victim_way_i * TSW) + 2-:3];
	assign w_victim_tag = tag_a_tag_state_i[(repl_victim_way_i * TSW) + (TSW - 1)-:TAG_W];
	assign w_victim_dirty = w_victim_state == 3'b011;
	always @(*) begin
		if (_sv2v_0)
			;
		w_victim_claimed = 1'b0;
		begin : sv2v_autoblock_4
			reg signed [31:0] e;
			for (e = 0; e < 2; e = e + 1)
				if ((r_claim_vld[e] && (r_claim_set[e] == w_req_set)) && (r_claim_way[e] == repl_victim_way_i))
					w_victim_claimed = 1'b1;
		end
	end
	assign w_wb_race = wb_sn_hit_i | (r_cap_busy & (r_cap_line == w_req_line));
	assign w_wb_block = w_victim_dirty & (wb_full_i | r_cap_busy);
	assign w_upgr_victim_block = (r_upgr_valid & (r_upgr_set == w_req_set)) & (r_upgr_way == repl_victim_way_i);
	assign w_upgr_line_stall = (w_serve_hit & r_upgr_valid) & (r_upgr_line == w_req_line);
	wire [TAG_W - 1:0] w_sn_tag;
	wire [SET_W - 1:0] w_sn_set;
	wire [LINE_W - 1:0] w_sn_line;
	reg w_sn_thit;
	reg [WAY_W - 1:0] w_sn_tway;
	reg [2:0] w_sn_tstate;
	reg w_sn_tclaimed;
	wire w_src_wb;
	wire w_src_mshr;
	wire w_src_array;
	wire [1:0] w_sn_src;
	wire [2:0] w_sn_ref;
	wire [2:0] w_sn_nxt;
	wire w_sn_deliver;
	wire [4:0] w_crresp_raw;
	wire [4:0] w_sn_crresp;
	wire w_any_done;
	wire w_cu_completing;
	wire w_sn_gnt;
	wire w_sn_block_cpu;
	wire w_sn_eff_needed;
	wire w_sn_eff_done;
	wire [1:0] w_sn_eff_new;
	wire w_sn_tagwr;
	wire w_sn_portb;
	reg [2 - 1:0] w_sn_way_onehot;
	assign w_sn_tag = sn_addr_i[32 - 1-:TAG_W];
	assign w_sn_set = sn_addr_i[OFF_W+:SET_W];
	assign w_sn_line = sn_addr_i[32 - 1:OFF_W];
	assign tag_b_req_o = sn_req_i;
	assign tag_b_set_o = w_sn_set;
	assign wb_sn_line_o = (sn_req_i ? w_sn_line : (r_sn_state != SN_IDLE ? r_sn_line : w_req_line));
	assign mshr_sn_line_o = (sn_req_i ? w_sn_line : r_sn_line);
	always @(*) begin
		if (_sv2v_0)
			;
		w_sn_thit = 1'b0;
		w_sn_tway = 1'sb0;
		w_sn_tstate = 3'b000;
		begin : sv2v_autoblock_5
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				if ((!w_sn_thit && (tag_b_tag_state_i[(w * TSW) + (TSW - 1)-:TAG_W] == w_sn_tag)) && (((tag_b_tag_state_i[(w * TSW) + 2-:3] == 3'b001) || (tag_b_tag_state_i[(w * TSW) + 2-:3] == 3'b010)) || (tag_b_tag_state_i[(w * TSW) + 2-:3] == 3'b011))) begin
					w_sn_thit = 1'b1;
					w_sn_tway = sv2v_cast_19C97_signed(w);
					w_sn_tstate = tag_b_tag_state_i[(w * TSW) + 2-:3];
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_sn_tclaimed = 1'b0;
		begin : sv2v_autoblock_6
			reg signed [31:0] e;
			for (e = 0; e < 2; e = e + 1)
				if ((r_claim_vld[e] && (r_claim_set[e] == w_sn_set)) && (r_claim_way[e] == w_sn_tway))
					w_sn_tclaimed = 1'b1;
		end
	end
	assign w_src_wb = wb_sn_hit_i;
	wire [MW - 1:0] w_launch_idx;
	wire w_mshr_pre_ar;
	assign w_launch_idx = (r_fill_pend ? r_fill_idx : mshr_alloc_idx_i);
	assign w_mshr_pre_ar = mshr_sn_match_i & (((fill_start_o & (fill_cls_o != 2'b10)) & (mshr_sn_match_idx_i == w_launch_idx)) | ((((r_fq_undone != {(FQ_W >= 0 ? FQ_W + 1 : 1 - FQ_W) {1'sb0}}) & ~r_ar_done) & (r_fq_cls[r_fq_done_ptr] != 2'b10)) & (mshr_sn_match_idx_i == r_fq_idx[r_fq_done_ptr])));
	assign w_src_mshr = (~w_src_wb & mshr_sn_match_i) & ~w_mshr_pre_ar;
	assign w_src_array = ((~w_src_wb & ~w_src_mshr) & w_sn_thit) & ~w_sn_tclaimed;
	assign w_sn_src = (w_src_wb ? SRC_WB : (w_src_mshr ? SRC_MSHR : (w_src_array ? SRC_ARRAY : SRC_NONE)));
	assign w_sn_ref = (w_src_wb ? 3'b011 : (w_src_mshr ? (mshr_sn_install_i ? 3'b011 : 3'b001) : (w_src_array ? w_sn_tstate : 3'b000)));
	function automatic [2:0] l1_pkg_amber_snoop_next_state;
		input reg [2:0] state;
		input reg [2:0] snoop;
		reg [2:0] nxt;
		begin
			nxt = 3'b000;
			case (state)
				3'b011:
					case (snoop)
						3'b000, 3'b011: nxt = 3'b001;
						default: nxt = 3'b000;
					endcase
				3'b010:
					case (snoop)
						3'b000, 3'b001: nxt = 3'b001;
						3'b011: nxt = 3'b010;
						default: nxt = 3'b000;
					endcase
				3'b001:
					case (snoop)
						3'b000, 3'b001, 3'b011: nxt = 3'b001;
						default: nxt = 3'b000;
					endcase
				default: nxt = 3'b000;
			endcase
			l1_pkg_amber_snoop_next_state = nxt;
		end
	endfunction
	assign w_sn_nxt = l1_pkg_amber_snoop_next_state(w_sn_ref, sn_type_i);
	assign w_sn_deliver = (w_src_wb | w_src_array) | (w_src_mshr & (&mshr_sn_beats_rcvd_i));
	function automatic [4:0] l1_pkg_amber_snoop_crresp;
		input reg [2:0] state;
		input reg [2:0] snoop;
		reg dt;
		reg pd;
		reg is;
		reg wu;
		begin
			dt = 1'b0;
			pd = 1'b0;
			is = 1'b0;
			wu = 1'b0;
			case (state)
				3'b011:
					case (snoop)
						3'b000, 3'b011, 3'b100: begin
							dt = 1'b1;
							pd = 1'b1;
							is = 1'b1;
						end
						3'b001, 3'b010: begin
							dt = 1'b1;
							pd = 1'b1;
						end
						default:
							;
					endcase
				3'b010:
					case (snoop)
						3'b000, 3'b001: begin
							dt = 1'b1;
							is = 1'b1;
							wu = 1'b1;
						end
						3'b010: begin
							dt = 1'b1;
							wu = 1'b1;
						end
						3'b011: begin
							is = 1'b1;
							wu = 1'b1;
						end
						default:
							;
					endcase
				3'b001:
					case (snoop)
						3'b000, 3'b001: is = 1'b1;
						default:
							;
					endcase
				default:
					;
			endcase
			l1_pkg_amber_snoop_crresp = {wu, is, pd, 1'b0, dt};
		end
	endfunction
	assign w_crresp_raw = l1_pkg_amber_snoop_crresp(w_sn_ref, sn_type_i);
	assign w_sn_crresp = (w_sn_deliver ? w_crresp_raw : w_crresp_raw & CRRESP_NO_DT);
	assign sn_crresp_o = w_sn_crresp;
	assign w_any_done = r_fq_cnt != r_fq_undone;
	assign w_cu_completing = fill_done_i & (r_fq_cls[r_fq_done_ptr] == 2'b10);
	assign sn_safe_o = (((~r_init_busy & (r_sn_state == SN_IDLE)) & ~w_any_done) & ~r_cap_busy) & ~w_cu_completing;
	assign w_sn_gnt = sn_req_i & sn_safe_o;
	assign sn_ready_o = w_sn_gnt;
	assign w_sn_block_cpu = (w_sn_gnt | (r_sn_state != SN_IDLE)) | sn_want_i;
	assign w_sn_eff_needed = (((w_sn_src == SRC_WB) | (w_sn_src == SRC_MSHR)) | (w_sn_src == SRC_ARRAY)) & (w_sn_nxt != w_sn_ref);
	assign w_sn_eff_done = (((r_sn_src == SRC_WB) | (r_sn_src == SRC_MSHR)) | (r_sn_src == SRC_ARRAY)) & (r_sn_nxt != r_sn_ref);
	assign w_sn_eff_new = (r_sn_nxt == 3'b000 ? 2'b10 : 2'b01);
	assign mshr_sn_eff_o = (((r_sn_state == SN_EFFECT) & (r_sn_src == SRC_MSHR)) & (r_sn_nxt != r_sn_ref)) & (r_sn_pend[r_sn_idx] != 2'b10);
	assign mshr_sn_eff_idx_o = r_sn_idx;
	assign mshr_sn_eff_value_o = w_sn_eff_new;
	assign wb_sn_eff_o = (((r_sn_state == SN_EFFECT) & (r_sn_src == SRC_WB)) & (r_sn_nxt != r_sn_ref) ? w_sn_eff_new : 2'b00);
	assign w_sn_tagwr = ((r_sn_state == SN_EFFECT) & (r_sn_src == SRC_ARRAY)) & (r_sn_nxt != r_sn_ref);
	assign sn_cdvalid_o = r_sn_state == SN_DATA;
	function automatic signed [BEAT_W - 1:0] sv2v_cast_6E789_signed;
		input reg signed [BEAT_W - 1:0] inp;
		sv2v_cast_6E789_signed = inp;
	endfunction
	assign sn_cdlast_o = (r_sn_state == SN_DATA) & (r_sn_beat == sv2v_cast_6E789_signed(FILL_BEATS - 1));
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign sn_cddata_o = (r_sn_src == SRC_WB ? r_sn_wb_data[sv2v_cast_32(r_sn_beat) * 64+:64] : dat_b_rdata_i);
	assign w_sn_portb = (r_sn_state == SN_DATA) & (r_sn_src != SRC_WB);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				w_sn_way_onehot[w] = r_sn_way == sv2v_cast_19C97_signed(w);
		end
	end
	wire w_fq_head_done;
	wire w_fq_push;
	wire w_fq_pop;
	wire w_cmt_snap;
	wire w_cmt_cpl;
	wire w_cmt_datrd;
	wire w_cmt_datwr;
	wire w_cmt_tagwr;
	wire w_cmt_retire;
	wire w_slot_done;
	wire w_slot_we;
	wire [BEAT_W - 1:0] w_slot_beat;
	wire [STRB_W - 1:0] w_slot_be;
	wire [64 - 1:0] w_slot_wdata;
	wire [SEQ_W - 1:0] w_cmt_cpl_tag;
	wire [64 - 1:0] w_cmt_cpl_data;
	wire [2:0] w_install_state;
	reg [2 - 1:0] w_cmt_way_onehot;
	reg [2 - 1:0] w_upgr_way_onehot;
	wire [SET_W - 1:0] w_cmt_set;
	wire [TAG_W - 1:0] w_cmt_tag;
	wire [TAG_W - 1:0] w_upgr_tag;
	assign w_fq_head_done = (r_fq_cnt != {(FQ_W >= 0 ? FQ_W + 1 : 1 - FQ_W) {1'sb0}}) & r_fq_done[r_fq_head];
	assign w_cmt_snap = ((r_cmt_state == C_IDLE) & w_fq_head_done) & (r_fq_cls[r_fq_head] != 2'b10);
	assign w_slot_done = r_cmt_k == r_cmt_count;
	assign w_slot_we = r_req_we[(sv2v_cast_32(r_cmt_idx) * 2) + sv2v_cast_32(r_cmt_k[MW - 1:0])];
	assign w_slot_beat = r_req_beat[(sv2v_cast_32(r_cmt_idx) * 2) + sv2v_cast_32(r_cmt_k[MW - 1:0])];
	assign w_slot_be = r_req_be[(sv2v_cast_32(r_cmt_idx) * 2) + sv2v_cast_32(r_cmt_k[MW - 1:0])];
	assign w_slot_wdata = r_req_wdata[(sv2v_cast_32(r_cmt_idx) * 2) + sv2v_cast_32(r_cmt_k[MW - 1:0])];
	assign w_cmt_datwr = ((((r_cmt_state == C_MERGE) & ~w_slot_done) & w_slot_we) & ~fill_beat_valid_i) | ((r_cmt_state == C_CU_MERGE) & ~fill_beat_valid_i);
	assign w_cmt_datrd = ((r_cmt_state == C_MERGE) & ~w_slot_done) & ~w_slot_we;
	assign w_cmt_cpl = (r_cmt_state == C_DEPOSIT) | (r_cmt_state == C_CU_DEPOSIT);
	assign w_cmt_tagwr = ((r_cmt_state == C_INSTALL) | (r_cmt_state == C_PEND)) | (r_cmt_state == C_CU_INSTALL);
	assign w_cmt_retire = r_cmt_state == C_RETIRE;
	assign w_install_state = ((r_cmt_cls == 2'b00) && !r_cmt_pd ? 3'b001 : 3'b011);
	assign w_cmt_set = r_cmt_line[SET_W - 1:0];
	assign w_cmt_tag = r_cmt_line[LINE_W - 1-:TAG_W];
	assign w_upgr_tag = r_upgr_line[LINE_W - 1-:TAG_W];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				begin
					w_cmt_way_onehot[w] = r_cmt_way == sv2v_cast_19C97_signed(w);
					w_upgr_way_onehot[w] = r_upgr_way == sv2v_cast_19C97_signed(w);
				end
		end
	end
	assign w_cmt_cpl_tag = (r_cmt_state == C_CU_DEPOSIT ? r_upgr_seq : r_cmt_seqs[r_cmt_k[MW - 1:0]]);
	assign w_cmt_cpl_data = (r_cmt_state == C_CU_DEPOSIT ? r_upgr_wdata : (w_slot_we ? w_slot_wdata : r_cmt_rdata[r_cmt_k[MW - 1:0]]));
	reg w_acceptable;
	reg w_stall;
	reg [2:0] w_reason;
	reg w_yield;
	always @(*) begin
		if (_sv2v_0)
			;
		w_acceptable = 1'b0;
		w_stall = 1'b0;
		w_reason = STALL_NONE;
		w_yield = 1'b0;
		if ((lkup_valid_i && !r_init_busy) && !w_sn_block_cpu) begin
			if (w_upgr_line_stall) begin
				w_stall = 1'b1;
				w_reason = STALL_XCLASS;
			end
			else if (w_hit_rd) begin
				if (!(w_cmt_cpl | w_cmt_datrd))
					w_acceptable = 1'b1;
			end
			else if (w_hit_wr) begin
				if (w_cmt_cpl)
					;
				else if (fill_beat_valid_i | w_cmt_datwr)
					w_yield = 1'b1;
				else if ((w_hit_state == 3'b010) & w_cmt_tagwr)
					;
				else
					w_acceptable = 1'b1;
			end
			else if (w_hit_upgr) begin
				if (!r_upgr_valid && !r_fill_pend)
					w_acceptable = 1'b1;
			end
			else if (mshr_lkup_reg_match_i) begin
				if (w_xclass) begin
					w_stall = 1'b1;
					w_reason = STALL_XCLASS;
				end
				else if (r_efill_done[mshr_lkup_reg_match_idx_i]) begin
					w_stall = 1'b1;
					w_reason = STALL_COMMIT;
				end
				else if (w_cmt_snap)
					;
				else if (!w_merge_room) begin
					w_stall = 1'b1;
					w_reason = STALL_MSHR_FULL;
				end
				else
					w_acceptable = 1'b1;
			end
			else if (w_wb_race) begin
				w_stall = 1'b1;
				w_reason = STALL_WB;
			end
			else if (mshr_full_i) begin
				w_stall = 1'b1;
				w_reason = STALL_MSHR_FULL;
			end
			else if ((mshr_set_full_i | w_upgr_victim_block) | w_victim_claimed) begin
				w_stall = 1'b1;
				w_reason = STALL_SET_OVERSUB;
			end
			else if (w_wb_block) begin
				w_stall = 1'b1;
				w_reason = STALL_WB;
			end
			else if (!r_fill_pend)
				w_acceptable = 1'b1;
		end
	end
	wire w_accept;
	wire w_accept_rd;
	wire w_accept_wr;
	wire w_accept_upgr;
	wire w_accept_merge;
	wire w_accept_alloc;
	assign tag_req_o = ((lkup_valid_i & ~r_init_busy) & w_acceptable) & ~r_ctrl_err;
	assign w_accept = tag_req_o & tag_gnt_i;
	assign lkup_ready_o = w_accept;
	assign lkup_stall_o = ((lkup_valid_i & ~r_init_busy) & ~w_accept) & (w_stall | (w_acceptable & ~tag_gnt_i));
	assign lkup_stall_reason_o = (w_stall ? w_reason : (((lkup_valid_i & ~r_init_busy) & w_acceptable) & ~tag_gnt_i ? STALL_TAG_FULL : STALL_NONE));
	assign lkup_wr_yield_o = w_yield;
	assign w_accept_rd = w_accept & w_hit_rd;
	assign w_accept_wr = w_accept & w_hit_wr;
	assign w_accept_upgr = w_accept & w_hit_upgr;
	assign w_accept_merge = (w_accept & ~w_serve_hit) & mshr_lkup_reg_match_i;
	assign w_accept_alloc = (w_accept & ~w_serve_hit) & ~mshr_lkup_reg_match_i;
	assign lkup_hit_o = w_accept_rd | w_accept_wr;
	assign lkup_merge_o = w_accept_merge;
	assign lkup_miss_alloc_o = w_accept_alloc;
	assign lkup_upgrade_o = w_accept_upgr;
	assign cap_busy_o = r_cap_busy;
	assign init_busy_o = r_init_busy;
	assign ctrl_error_o = r_ctrl_err;
	wire w_launch;
	wire [32 - 1:0] w_launch_addr;
	wire [1:0] w_launch_cls;
	assign w_launch = w_accept_alloc | w_accept_upgr;
	assign w_launch_addr = {w_req_line, {OFF_W {1'b0}}};
	assign w_launch_cls = (w_accept_upgr ? 2'b10 : (lkup_we_i ? 2'b01 : 2'b00));
	assign fill_start_o = r_fill_pend | w_launch;
	assign fill_addr_o = (r_fill_pend ? r_fill_addr : w_launch_addr);
	assign fill_cls_o = (r_fill_pend ? r_fill_cls : w_launch_cls);
	assign w_fq_push = fill_start_o & fill_accept_i;
	assign w_fq_pop = w_cmt_retire | (r_cmt_state == C_CU_DEPOSIT);
	assign cpl_valid_o = (w_cmt_cpl | w_accept_rd) | w_accept_wr;
	assign cpl_tag_o = (w_cmt_cpl ? w_cmt_cpl_tag : tag_i);
	assign cpl_data_o = (w_cmt_cpl ? w_cmt_cpl_data : (w_accept_rd ? dat_a_rdata_i : lkup_wdata_i));
	assign tag_a_set_o = (r_init_busy ? r_init_cnt : w_req_set);
	assign tag_a_wr_en_o = (((r_init_busy & ~(!rst_n)) | w_cmt_tagwr) | w_sn_tagwr) | (w_accept_wr & (w_hit_state == 3'b010));
	assign tag_a_wr_way_onehot_o = (r_init_busy ? {2 {1'b1}} : (w_cmt_tagwr ? (r_cmt_state == C_CU_INSTALL ? w_upgr_way_onehot : w_cmt_way_onehot) : (w_sn_tagwr ? w_sn_way_onehot : w_hit_way_onehot)));
	assign tag_a_wr_set_o = (r_init_busy ? r_init_cnt : (w_cmt_tagwr ? (r_cmt_state == C_CU_INSTALL ? r_upgr_set : w_cmt_set) : (w_sn_tagwr ? r_sn_set : w_req_set)));
	assign tag_a_wr_tag_state_o = (r_init_busy ? {{TAG_W {1'b0}}, 3'b000} : (r_cmt_state == C_INSTALL ? {w_cmt_tag, w_install_state} : (r_cmt_state == C_PEND ? {w_cmt_tag, (r_cmt_pend == 2'b10 ? 3'b000 : 3'b001)} : (r_cmt_state == C_CU_INSTALL ? {w_upgr_tag, (r_upgr_killed ? 3'b000 : 3'b011)} : (w_sn_tagwr ? {r_sn_tag, r_sn_nxt} : {w_req_tag, 3'b011})))));
	assign dat_a_addr_o = (w_cmt_datrd ? {w_cmt_set, w_slot_beat} : {w_req_set, w_req_beat});
	assign dat_a_way_o = (w_cmt_datrd ? r_cmt_way : w_hit_way);
	assign dat_a_wr_en_o = w_accept_wr | w_cmt_datwr;
	assign dat_a_wr_way_onehot_o = (w_cmt_datwr ? (r_cmt_state == C_CU_MERGE ? w_upgr_way_onehot : w_cmt_way_onehot) : w_hit_way_onehot);
	assign dat_a_wr_addr_o = (w_cmt_datwr ? (r_cmt_state == C_CU_MERGE ? {r_upgr_set, r_upgr_beat} : {w_cmt_set, w_slot_beat}) : {w_req_set, w_req_beat});
	assign dat_a_wr_wdata_o = (w_cmt_datwr ? (r_cmt_state == C_CU_MERGE ? r_upgr_wdata : w_slot_wdata) : lkup_wdata_i);
	assign dat_a_wr_be_o = (w_cmt_datwr ? (r_cmt_state == C_CU_MERGE ? r_upgr_be : w_slot_be) : lkup_be_i);
	assign dat_b_addr_o = (w_sn_portb ? {r_sn_set, r_sn_beat} : {r_cap_set, r_cap_beat});
	assign dat_b_way_o = (w_sn_portb ? r_sn_way : r_cap_way);
	assign repl_req_o = w_accept_alloc;
	assign repl_set_o = w_req_set;
	assign repl_hit_o = (w_accept_rd | w_accept_wr) | w_accept_upgr;
	assign repl_update_o = w_accept_alloc;
	assign repl_hit_way_o = (w_accept_alloc ? repl_victim_way_i : w_hit_way);
	assign mshr_alloc_o = w_accept_alloc;
	assign mshr_alloc_line_o = w_req_line;
	assign mshr_alloc_set_o = w_req_set;
	assign mshr_alloc_cls_o = (lkup_we_i ? 2'b01 : 2'b00);
	assign mshr_alloc_install_o = lkup_we_i;
	assign mshr_alloc_victim_way_o = repl_victim_way_i;
	assign mshr_alloc_wb_slot_o = wb_cap_slot_i;
	assign mshr_alloc_wb_valid_o = w_victim_dirty;
	assign mshr_alloc_seq_o = tag_i;
	assign mshr_lkup_line_o = w_req_line;
	assign mshr_cpl_idx_o = (w_cmt_snap ? r_fq_idx[r_fq_head] : mshr_lkup_reg_match_idx_i);
	assign mshr_merge_o = w_accept_merge;
	assign mshr_merge_idx_o = mshr_lkup_reg_match_idx_i;
	assign mshr_merge_seq_o = tag_i;
	assign mshr_beat_o = fill_beat_valid_i;
	assign mshr_beat_idx_o = fill_beat_idx_i;
	assign mshr_beat_num_o = fill_beat_num_i;
	assign mshr_retire_o = w_cmt_retire;
	assign mshr_retire_idx_o = r_cmt_idx;
	assign cmt_busy_o = (r_cmt_state != C_IDLE) | w_fq_head_done;
	assign wb_cap_o = (w_accept_alloc & w_victim_dirty) | r_cap_busy;
	assign wb_cap_line_o = (r_cap_busy ? r_cap_line : {w_victim_tag, w_req_set});
	assign wb_cap_beat_o = r_cap_busy & ~w_sn_portb;
	assign wb_cap_beat_data_o = dat_b_rdata_i;
	assign drain_start_o = wb_drain_valid_i & ~r_drain_busy;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_DT = 0;
	function automatic signed [SET_W - 1:0] sv2v_cast_DCA8A_signed;
		input reg signed [SET_W - 1:0] inp;
		sv2v_cast_DCA8A_signed = inp;
	endfunction
	function automatic signed [FQ_W - 1:0] sv2v_cast_6D0AE_signed;
		input reg signed [FQ_W - 1:0] inp;
		sv2v_cast_6D0AE_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_init_busy <= 1'b1;
			r_init_cnt <= 1'sb0;
			r_cap_busy <= 1'b0;
			r_cap_set <= 1'sb0;
			r_cap_way <= 1'sb0;
			r_cap_line <= 1'sb0;
			r_cap_beat <= 1'sb0;
			r_fill_pend <= 1'b0;
			r_fill_addr <= 1'sb0;
			r_fill_cls <= 1'sb0;
			r_fill_idx <= 1'sb0;
			r_ar_done <= 1'b0;
			r_drain_busy <= 1'b0;
			r_upgr_valid <= 1'b0;
			r_upgr_line <= 1'sb0;
			r_upgr_set <= 1'sb0;
			r_upgr_way <= 1'sb0;
			r_upgr_seq <= 1'sb0;
			r_upgr_beat <= 1'sb0;
			r_upgr_be <= 1'sb0;
			r_upgr_wdata <= 1'sb0;
			r_upgr_killed <= 1'b0;
			r_ctrl_err <= 1'b0;
			r_claim_vld <= 1'sb0;
			r_efill_done <= 1'sb0;
			r_fq_head <= 1'sb0;
			r_fq_tail <= 1'sb0;
			r_fq_done_ptr <= 1'sb0;
			r_fq_cnt <= 1'sb0;
			r_fq_undone <= 1'sb0;
			r_cmt_state <= C_IDLE;
			r_cmt_idx <= 1'sb0;
			r_cmt_line <= 1'sb0;
			r_cmt_cls <= 1'sb0;
			r_cmt_pd <= 1'b0;
			r_cmt_pend <= 2'b00;
			r_cmt_way <= 1'sb0;
			r_cmt_count <= 1'sb0;
			r_cmt_k <= 1'sb0;
			r_sn_state <= SN_IDLE;
			r_sn_line <= 1'sb0;
			r_sn_set <= 1'sb0;
			r_sn_tag <= 1'sb0;
			r_sn_src <= SRC_NONE;
			r_sn_allb <= 1'b0;
			r_sn_way <= 1'sb0;
			r_sn_idx <= 1'sb0;
			r_sn_ref <= 1'sb0;
			r_sn_nxt <= 1'sb0;
			r_sn_beat <= 1'sb0;
			r_sn_wb_data <= 1'sb0;
			begin : sv2v_autoblock_9
				reg signed [31:0] e;
				for (e = 0; e < 2; e = e + 1)
					begin
						r_claim_set[e] <= 1'sb0;
						r_claim_way[e] <= 1'sb0;
						r_cmt_seqs[e] <= 1'sb0;
						r_cmt_rdata[e] <= 1'sb0;
						r_sn_pend[e] <= 2'b00;
					end
			end
			begin : sv2v_autoblock_10
				reg signed [31:0] q;
				for (q = 0; q < FQ_DEPTH; q = q + 1)
					begin
						r_fq_idx[q] <= 1'sb0;
						r_fq_cls[q] <= 1'sb0;
						r_fq_pd[q] <= 1'b0;
						r_fq_done[q] <= 1'b0;
					end
			end
			begin : sv2v_autoblock_11
				reg signed [31:0] k;
				for (k = 0; k < (2 * 2); k = k + 1)
					begin
						r_req_we[k] <= 1'b0;
						r_req_beat[k] <= 1'sb0;
						r_req_be[k] <= 1'sb0;
						r_req_wdata[k] <= 1'sb0;
					end
			end
		end
		else begin
			if (r_init_busy) begin
				if (r_init_cnt == sv2v_cast_DCA8A_signed(16 - 1))
					r_init_busy <= 1'b0;
				else
					r_init_cnt <= r_init_cnt + 1'b1;
			end
			if (w_accept_alloc & w_victim_dirty) begin
				r_cap_busy <= 1'b1;
				r_cap_set <= w_req_set;
				r_cap_way <= repl_victim_way_i;
				r_cap_line <= {w_victim_tag, w_req_set};
				r_cap_beat <= 1'sb0;
			end
			else if (r_cap_busy & ~w_sn_portb) begin
				if (r_cap_beat == sv2v_cast_6E789_signed(FILL_BEATS - 1)) begin
					r_cap_busy <= 1'b0;
					r_cap_beat <= 1'sb0;
				end
				else
					r_cap_beat <= r_cap_beat + 1'b1;
			end
			if (w_launch & ~fill_accept_i) begin
				r_fill_pend <= 1'b1;
				r_fill_addr <= w_launch_addr;
				r_fill_cls <= w_launch_cls;
				r_fill_idx <= (w_accept_upgr ? {MW {1'sb0}} : mshr_alloc_idx_i);
			end
			else if (fill_accept_i)
				r_fill_pend <= 1'b0;
			if (fill_done_i)
				r_ar_done <= 1'b0;
			else if (fill_ar_done_i)
				r_ar_done <= 1'b1;
			if (drain_start_o)
				r_drain_busy <= 1'b1;
			else if (drain_done_i)
				r_drain_busy <= 1'b0;
			if (w_accept_upgr) begin
				r_upgr_valid <= 1'b1;
				r_upgr_line <= w_req_line;
				r_upgr_set <= w_req_set;
				r_upgr_way <= w_hit_way;
				r_upgr_seq <= tag_i;
				r_upgr_beat <= w_req_beat;
				r_upgr_be <= lkup_be_i;
				r_upgr_wdata <= lkup_wdata_i;
				r_upgr_killed <= 1'b0;
			end
			else if (r_cmt_state == C_CU_DEPOSIT) begin
				r_upgr_valid <= 1'b0;
				r_upgr_killed <= 1'b0;
			end
			if (((((r_sn_state == SN_EFFECT) && (r_sn_src == SRC_ARRAY)) && r_upgr_valid) && (r_sn_line == r_upgr_line)) && (r_sn_nxt == 3'b000))
				r_upgr_killed <= 1'b1;
			if ((r_cmt_state > C_CU_DEPOSIT) || (r_sn_state == 2'd3))
				r_ctrl_err <= 1'b1;
			if (w_accept_alloc) begin
				r_claim_vld[mshr_alloc_idx_i] <= 1'b1;
				r_claim_set[mshr_alloc_idx_i] <= w_req_set;
				r_claim_way[mshr_alloc_idx_i] <= repl_victim_way_i;
			end
			if (w_cmt_retire) begin
				r_claim_vld[r_cmt_idx] <= 1'b0;
				r_efill_done[r_cmt_idx] <= 1'b0;
			end
			if (w_accept_alloc) begin
				r_req_we[sv2v_cast_32(mshr_alloc_idx_i) * 2] <= lkup_we_i;
				r_req_beat[sv2v_cast_32(mshr_alloc_idx_i) * 2] <= w_req_beat;
				r_req_be[sv2v_cast_32(mshr_alloc_idx_i) * 2] <= lkup_be_i;
				r_req_wdata[sv2v_cast_32(mshr_alloc_idx_i) * 2] <= lkup_wdata_i;
			end
			if (w_accept_merge) begin
				r_req_we[(sv2v_cast_32(mshr_lkup_reg_match_idx_i) * 2) + sv2v_cast_32(mshr_cpl_merge_count_i[MW - 1:0])] <= lkup_we_i;
				r_req_beat[(sv2v_cast_32(mshr_lkup_reg_match_idx_i) * 2) + sv2v_cast_32(mshr_cpl_merge_count_i[MW - 1:0])] <= w_req_beat;
				r_req_be[(sv2v_cast_32(mshr_lkup_reg_match_idx_i) * 2) + sv2v_cast_32(mshr_cpl_merge_count_i[MW - 1:0])] <= lkup_be_i;
				r_req_wdata[(sv2v_cast_32(mshr_lkup_reg_match_idx_i) * 2) + sv2v_cast_32(mshr_cpl_merge_count_i[MW - 1:0])] <= lkup_wdata_i;
			end
			if (w_fq_push) begin
				r_fq_idx[r_fq_tail] <= (r_fill_pend ? r_fill_idx : mshr_alloc_idx_i);
				r_fq_cls[r_fq_tail] <= (r_fill_pend ? r_fill_cls : w_launch_cls);
				r_fq_done[r_fq_tail] <= 1'b0;
				if (r_fq_tail == sv2v_cast_6D0AE_signed(FQ_DEPTH - 1))
					r_fq_tail <= 1'sb0;
				else
					r_fq_tail <= r_fq_tail + 1'b1;
			end
			if (fill_done_i) begin
				r_fq_done[r_fq_done_ptr] <= 1'b1;
				r_fq_pd[r_fq_done_ptr] <= fill_pass_dirty_i;
				if (r_fq_cls[r_fq_done_ptr] != 2'b10)
					r_efill_done[r_fq_idx[r_fq_done_ptr]] <= 1'b1;
				if (r_fq_done_ptr == sv2v_cast_6D0AE_signed(FQ_DEPTH - 1))
					r_fq_done_ptr <= 1'sb0;
				else
					r_fq_done_ptr <= r_fq_done_ptr + 1'b1;
			end
			if (w_fq_pop) begin
				if (r_fq_head == sv2v_cast_6D0AE_signed(FQ_DEPTH - 1))
					r_fq_head <= 1'sb0;
				else
					r_fq_head <= r_fq_head + 1'b1;
			end
			case ({w_fq_push, w_fq_pop})
				2'b10: r_fq_cnt <= r_fq_cnt + 1'b1;
				2'b01: r_fq_cnt <= r_fq_cnt - 1'b1;
				default:
					;
			endcase
			case ({w_fq_push, fill_done_i})
				2'b10: r_fq_undone <= r_fq_undone + 1'b1;
				2'b01: r_fq_undone <= r_fq_undone - 1'b1;
				default:
					;
			endcase
			if (w_sn_gnt) begin
				r_sn_line <= w_sn_line;
				r_sn_set <= w_sn_set;
				r_sn_tag <= w_sn_tag;
				r_sn_src <= w_sn_src;
				r_sn_allb <= &mshr_sn_beats_rcvd_i;
				r_sn_way <= (w_src_mshr ? r_claim_way[mshr_sn_match_idx_i] : w_sn_tway);
				r_sn_idx <= mshr_sn_match_idx_i;
				r_sn_ref <= w_sn_ref;
				r_sn_nxt <= w_sn_nxt;
				r_sn_beat <= 1'sb0;
				if (w_src_wb)
					r_sn_wb_data <= wb_sn_data_i;
				if (w_sn_crresp[l1_pkg_AMBER_CRRESP_DT])
					r_sn_state <= SN_DATA;
				else if (w_sn_eff_needed)
					r_sn_state <= SN_EFFECT;
			end
			else if (r_sn_state == SN_DATA) begin
				if (sn_cdready_i) begin
					if (r_sn_beat == sv2v_cast_6E789_signed(FILL_BEATS - 1))
						r_sn_state <= (w_sn_eff_done ? SN_EFFECT : SN_IDLE);
					else
						r_sn_beat <= r_sn_beat + 1'b1;
				end
			end
			else if (r_sn_state == SN_EFFECT) begin
				r_sn_state <= SN_IDLE;
				if (((r_sn_src == SRC_MSHR) && (r_sn_nxt != r_sn_ref)) && (r_sn_pend[r_sn_idx] != 2'b10))
					r_sn_pend[r_sn_idx] <= w_sn_eff_new;
			end
			if (w_accept_alloc)
				r_sn_pend[mshr_alloc_idx_i] <= 2'b00;
			case (r_cmt_state)
				C_IDLE:
					if (w_fq_head_done && (r_sn_state == SN_IDLE)) begin
						if (r_fq_cls[r_fq_head] == 2'b10)
							r_cmt_state <= C_CU_MERGE;
						else begin
							r_cmt_state <= C_MERGE;
							r_cmt_idx <= r_fq_idx[r_fq_head];
							r_cmt_cls <= r_fq_cls[r_fq_head];
							r_cmt_pd <= r_fq_pd[r_fq_head];
							r_cmt_line <= mshr_cpl_line_i;
							r_cmt_pend <= mshr_cpl_pend_eff_i;
							r_cmt_count <= mshr_cpl_merge_count_i;
							r_cmt_way <= r_claim_way[r_fq_idx[r_fq_head]];
							begin : sv2v_autoblock_12
								reg signed [31:0] k;
								for (k = 0; k < 2; k = k + 1)
									r_cmt_seqs[k] <= mshr_cpl_merge_seqs_i[k * SEQ_W+:SEQ_W];
							end
							r_cmt_k <= 1'sb0;
						end
					end
				C_MERGE:
					if (w_slot_done)
						r_cmt_state <= C_INSTALL;
					else if (w_slot_we) begin
						if (!fill_beat_valid_i)
							r_cmt_k <= r_cmt_k + 1'b1;
					end
					else begin
						r_cmt_rdata[r_cmt_k[MW - 1:0]] <= dat_a_rdata_i;
						r_cmt_k <= r_cmt_k + 1'b1;
					end
				C_INSTALL: begin
					r_cmt_k <= 1'sb0;
					if (r_cmt_pend != 2'b00)
						r_cmt_state <= C_PEND;
					else
						r_cmt_state <= C_DEPOSIT;
				end
				C_PEND: r_cmt_state <= C_DEPOSIT;
				C_DEPOSIT:
					if (r_cmt_k == (r_cmt_count - 1'b1))
						r_cmt_state <= C_RETIRE;
					else
						r_cmt_k <= r_cmt_k + 1'b1;
				C_RETIRE: r_cmt_state <= C_IDLE;
				C_CU_MERGE:
					if (!fill_beat_valid_i)
						r_cmt_state <= C_CU_INSTALL;
				C_CU_INSTALL: r_cmt_state <= C_CU_DEPOSIT;
				C_CU_DEPOSIT: r_cmt_state <= C_IDLE;
				default: r_cmt_state <= C_IDLE;
			endcase
		end
	initial _sv2v_0 = 0;
endmodule
