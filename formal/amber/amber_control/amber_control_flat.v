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
			$display("Error [%0t] /tmp/formal_amber_control/amber_pending_fill_bypass.sv:125:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: SETS must be a power of two");
		if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_pending_fill_bypass.sv:127:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: LINE_BYTES must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_pending_fill_bypass.sv:129:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
		if ((BUS_WIDTH % 8) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_pending_fill_bypass.sv:131:13 - amber_pending_fill_bypass.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_pending_fill_bypass: BUS_WIDTH must be a multiple of 8");
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
module amber_victim (
	clk,
	rst_n,
	victim_load,
	victim_addr_in,
	victim_data_in,
	victim_clear,
	victim_busy,
	victim_empty,
	victim_valid,
	victim_addr,
	victim_data
);
	localparam signed [31:0] amber_pkg_AMBER_ADDR_WIDTH = 32;
	parameter signed [31:0] ADDR_WIDTH = amber_pkg_AMBER_ADDR_WIDTH;
	localparam signed [31:0] amber_pkg_AMBER_SETS = 128;
	parameter signed [31:0] SETS = amber_pkg_AMBER_SETS;
	localparam signed [31:0] amber_pkg_AMBER_LINE_BYTES = 64;
	parameter signed [31:0] LINE_BYTES = amber_pkg_AMBER_LINE_BYTES;
	localparam signed [31:0] amber_pkg_AMBER_BUS_WIDTH = 64;
	parameter signed [31:0] BUS_WIDTH = amber_pkg_AMBER_BUS_WIDTH;
	localparam signed [31:0] LINE_OFFSET_WIDTH = $clog2(LINE_BYTES);
	localparam signed [31:0] STRB_W = BUS_WIDTH / 8;
	localparam signed [31:0] FILL_BEATS = LINE_BYTES / STRB_W;
	localparam signed [31:0] LINE_WIDTH = LINE_BYTES * 8;
	input wire clk;
	input wire rst_n;
	input wire victim_load;
	input wire [ADDR_WIDTH - 1:0] victim_addr_in;
	input wire [LINE_WIDTH - 1:0] victim_data_in;
	input wire victim_clear;
	output wire victim_busy;
	output wire victim_empty;
	output wire victim_valid;
	output wire [ADDR_WIDTH - 1:0] victim_addr;
	output wire [LINE_WIDTH - 1:0] victim_data;
	initial begin
		if ((SETS & (SETS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_victim.sv:124:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: SETS must be a power of two");
		if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_victim.sv:126:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: LINE_BYTES must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_victim.sv:128:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
		if ((BUS_WIDTH % 8) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_victim.sv:130:13 - amber_victim.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_victim: BUS_WIDTH must be a multiple of 8");
	end
	reg victim_valid_q;
	reg [ADDR_WIDTH - 1:0] victim_addr_q;
	reg [LINE_WIDTH - 1:0] victim_data_q;
	assign victim_valid = victim_valid_q;
	assign victim_busy = victim_valid_q;
	assign victim_empty = !victim_valid_q;
	assign victim_addr = victim_addr_q;
	assign victim_data = victim_data_q;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			victim_valid_q <= 1'b0;
			victim_addr_q <= 1'sb0;
			victim_data_q <= 1'sb0;
		end
		else if (victim_clear)
			victim_valid_q <= 1'b0;
		else if (victim_load && !victim_valid_q) begin
			victim_valid_q <= 1'b1;
			victim_addr_q <= victim_addr_in;
			victim_data_q <= victim_data_in;
		end
endmodule
module amber_control (
	clk,
	rst_n,
	req_valid,
	req_addr,
	req_we,
	req_be,
	req_wdata,
	ctrl_req_ready,
	ctrl_rsp_valid,
	ctrl_rsp_data,
	ctrl_tag_a_set,
	ctrl_tag_a_tag_state,
	ctrl_tag_a_wr_en,
	ctrl_tag_a_wr_way_onehot,
	ctrl_tag_a_wr_set,
	ctrl_tag_a_wr_tag_state,
	ctrl_data_a_addr,
	ctrl_data_a_way,
	ctrl_data_a_rdata,
	ctrl_data_a_wr_en,
	ctrl_data_a_wr_way_onehot,
	ctrl_data_a_wr_addr,
	ctrl_data_a_wr_wdata,
	ctrl_data_a_wr_be,
	ctrl_tag_b_req,
	ctrl_tag_b_set,
	ctrl_tag_b_tag_state,
	ctrl_data_b_addr,
	ctrl_data_b_way,
	ctrl_data_b_rdata,
	ctrl_repl_req,
	ctrl_repl_set,
	ctrl_repl_way,
	ctrl_repl_hit,
	ctrl_repl_update,
	ctrl_repl_hit_way,
	ctrl_victim_load,
	ctrl_victim_addr_in,
	ctrl_victim_data_in,
	ctrl_fill_start,
	ctrl_fill_addr,
	ctrl_req_class,
	ctrl_fill_done,
	ctrl_fill_beat_valid,
	ctrl_fill_beat_idx,
	ctrl_drain_start,
	ctrl_drain_done,
	ctrl_snoop_req,
	ctrl_snoop_ready,
	ctrl_snoop_type,
	ctrl_snoop_addr,
	ctrl_crresp,
	ctrl_cddata,
	ctrl_cdlast,
	ctrl_cdvalid,
	ctrl_cdready,
	ctrl_init_busy,
	ctrl_init_set,
	ctrl_state
);
	reg _sv2v_0;
	localparam signed [31:0] amber_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] amber_pkg_AMBER_SETS = 128;
	localparam signed [31:0] amber_pkg_AMBER_WAYS = 4;
	localparam signed [31:0] amber_pkg_AMBER_LINE_BYTES = 64;
	localparam signed [31:0] amber_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] SET_INDEX_WIDTH = $clog2(16);
	localparam signed [31:0] LINE_OFFSET_WIDTH = $clog2(64);
	localparam signed [31:0] TAG_WIDTH = (32 - SET_INDEX_WIDTH) - LINE_OFFSET_WIDTH;
	localparam signed [31:0] TAG_STATE_WIDTH = TAG_WIDTH + 3;
	localparam signed [31:0] STRB_W = 64 / 8;
	localparam signed [31:0] FILL_BEATS = 64 / STRB_W;
	localparam signed [31:0] BEAT_INDEX_WIDTH = $clog2(FILL_BEATS);
	localparam signed [31:0] WAY_INDEX_WIDTH = $clog2(2);
	localparam signed [31:0] MEM_ADDR_WIDTH = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH;
	localparam signed [31:0] LINE_ADDR_WIDTH = TAG_WIDTH + SET_INDEX_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire req_valid;
	input wire [32 - 1:0] req_addr;
	input wire req_we;
	input wire [STRB_W - 1:0] req_be;
	input wire [64 - 1:0] req_wdata;
	output wire ctrl_req_ready;
	output wire ctrl_rsp_valid;
	output wire [64 - 1:0] ctrl_rsp_data;
	output reg [SET_INDEX_WIDTH - 1:0] ctrl_tag_a_set;
	input wire [(2 * TAG_STATE_WIDTH) - 1:0] ctrl_tag_a_tag_state;
	output reg ctrl_tag_a_wr_en;
	output reg [2 - 1:0] ctrl_tag_a_wr_way_onehot;
	output reg [SET_INDEX_WIDTH - 1:0] ctrl_tag_a_wr_set;
	output reg [TAG_STATE_WIDTH - 1:0] ctrl_tag_a_wr_tag_state;
	output reg [MEM_ADDR_WIDTH - 1:0] ctrl_data_a_addr;
	output reg [WAY_INDEX_WIDTH - 1:0] ctrl_data_a_way;
	input wire [64 - 1:0] ctrl_data_a_rdata;
	output reg ctrl_data_a_wr_en;
	output reg [2 - 1:0] ctrl_data_a_wr_way_onehot;
	output reg [MEM_ADDR_WIDTH - 1:0] ctrl_data_a_wr_addr;
	output reg [64 - 1:0] ctrl_data_a_wr_wdata;
	output reg [STRB_W - 1:0] ctrl_data_a_wr_be;
	output wire ctrl_tag_b_req;
	output wire [SET_INDEX_WIDTH - 1:0] ctrl_tag_b_set;
	input wire [(2 * TAG_STATE_WIDTH) - 1:0] ctrl_tag_b_tag_state;
	output reg [MEM_ADDR_WIDTH - 1:0] ctrl_data_b_addr;
	output reg [WAY_INDEX_WIDTH - 1:0] ctrl_data_b_way;
	input wire [64 - 1:0] ctrl_data_b_rdata;
	output reg ctrl_repl_req;
	output reg [SET_INDEX_WIDTH - 1:0] ctrl_repl_set;
	input wire [WAY_INDEX_WIDTH - 1:0] ctrl_repl_way;
	output reg ctrl_repl_hit;
	output reg ctrl_repl_update;
	output reg [WAY_INDEX_WIDTH - 1:0] ctrl_repl_hit_way;
	output reg ctrl_victim_load;
	output reg [32 - 1:0] ctrl_victim_addr_in;
	output reg [(64 * 8) - 1:0] ctrl_victim_data_in;
	output reg ctrl_fill_start;
	output reg [32 - 1:0] ctrl_fill_addr;
	output wire [2:0] ctrl_req_class;
	input wire ctrl_fill_done;
	input wire ctrl_fill_beat_valid;
	input wire [BEAT_INDEX_WIDTH - 1:0] ctrl_fill_beat_idx;
	output reg ctrl_drain_start;
	input wire ctrl_drain_done;
	input wire ctrl_snoop_req;
	output wire ctrl_snoop_ready;
	input wire [2:0] ctrl_snoop_type;
	input wire [32 - 1:0] ctrl_snoop_addr;
	localparam signed [31:0] amber_pkg_AMBER_CRRESP_WIDTH = 5;
	output reg [4:0] ctrl_crresp;
	output reg [64 - 1:0] ctrl_cddata;
	output reg ctrl_cdlast;
	output reg ctrl_cdvalid;
	input wire ctrl_cdready;
	output wire ctrl_init_busy;
	output wire [SET_INDEX_WIDTH - 1:0] ctrl_init_set;
	output reg [3:0] ctrl_state;
	initial begin
		if ((16 & (16 - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_control.sv:242:13 - amber_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_control: 16 must be a power of two");
		if ((64 & (64 - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_control.sv:244:13 - amber_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_control: 64 must be a power of two");
		if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_control.sv:246:13 - amber_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_control: 64 / 64*8 must be a power of two");
		if ((64 % 8) != 0)
			$display("Error [%0t] /tmp/formal_amber_control/amber_control.sv:248:13 - amber_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_control: 64 must be a multiple of 8");
		if (2 < 2)
			$display("Error [%0t] /tmp/formal_amber_control/amber_control.sv:250:13 - amber_control.<unnamed_block>.<unnamed_block>\n msg: ", $time, "amber_control: 2 must be >= 2");
	end
	localparam signed [31:0] CTRL_BITS = 12;
	localparam [11:0] OH_IDLE = 12'b000000000001;
	localparam [11:0] OH_INIT = 12'b000000000010;
	localparam [11:0] OH_LOOKUP = 12'b000000000100;
	localparam [11:0] OH_HIT_RD = 12'b000000001000;
	localparam [11:0] OH_HIT_WR = 12'b000000010000;
	localparam [11:0] OH_MISS_VICTIM = 12'b000000100000;
	localparam [11:0] OH_MISS_DRAIN = 12'b000001000000;
	localparam [11:0] OH_MISS_FILL = 12'b000010000000;
	localparam [11:0] OH_FILL_WRITE = 12'b000100000000;
	localparam [11:0] OH_REPLAY = 12'b001000000000;
	localparam [11:0] OH_SNOOP = 12'b010000000000;
	localparam [11:0] OH_ERROR = 12'b100000000000;
	reg [11:0] state_q;
	reg [11:0] state_d;
	reg [32 - 1:0] req_addr_q;
	reg req_we_q;
	reg [STRB_W - 1:0] req_be_q;
	reg [64 - 1:0] req_wdata_q;
	reg [WAY_INDEX_WIDTH - 1:0] hit_way_q;
	reg [2:0] hit_state_q;
	reg [2:0] req_class_q;
	reg upgr_q;
	reg [WAY_INDEX_WIDTH - 1:0] victim_way_q;
	reg [TAG_WIDTH - 1:0] victim_tag_q;
	reg [2:0] victim_state_q;
	reg [(64 * 8) - 1:0] victim_line_q;
	reg [BEAT_INDEX_WIDTH:0] mv_cnt_q;
	reg fill_seen_q;
	reg fill_done_q;
	reg drain_seen_q;
	reg drain_done_q;
	reg rsp_valid_q;
	reg [64 - 1:0] rsp_data_q;
	reg [SET_INDEX_WIDTH - 1:0] init_cnt_q;
	reg [32 - 1:0] sn_addr_q;
	reg [2:0] sn_type_q;
	reg [BEAT_INDEX_WIDTH - 1:0] sn_beat_q;
	reg [11:0] sn_return_q;
	reg sn_back_to_lookup_q;
	reg sn_pf_q;
	reg sn_hit_any_q;
	reg [WAY_INDEX_WIDTH - 1:0] sn_hit_way_q;
	reg [2:0] sn_hit_state_q;
	reg [TAG_WIDTH - 1:0] sn_hit_tag_q;
	reg sn_stale_q;
	reg sn_victim_q;
	reg sn_upgr_line_q;
	reg sn_dt_q;
	reg [2:0] sn_ref_q;
	reg pend_vld_q;
	reg [2:0] pend_state_q;
	wire [TAG_WIDTH - 1:0] req_tag;
	wire [SET_INDEX_WIDTH - 1:0] req_set;
	wire [BEAT_INDEX_WIDTH - 1:0] req_beat;
	wire [LINE_ADDR_WIDTH - 1:0] req_line_addr;
	wire [32 - 1:0] req_line_base;
	assign req_tag = req_addr_q[32 - 1-:TAG_WIDTH];
	assign req_set = req_addr_q[LINE_OFFSET_WIDTH+:SET_INDEX_WIDTH];
	assign req_beat = req_addr_q[LINE_OFFSET_WIDTH - 1-:BEAT_INDEX_WIDTH];
	assign req_line_addr = req_addr_q[32 - 1:LINE_OFFSET_WIDTH];
	assign req_line_base = {req_line_addr, {LINE_OFFSET_WIDTH {1'b0}}};
	reg hit_any;
	reg [WAY_INDEX_WIDTH - 1:0] hit_way;
	reg [2:0] hit_state;
	function automatic signed [WAY_INDEX_WIDTH - 1:0] sv2v_cast_1803D_signed;
		input reg signed [WAY_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_1803D_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		hit_any = 1'b0;
		hit_way = 1'sb0;
		hit_state = 3'b000;
		begin : sv2v_autoblock_1
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				if ((!hit_any && (ctrl_tag_a_tag_state[(w * TAG_STATE_WIDTH) + (TAG_STATE_WIDTH - 1)-:TAG_WIDTH] == req_tag)) && (((ctrl_tag_a_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b001) || (ctrl_tag_a_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b010)) || (ctrl_tag_a_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b011))) begin
					hit_any = 1'b1;
					hit_way = sv2v_cast_1803D_signed(w);
					hit_state = ctrl_tag_a_tag_state[(w * TAG_STATE_WIDTH) + 2-:3];
				end
		end
	end
	reg [2 - 1:0] hit_way_onehot;
	reg [2 - 1:0] victim_way_onehot;
	reg [2 - 1:0] sn_hit_way_onehot;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				begin
					hit_way_onehot[w] = hit_way_q == sv2v_cast_1803D_signed(w);
					victim_way_onehot[w] = victim_way_q == sv2v_cast_1803D_signed(w);
					sn_hit_way_onehot[w] = sn_hit_way_q == sv2v_cast_1803D_signed(w);
				end
		end
	end
	wire [LINE_ADDR_WIDTH - 1:0] w_sn_line_addr;
	wire [SET_INDEX_WIDTH - 1:0] sn_set_grant;
	wire [SET_INDEX_WIDTH - 1:0] sn_set_q;
	wire [TAG_WIDTH - 1:0] sn_tag_grant;
	assign sn_set_grant = ctrl_snoop_addr[LINE_OFFSET_WIDTH+:SET_INDEX_WIDTH];
	assign sn_tag_grant = ctrl_snoop_addr[32 - 1-:TAG_WIDTH];
	assign sn_set_q = sn_addr_q[LINE_OFFSET_WIDTH+:SET_INDEX_WIDTH];
	assign w_sn_line_addr = (state_q == 12'b010000000000 ? sn_addr_q[32 - 1:LINE_OFFSET_WIDTH] : ctrl_snoop_addr[32 - 1:LINE_OFFSET_WIDTH]);
	wire pf_active;
	wire [LINE_ADDR_WIDTH - 1:0] pf_addr;
	wire [2:0] pf_state;
	wire [FILL_BEATS - 1:0] pf_data_valid;
	wire pf_match;
	wire pf_beat_valid;
	wire pf_load;
	wire pf_clear;
	wire [2:0] install_state;
	wire [2:0] install_state_eff;
	assign install_state = (req_class_q == 3'b000 ? 3'b001 : 3'b011);
	assign install_state_eff = (pend_vld_q ? pend_state_q : install_state);
	assign pf_load = ((state_q == OH_MISS_FILL) && !upgr_q) && !pf_active;
	assign pf_clear = state_q == OH_FILL_WRITE;
	amber_pending_fill_bypass #(
		.ADDR_WIDTH(32),
		.SETS(16),
		.LINE_BYTES(64),
		.BUS_WIDTH(64)
	) u_pf(
		.clk(clk),
		.rst_n(rst_n),
		.pf_load(pf_load),
		.pf_load_addr(req_line_addr),
		.pf_load_state(install_state),
		.pf_beat_set(ctrl_fill_beat_valid),
		.pf_beat_idx(ctrl_fill_beat_idx),
		.pf_snoop_addr(w_sn_line_addr),
		.pf_match(pf_match),
		.pf_active(pf_active),
		.pf_addr(pf_addr),
		.pf_state(pf_state),
		.pf_data_valid(pf_data_valid),
		.pf_beat_valid(pf_beat_valid),
		.pf_clear(pf_clear)
	);
	wire victim_busy_unused;
	wire victim_empty_unused;
	wire victim_valid;
	wire [32 - 1:0] victim_buf_addr;
	wire [(64 * 8) - 1:0] victim_buf_data;
	amber_victim #(
		.ADDR_WIDTH(32),
		.SETS(16),
		.LINE_BYTES(64),
		.BUS_WIDTH(64)
	) u_victim(
		.clk(clk),
		.rst_n(rst_n),
		.victim_load(ctrl_victim_load),
		.victim_addr_in(ctrl_victim_addr_in),
		.victim_data_in(ctrl_victim_data_in),
		.victim_clear(ctrl_drain_done),
		.victim_busy(victim_busy_unused),
		.victim_empty(victim_empty_unused),
		.victim_valid(victim_valid),
		.victim_addr(victim_buf_addr),
		.victim_data(victim_buf_data)
	);
	reg sn_hit_any;
	reg [WAY_INDEX_WIDTH - 1:0] sn_hit_way;
	reg [2:0] sn_hit_state;
	reg [TAG_WIDTH - 1:0] sn_hit_tag;
	always @(*) begin
		if (_sv2v_0)
			;
		sn_hit_any = 1'b0;
		sn_hit_way = 1'sb0;
		sn_hit_state = 3'b000;
		sn_hit_tag = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] w;
			for (w = 0; w < 2; w = w + 1)
				if ((!sn_hit_any && (ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + (TAG_STATE_WIDTH - 1)-:TAG_WIDTH] == sn_tag_grant)) && (((ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b001) || (ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b010)) || (ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + 2-:3] == 3'b011))) begin
					sn_hit_any = 1'b1;
					sn_hit_way = sv2v_cast_1803D_signed(w);
					sn_hit_state = ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + 2-:3];
					sn_hit_tag = ctrl_tag_b_tag_state[(w * TAG_STATE_WIDTH) + (TAG_STATE_WIDTH - 1)-:TAG_WIDTH];
				end
		end
	end
	wire sn_pf_gnt_match;
	assign sn_pf_gnt_match = pf_match && (state_q == OH_MISS_FILL);
	wire sn_stale_gnt;
	assign sn_stale_gnt = (((((state_q == OH_MISS_FILL) && !upgr_q) && sn_hit_any) && (sn_set_grant == req_set)) && (sn_hit_way == victim_way_q)) && (sn_hit_tag == victim_tag_q);
	wire victim_match;
	assign victim_match = victim_valid && (w_sn_line_addr == victim_buf_addr[32 - 1:LINE_OFFSET_WIDTH]);
	wire sn_upgr_line_gnt;
	assign sn_upgr_line_gnt = (((state_q == OH_MISS_FILL) && upgr_q) && sn_hit_any) && ({sn_hit_tag, sn_set_grant} == req_line_addr);
	wire [2:0] sn_ref_grant;
	assign sn_ref_grant = (sn_pf_gnt_match ? pf_state : (sn_stale_gnt ? 3'b000 : (victim_match ? 3'b011 : (sn_hit_any ? sn_hit_state : 3'b000))));
	wire sn_idle_ok;
	wire sn_fill_ok;
	wire sn_drain_ok;
	wire snoop_gnt;
	assign sn_idle_ok = state_q == OH_IDLE;
	assign sn_fill_ok = (state_q == OH_MISS_FILL) && (upgr_q || pf_active);
	assign sn_drain_ok = state_q == OH_MISS_DRAIN;
	assign snoop_gnt = ctrl_snoop_req && ((sn_idle_ok || sn_fill_ok) || sn_drain_ok);
	assign ctrl_snoop_ready = snoop_gnt;
	assign ctrl_tag_b_req = snoop_gnt || (state_q == OH_SNOOP);
	assign ctrl_tag_b_set = (state_q == 12'b010000000000 ? sn_set_q : sn_set_grant);
	wire [2:0] mv_victim_state;
	wire bypass_match;
	wire kmap_victim_dirty;
	wire kmap_start_drain;
	wire kmap_start_fill;
	wire kmap_replay_now;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign mv_victim_state = ctrl_tag_a_tag_state[(sv2v_cast_32(ctrl_repl_way) * TAG_STATE_WIDTH) + 2-:3];
	assign bypass_match = pf_active && (req_line_addr == pf_addr);
	assign kmap_victim_dirty = (mv_cnt_q == {(BEAT_INDEX_WIDTH >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - BEAT_INDEX_WIDTH) {1'sb0}} ? mv_victim_state == 3'b011 : victim_state_q == 3'b011);
	assign kmap_start_drain = kmap_victim_dirty && !bypass_match;
	assign kmap_start_fill = !kmap_victim_dirty && !bypass_match;
	assign kmap_replay_now = bypass_match;
	wire [4:0] sn_crresp_grant;
	function automatic [4:0] amber_pkg_amber_snoop_crresp;
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
			amber_pkg_amber_snoop_crresp = {wu, is, pd, 1'b0, dt};
		end
	endfunction
	assign sn_crresp_grant = amber_pkg_amber_snoop_crresp(sn_ref_grant, ctrl_snoop_type);
	wire [2:0] w_sn_nxt;
	function automatic [2:0] amber_pkg_amber_snoop_next_state;
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
			amber_pkg_amber_snoop_next_state = nxt;
		end
	endfunction
	assign w_sn_nxt = amber_pkg_amber_snoop_next_state(sn_ref_q, sn_type_q);
	wire sn_wr_tag;
	assign sn_wr_tag = ((((sn_hit_any_q && !sn_pf_q) && !sn_stale_q) && !sn_victim_q) && !sn_upgr_line_q) && (w_sn_nxt != sn_hit_state_q);
	wire sn_beat_gated;
	wire sn_complete;
	assign sn_beat_gated = sn_dt_q && (sn_pf_q ? pf_data_valid[sv2v_cast_32(sn_beat_q)] : 1'b1);
	function automatic signed [BEAT_INDEX_WIDTH - 1:0] sv2v_cast_9FF7F_signed;
		input reg signed [BEAT_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_9FF7F_signed = inp;
	endfunction
	assign sn_complete = (sn_dt_q ? (sn_beat_gated && ctrl_cdready) && (sn_beat_q == sv2v_cast_9FF7F_signed(FILL_BEATS - 1)) : 1'b1);
	function automatic signed [SET_INDEX_WIDTH - 1:0] sv2v_cast_CC260_signed;
		input reg signed [SET_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_CC260_signed = inp;
	endfunction
	wire init_last = init_cnt_q == sv2v_cast_CC260_signed(16 - 1);
	function automatic signed [((BEAT_INDEX_WIDTH + 0) >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - (BEAT_INDEX_WIDTH + 0)) - 1:0] sv2v_cast_DE5CF_signed;
		input reg signed [((BEAT_INDEX_WIDTH + 0) >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - (BEAT_INDEX_WIDTH + 0)) - 1:0] inp;
		sv2v_cast_DE5CF_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		state_d = OH_ERROR;
		(* full_case, parallel_case *)
		case (state_q)
			OH_IDLE:
				if (snoop_gnt)
					state_d = OH_SNOOP;
				else if (req_valid)
					state_d = OH_LOOKUP;
				else
					state_d = OH_IDLE;
			OH_INIT:
				if (init_last)
					state_d = OH_IDLE;
				else
					state_d = OH_INIT;
			OH_LOOKUP:
				if (!req_we_q && hit_any)
					state_d = OH_HIT_RD;
				else if (req_we_q && ((hit_state == 3'b010) || (hit_state == 3'b011)))
					state_d = OH_HIT_WR;
				else if (req_we_q && (hit_state == 3'b001))
					state_d = OH_MISS_FILL;
				else
					state_d = OH_MISS_VICTIM;
			OH_HIT_RD: state_d = OH_IDLE;
			OH_HIT_WR: state_d = OH_IDLE;
			OH_MISS_VICTIM:
				if (kmap_replay_now)
					state_d = OH_REPLAY;
				else if ((mv_cnt_q == {(BEAT_INDEX_WIDTH >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - BEAT_INDEX_WIDTH) {1'sb0}}) && kmap_start_fill)
					state_d = OH_MISS_FILL;
				else if (mv_cnt_q == sv2v_cast_DE5CF_signed(FILL_BEATS))
					state_d = OH_MISS_DRAIN;
				else
					state_d = OH_MISS_VICTIM;
			OH_MISS_DRAIN:
				if (snoop_gnt)
					state_d = OH_SNOOP;
				else if (drain_seen_q && drain_done_q)
					state_d = OH_MISS_FILL;
				else
					state_d = OH_MISS_DRAIN;
			OH_MISS_FILL:
				if (snoop_gnt)
					state_d = OH_SNOOP;
				else if (fill_seen_q && fill_done_q)
					state_d = OH_FILL_WRITE;
				else
					state_d = OH_MISS_FILL;
			OH_FILL_WRITE: state_d = OH_REPLAY;
			OH_REPLAY: state_d = OH_LOOKUP;
			OH_SNOOP:
				if (sn_complete)
					state_d = (sn_back_to_lookup_q ? OH_LOOKUP : sn_return_q);
				else
					state_d = OH_SNOOP;
			OH_ERROR: state_d = OH_ERROR;
			default: state_d = OH_ERROR;
		endcase
	end
	localparam signed [31:0] amber_pkg_AMBER_CRRESP_DT = 0;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			state_q <= OH_INIT;
			req_addr_q <= 1'sb0;
			req_we_q <= 1'b0;
			req_be_q <= 1'sb0;
			req_wdata_q <= 1'sb0;
			hit_way_q <= 1'sb0;
			hit_state_q <= 3'b000;
			req_class_q <= 3'b000;
			upgr_q <= 1'b0;
			victim_way_q <= 1'sb0;
			victim_tag_q <= 1'sb0;
			victim_state_q <= 3'b000;
			victim_line_q <= 1'sb0;
			mv_cnt_q <= 1'sb0;
			fill_seen_q <= 1'b0;
			fill_done_q <= 1'b0;
			drain_seen_q <= 1'b0;
			drain_done_q <= 1'b0;
			rsp_valid_q <= 1'b0;
			rsp_data_q <= 1'sb0;
			init_cnt_q <= 1'sb0;
			sn_addr_q <= 1'sb0;
			sn_type_q <= 1'sb0;
			sn_beat_q <= 1'sb0;
			sn_return_q <= OH_IDLE;
			sn_back_to_lookup_q <= 1'b0;
			sn_pf_q <= 1'b0;
			sn_hit_any_q <= 1'b0;
			sn_hit_way_q <= 1'sb0;
			sn_hit_state_q <= 3'b000;
			sn_hit_tag_q <= 1'sb0;
			sn_stale_q <= 1'b0;
			sn_victim_q <= 1'b0;
			sn_upgr_line_q <= 1'b0;
			sn_dt_q <= 1'b0;
			sn_ref_q <= 3'b000;
			pend_vld_q <= 1'b0;
			pend_state_q <= 3'b000;
		end
		else begin
			state_q <= state_d;
			rsp_valid_q <= 1'b0;
			if (ctrl_fill_done)
				fill_done_q <= 1'b1;
			if (ctrl_drain_done)
				drain_done_q <= 1'b1;
			if (snoop_gnt) begin
				sn_addr_q <= ctrl_snoop_addr;
				sn_type_q <= ctrl_snoop_type;
				sn_beat_q <= 1'sb0;
				sn_return_q <= state_q;
				sn_back_to_lookup_q <= (state_q == OH_IDLE) && req_valid;
				sn_pf_q <= sn_pf_gnt_match;
				sn_hit_any_q <= sn_hit_any;
				sn_hit_way_q <= sn_hit_way;
				sn_hit_state_q <= sn_hit_state;
				sn_hit_tag_q <= sn_hit_tag;
				sn_stale_q <= sn_stale_gnt;
				sn_victim_q <= victim_match;
				sn_upgr_line_q <= sn_upgr_line_gnt;
				sn_dt_q <= sn_crresp_grant[amber_pkg_AMBER_CRRESP_DT];
				sn_ref_q <= sn_ref_grant;
			end
			else if (state_q == OH_SNOOP) begin
				if (sn_beat_gated && ctrl_cdready)
					sn_beat_q <= sn_beat_q + 1'b1;
			end
			if (((((state_q == OH_SNOOP) && sn_complete) && (sn_return_q == OH_MISS_FILL)) && (sn_pf_q || sn_upgr_line_q)) && (w_sn_nxt != sn_ref_q)) begin
				if (w_sn_nxt == 3'b000) begin
					pend_vld_q <= 1'b1;
					pend_state_q <= 3'b000;
				end
				else if ((w_sn_nxt == 3'b001) && !pend_vld_q) begin
					pend_vld_q <= 1'b1;
					pend_state_q <= 3'b001;
				end
			end
			(* full_case, parallel_case *)
			case (state_q)
				OH_IDLE:
					if (req_valid) begin
						req_addr_q <= req_addr;
						req_we_q <= req_we;
						req_be_q <= req_be;
						req_wdata_q <= req_wdata;
					end
				OH_INIT:
					if (!init_last)
						init_cnt_q <= init_cnt_q + 1'b1;
				OH_LOOKUP: begin
					hit_way_q <= hit_way;
					hit_state_q <= hit_state;
					upgr_q <= 1'b0;
					if (req_we_q && (hit_state == 3'b001)) begin
						req_class_q <= 3'b010;
						upgr_q <= 1'b1;
					end
					else if (!hit_any)
						req_class_q <= (req_we_q ? 3'b001 : 3'b000);
				end
				OH_HIT_RD: begin
					rsp_valid_q <= 1'b1;
					rsp_data_q <= ctrl_data_a_rdata;
				end
				OH_HIT_WR: begin
					rsp_valid_q <= 1'b1;
					rsp_data_q <= req_wdata_q;
				end
				OH_MISS_VICTIM:
					if (mv_cnt_q == {(BEAT_INDEX_WIDTH >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - BEAT_INDEX_WIDTH) {1'sb0}}) begin
						victim_way_q <= ctrl_repl_way;
						victim_tag_q <= ctrl_tag_a_tag_state[(sv2v_cast_32(ctrl_repl_way) * TAG_STATE_WIDTH) + (TAG_STATE_WIDTH - 1)-:TAG_WIDTH];
						victim_state_q <= mv_victim_state;
						victim_line_q[0+:64] <= ctrl_data_a_rdata;
						mv_cnt_q <= mv_cnt_q + 1'b1;
					end
					else if (mv_cnt_q < sv2v_cast_DE5CF_signed(FILL_BEATS)) begin
						victim_line_q[sv2v_cast_32(mv_cnt_q) * 64+:64] <= ctrl_data_a_rdata;
						mv_cnt_q <= mv_cnt_q + 1'b1;
					end
					else
						mv_cnt_q <= 1'sb0;
				OH_MISS_FILL: fill_seen_q <= 1'b1;
				OH_MISS_DRAIN: drain_seen_q <= 1'b1;
				OH_FILL_WRITE: begin
					mv_cnt_q <= 1'sb0;
					fill_seen_q <= 1'b0;
					fill_done_q <= 1'b0;
					drain_seen_q <= 1'b0;
					drain_done_q <= 1'b0;
					pend_vld_q <= 1'b0;
				end
				default:
					;
			endcase
		end
	always @(*) begin
		if (_sv2v_0)
			;
		ctrl_tag_a_set = req_set;
		ctrl_tag_a_wr_en = 1'b0;
		ctrl_tag_a_wr_way_onehot = 1'sb0;
		ctrl_tag_a_wr_set = req_set;
		ctrl_tag_a_wr_tag_state = 1'sb0;
		ctrl_data_a_addr = {req_set, req_beat};
		ctrl_data_a_way = hit_way_q;
		ctrl_data_a_wr_en = 1'b0;
		ctrl_data_a_wr_way_onehot = hit_way_onehot;
		ctrl_data_a_wr_addr = {req_set, req_beat};
		ctrl_data_a_wr_wdata = req_wdata_q;
		ctrl_data_a_wr_be = req_be_q;
		ctrl_data_b_addr = {sn_set_q, sn_beat_q};
		ctrl_data_b_way = (sn_pf_q ? victim_way_q : sn_hit_way_q);
		ctrl_repl_req = 1'b0;
		ctrl_repl_set = req_set;
		ctrl_repl_hit = 1'b0;
		ctrl_repl_update = 1'b0;
		ctrl_repl_hit_way = hit_way_q;
		ctrl_victim_load = 1'b0;
		ctrl_victim_addr_in = {victim_tag_q, req_set, {LINE_OFFSET_WIDTH {1'b0}}};
		ctrl_victim_data_in = victim_line_q;
		ctrl_fill_start = 1'b0;
		ctrl_fill_addr = req_line_base;
		ctrl_drain_start = 1'b0;
		ctrl_crresp = amber_pkg_amber_snoop_crresp((state_q == 12'b010000000000 ? sn_ref_q : sn_ref_grant), (state_q == 12'b010000000000 ? sn_type_q : ctrl_snoop_type));
		ctrl_cddata = (sn_victim_q ? victim_buf_data[sv2v_cast_32(sn_beat_q) * 64+:64] : ctrl_data_b_rdata);
		ctrl_cdlast = 1'b0;
		ctrl_cdvalid = 1'b0;
		(* full_case, parallel_case *)
		case (state_q)
			OH_INIT: begin
				ctrl_tag_a_wr_en = !(!rst_n);
				ctrl_tag_a_wr_way_onehot = {2 {1'b1}};
				ctrl_tag_a_wr_set = init_cnt_q;
				ctrl_tag_a_wr_tag_state = {{TAG_WIDTH {1'b0}}, 3'b000};
			end
			OH_HIT_WR: begin
				ctrl_data_a_wr_en = 1'b1;
				ctrl_tag_a_wr_en = hit_state_q != 3'b011;
				ctrl_tag_a_wr_way_onehot = hit_way_onehot;
				ctrl_tag_a_wr_tag_state = {req_tag, 3'b011};
				ctrl_repl_hit = 1'b1;
			end
			OH_HIT_RD: ctrl_repl_hit = 1'b1;
			OH_MISS_VICTIM:
				if (mv_cnt_q == {(BEAT_INDEX_WIDTH >= 0 ? BEAT_INDEX_WIDTH + 1 : 1 - BEAT_INDEX_WIDTH) {1'sb0}}) begin
					ctrl_repl_req = 1'b1;
					ctrl_data_a_addr = {req_set, {BEAT_INDEX_WIDTH {1'b0}}};
					ctrl_data_a_way = ctrl_repl_way;
				end
				else if (mv_cnt_q < sv2v_cast_DE5CF_signed(FILL_BEATS)) begin
					ctrl_data_a_addr = {req_set, mv_cnt_q[BEAT_INDEX_WIDTH - 1:0]};
					ctrl_data_a_way = victim_way_q;
				end
				else
					ctrl_victim_load = 1'b1;
			OH_MISS_FILL: ctrl_fill_start = !fill_seen_q;
			OH_MISS_DRAIN: ctrl_drain_start = !drain_seen_q;
			OH_FILL_WRITE: begin
				ctrl_tag_a_wr_en = 1'b1;
				ctrl_tag_a_wr_way_onehot = (upgr_q ? hit_way_onehot : victim_way_onehot);
				ctrl_tag_a_wr_tag_state = {req_tag, install_state_eff};
				if (upgr_q) begin
					ctrl_repl_hit = 1'b1;
					ctrl_repl_hit_way = hit_way_q;
				end
				else begin
					ctrl_repl_update = 1'b1;
					ctrl_repl_hit_way = victim_way_q;
				end
			end
			OH_SNOOP: begin
				ctrl_cdvalid = sn_beat_gated;
				ctrl_cdlast = sn_beat_q == sv2v_cast_9FF7F_signed(FILL_BEATS - 1);
				if (sn_complete && sn_wr_tag) begin
					ctrl_tag_a_wr_en = 1'b1;
					ctrl_tag_a_wr_way_onehot = sn_hit_way_onehot;
					ctrl_tag_a_wr_set = sn_set_q;
					ctrl_tag_a_wr_tag_state = {sn_hit_tag_q, w_sn_nxt};
				end
			end
			default:
				;
		endcase
	end
	assign ctrl_req_ready = state_q == OH_IDLE;
	assign ctrl_rsp_valid = rsp_valid_q;
	assign ctrl_rsp_data = rsp_data_q;
	assign ctrl_init_busy = state_q == OH_INIT;
	assign ctrl_init_set = init_cnt_q;
	assign ctrl_req_class = req_class_q;
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (state_q)
			OH_IDLE: ctrl_state = 4'h0;
			OH_INIT: ctrl_state = 4'h1;
			OH_LOOKUP: ctrl_state = 4'h2;
			OH_HIT_RD: ctrl_state = 4'h3;
			OH_HIT_WR: ctrl_state = 4'h4;
			OH_MISS_VICTIM: ctrl_state = 4'h5;
			OH_MISS_DRAIN: ctrl_state = 4'h6;
			OH_MISS_FILL: ctrl_state = 4'h7;
			OH_FILL_WRITE: ctrl_state = 4'h8;
			OH_REPLAY: ctrl_state = 4'h9;
			OH_SNOOP: ctrl_state = 4'ha;
			OH_ERROR: ctrl_state = 4'hb;
			default: ctrl_state = 4'hb;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
