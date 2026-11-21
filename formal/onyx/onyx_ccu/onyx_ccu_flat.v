module onyx_ccu (
	clk,
	rst_n,
	c_arid,
	c_araddr,
	c_arlen,
	c_arsize,
	c_arburst,
	c_arlock,
	c_arcache,
	c_arprot,
	c_arqos,
	c_arregion,
	c_aruser,
	c_arvalid,
	c_arready,
	c_rid,
	c_rdata,
	c_rresp,
	c_rlast,
	c_ruser,
	c_rvalid,
	c_rready,
	c_awid,
	c_awaddr,
	c_awlen,
	c_awsize,
	c_awburst,
	c_awlock,
	c_awcache,
	c_awprot,
	c_awqos,
	c_awregion,
	c_awuser,
	c_awvalid,
	c_awready,
	c_wdata,
	c_wstrb,
	c_wlast,
	c_wuser,
	c_wvalid,
	c_wready,
	c_bid,
	c_bresp,
	c_buser,
	c_bvalid,
	c_bready,
	s_acaddr,
	s_acsnoop,
	s_acprot,
	s_acvalid,
	s_acready,
	s_crresp,
	s_crvalid,
	s_crready,
	s_cddata,
	s_cdlast,
	s_cdvalid,
	s_cdready,
	c_coh_req_valid,
	c_coh_req_addr,
	c_coh_req_type,
	c_coh_done_valid,
	c_coh_done_id,
	mem_arid,
	mem_araddr,
	mem_arlen,
	mem_arsize,
	mem_arburst,
	mem_arlock,
	mem_arcache,
	mem_arprot,
	mem_arqos,
	mem_arregion,
	mem_aruser,
	mem_arvalid,
	mem_arready,
	mem_rid,
	mem_rdata,
	mem_rresp,
	mem_rlast,
	mem_ruser,
	mem_rvalid,
	mem_rready,
	mem_awid,
	mem_awaddr,
	mem_awlen,
	mem_awsize,
	mem_awburst,
	mem_awlock,
	mem_awcache,
	mem_awprot,
	mem_awqos,
	mem_awregion,
	mem_awuser,
	mem_awvalid,
	mem_awready,
	mem_wdata,
	mem_wstrb,
	mem_wlast,
	mem_wuser,
	mem_wvalid,
	mem_wready,
	mem_bid,
	mem_bresp,
	mem_buser,
	mem_bvalid,
	mem_bready,
	dbg_busy,
	dbg_slot_vld,
	dbg_pend_vld,
	dbg_abs_pend,
	dbg_grant,
	dbg_grant_dir,
	dbg_grant_addr,
	dbg_grant_slot
);
	reg _sv2v_0;
	localparam signed [31:0] l1_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] l1_pkg_AMBER_LINE_BYTES = 64;
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] STRB_W = 32 / 8;
	localparam signed [31:0] FILL_BEATS = 16 / STRB_W;
	localparam signed [31:0] BEAT_INDEX_WIDTH = $clog2(FILL_BEATS);
	localparam signed [31:0] IW = 3;
	localparam signed [31:0] UW = 1;
	localparam signed [31:0] SLOT_W = (4 > 1 ? $clog2(4) : 1);
	localparam signed [31:0] PORT_W = (2 > 1 ? $clog2(2) : 1);
	localparam signed [31:0] OFFSET_W = $clog2(16);
	localparam signed [31:0] LINE_W = 8 - OFFSET_W;
	input wire clk;
	input wire rst_n;
	input wire [(2 * IW) - 1:0] c_arid;
	input wire [(2 * 8) - 1:0] c_araddr;
	input wire [(2 * 8) - 1:0] c_arlen;
	input wire [(2 * 3) - 1:0] c_arsize;
	input wire [(2 * 2) - 1:0] c_arburst;
	input wire [2 - 1:0] c_arlock;
	input wire [(2 * 4) - 1:0] c_arcache;
	input wire [(2 * 3) - 1:0] c_arprot;
	input wire [(2 * 4) - 1:0] c_arqos;
	input wire [(2 * 4) - 1:0] c_arregion;
	input wire [(2 * UW) - 1:0] c_aruser;
	input wire [2 - 1:0] c_arvalid;
	output wire [2 - 1:0] c_arready;
	output reg [(2 * IW) - 1:0] c_rid;
	output reg [(2 * 32) - 1:0] c_rdata;
	output reg [(2 * 2) - 1:0] c_rresp;
	output wire [2 - 1:0] c_rlast;
	output reg [(2 * UW) - 1:0] c_ruser;
	output wire [2 - 1:0] c_rvalid;
	input wire [2 - 1:0] c_rready;
	input wire [(2 * IW) - 1:0] c_awid;
	input wire [(2 * 8) - 1:0] c_awaddr;
	input wire [(2 * 8) - 1:0] c_awlen;
	input wire [(2 * 3) - 1:0] c_awsize;
	input wire [(2 * 2) - 1:0] c_awburst;
	input wire [2 - 1:0] c_awlock;
	input wire [(2 * 4) - 1:0] c_awcache;
	input wire [(2 * 3) - 1:0] c_awprot;
	input wire [(2 * 4) - 1:0] c_awqos;
	input wire [(2 * 4) - 1:0] c_awregion;
	input wire [(2 * UW) - 1:0] c_awuser;
	input wire [2 - 1:0] c_awvalid;
	output reg [2 - 1:0] c_awready;
	input wire [(2 * 32) - 1:0] c_wdata;
	input wire [(2 * STRB_W) - 1:0] c_wstrb;
	input wire [2 - 1:0] c_wlast;
	input wire [(2 * UW) - 1:0] c_wuser;
	input wire [2 - 1:0] c_wvalid;
	output reg [2 - 1:0] c_wready;
	output reg [(2 * IW) - 1:0] c_bid;
	output reg [(2 * 2) - 1:0] c_bresp;
	output reg [(2 * UW) - 1:0] c_buser;
	output reg [2 - 1:0] c_bvalid;
	input wire [2 - 1:0] c_bready;
	output reg [(2 * 8) - 1:0] s_acaddr;
	output reg [(2 * 4) - 1:0] s_acsnoop;
	output reg [(2 * 3) - 1:0] s_acprot;
	output reg [2 - 1:0] s_acvalid;
	input wire [2 - 1:0] s_acready;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_WIDTH = 5;
	input wire [(2 * l1_pkg_AMBER_CRRESP_WIDTH) - 1:0] s_crresp;
	input wire [2 - 1:0] s_crvalid;
	output reg [2 - 1:0] s_crready;
	input wire [(2 * 32) - 1:0] s_cddata;
	input wire [2 - 1:0] s_cdlast;
	input wire [2 - 1:0] s_cdvalid;
	output reg [2 - 1:0] s_cdready;
	input wire [2 - 1:0] c_coh_req_valid;
	input wire [(2 * 8) - 1:0] c_coh_req_addr;
	input wire [(2 * 3) - 1:0] c_coh_req_type;
	input wire [2 - 1:0] c_coh_done_valid;
	input wire [(2 * IW) - 1:0] c_coh_done_id;
	output wire [IW - 1:0] mem_arid;
	output wire [8 - 1:0] mem_araddr;
	output wire [7:0] mem_arlen;
	output wire [2:0] mem_arsize;
	output wire [1:0] mem_arburst;
	output wire mem_arlock;
	output wire [3:0] mem_arcache;
	output wire [2:0] mem_arprot;
	output wire [3:0] mem_arqos;
	output wire [3:0] mem_arregion;
	output wire [UW - 1:0] mem_aruser;
	output wire mem_arvalid;
	input wire mem_arready;
	input wire [IW - 1:0] mem_rid;
	input wire [32 - 1:0] mem_rdata;
	input wire [1:0] mem_rresp;
	input wire mem_rlast;
	input wire [UW - 1:0] mem_ruser;
	input wire mem_rvalid;
	output wire mem_rready;
	output wire [IW - 1:0] mem_awid;
	output wire [8 - 1:0] mem_awaddr;
	output wire [7:0] mem_awlen;
	output wire [2:0] mem_awsize;
	output wire [1:0] mem_awburst;
	output wire mem_awlock;
	output wire [3:0] mem_awcache;
	output wire [2:0] mem_awprot;
	output wire [3:0] mem_awqos;
	output wire [3:0] mem_awregion;
	output wire [UW - 1:0] mem_awuser;
	output wire mem_awvalid;
	input wire mem_awready;
	output wire [32 - 1:0] mem_wdata;
	output wire [STRB_W - 1:0] mem_wstrb;
	output wire mem_wlast;
	output wire [UW - 1:0] mem_wuser;
	output wire mem_wvalid;
	input wire mem_wready;
	input wire [IW - 1:0] mem_bid;
	input wire [1:0] mem_bresp;
	input wire [UW - 1:0] mem_buser;
	input wire mem_bvalid;
	output wire mem_bready;
	output wire dbg_busy;
	output wire [4 - 1:0] dbg_slot_vld;
	output reg [2 - 1:0] dbg_pend_vld;
	output wire dbg_abs_pend;
	output wire dbg_grant;
	output wire [PORT_W - 1:0] dbg_grant_dir;
	output wire [8 - 1:0] dbg_grant_addr;
	output wire [SLOT_W - 1:0] dbg_grant_slot;
	initial begin
		if ((2 < 2) || (2 > 4))
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:330:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 2 must be 2..4 (D11)");
		if ((16 & (16 - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:332:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 16 must be a power of two");
		if (((FILL_BEATS & (FILL_BEATS - 1)) != 0) || (FILL_BEATS < 2))
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:334:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 16 / 32*8 must be a power of two >= 2");
		if ((32 % 8) != 0)
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:336:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 32 must be a multiple of 8");
		if ((4 < 2) || ((1 << SLOT_W) < 4))
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:338:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 4 must be >= 2");
		if ((1 << IW) < 4)
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:340:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 2**3 must cover 4 (the memory read IDs)");
		if (2 < 1)
			$display("Error [%0t] .flat_build/prep/onyx_ccu.sv:342:13 - onyx_ccu.<unnamed_block>.<unnamed_block>\n msg: ", $time, "onyx_ccu: 2 must be >= 1");
	end
	localparam [3:0] ACSNOOP_READ_SHARED = 4'h1;
	localparam [3:0] ACSNOOP_READ_UNIQUE = 4'h7;
	localparam [3:0] ACSNOOP_MAKE_INVALID = 4'hc;
	function automatic [3:0] map_snoop;
		input reg [2:0] req_type;
		case (req_type)
			3'b000, 3'b110: map_snoop = ACSNOOP_READ_SHARED;
			3'b001: map_snoop = ACSNOOP_READ_UNIQUE;
			default: map_snoop = ACSNOOP_MAKE_INVALID;
		endcase
	endfunction
	function automatic is_nodata;
		input reg [2:0] req_type;
		is_nodata = (req_type == 3'b010) || (req_type == 3'b011);
	endfunction
	function automatic is_coh_req;
		input reg [2:0] req_type;
		is_coh_req = (req_type != 3'b100) && (req_type != 3'b101);
	endfunction
	function automatic [LINE_W - 1:0] line_of;
		input reg [8 - 1:0] addr;
		line_of = addr[8 - 1-:LINE_W];
	endfunction
	localparam signed [31:0] SNQ_W = SLOT_W + 1;
	localparam signed [31:0] SNI_W = $clog2(2 + 1);
	localparam signed [31:0] SNI_IW = (2 > 1 ? $clog2(2) : 1);
	localparam signed [31:0] PEND_DEPTH = 4;
	localparam signed [31:0] PEND_W = 3;
	localparam signed [31:0] BUF_AW = SLOT_W + BEAT_INDEX_WIDTH;
	localparam signed [31:0] BUF_DEPTH = 4 * FILL_BEATS;
	localparam signed [31:0] NW = 2 + 1;
	localparam signed [31:0] WSEL_W = $clog2(NW);
	localparam signed [31:0] NPEER = 2 - 1;
	reg [2 - 1:0] coh_req_vld;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				coh_req_vld[d] = c_coh_req_valid[d] & is_coh_req(c_coh_req_type[((2 - 1) - d) * 3+:3]);
		end
	end
	reg [4 - 1:0] r_vld;
	reg [PORT_W - 1:0] r_dir [0:4 - 1];
	reg [LINE_W - 1:0] r_line [0:4 - 1];
	reg [2:0] r_type [0:4 - 1];
	reg [4 - 1:0] r_nodata;
	reg [4 - 1:0] r_ar_taken;
	reg [IW - 1:0] r_arid [0:4 - 1];
	reg [3:0] r_arcache [0:4 - 1];
	reg [2:0] r_arprot [0:4 - 1];
	reg [UW - 1:0] r_aruser [0:4 - 1];
	reg [PORT_W - 1:0] r_ac_left [0:4 - 1];
	reg [PORT_W - 1:0] r_cr_left [0:4 - 1];
	reg [4 - 1:0] r_dt;
	reg [4 - 1:0] r_pd;
	reg [4 - 1:0] r_mem_issued;
	reg [4 - 1:0] r_mem_done;
	reg [4 - 1:0] r_rpl_done;
	reg [4 - 1:0] r_abs_issued;
	reg [4 - 1:0] r_abs_done;
	reg [4 - 1:0] r_rack;
	reg [4 - 1:0] w_ac_all;
	reg [4 - 1:0] w_gathered;
	reg [4 - 1:0] w_delivered;
	reg [4 - 1:0] w_free_now;
	wire w_mar_vld;
	wire [SLOT_W - 1:0] w_mar_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] s;
			for (s = 0; s < 4; s = s + 1)
				begin
					w_ac_all[s] = r_ac_left[s] == {PORT_W {1'sb0}};
					w_gathered[s] = r_cr_left[s] == {PORT_W {1'sb0}};
				end
		end
	end
	function automatic signed [SLOT_W - 1:0] sv2v_cast_7C1AF_signed;
		input reg signed [SLOT_W - 1:0] inp;
		sv2v_cast_7C1AF_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] s;
			for (s = 0; s < 4; s = s + 1)
				begin
					w_delivered[s] = (r_dt[s] | r_nodata[s] ? r_rpl_done[s] : r_mem_done[s]);
					w_free_now[s] = (((((r_vld[s] & w_gathered[s]) & w_delivered[s]) & (~r_mem_issued[s] | r_mem_done[s])) & ~(w_mar_vld & (w_mar_slot == sv2v_cast_7C1AF_signed(s)))) & (~r_pd[s] | r_abs_done[s])) & r_rack[s];
				end
		end
	end
	reg [2:0] r_pend_cnt [0:2 - 1];
	reg [8 - 1:0] r_pend_addr [0:2 - 1][0:3];
	reg [2:0] r_pend_type [0:2 - 1][0:3];
	reg [2 - 1:0] r_pend_ovf;
	reg [2 - 1:0] w_cand_vld;
	reg [8 - 1:0] w_cand_addr [0:2 - 1];
	reg [2:0] w_cand_type [0:2 - 1];
	reg [2 - 1:0] w_cand_live;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				if (r_pend_cnt[d] != {3 {1'sb0}}) begin
					w_cand_vld[d] = 1'b1;
					w_cand_live[d] = 1'b0;
					w_cand_addr[d] = r_pend_addr[d][0];
					w_cand_type[d] = r_pend_type[d][0];
				end
				else begin
					w_cand_vld[d] = coh_req_vld[d];
					w_cand_live[d] = 1'b1;
					w_cand_addr[d] = c_coh_req_addr[((2 - 1) - d) * 8+:8];
					w_cand_type[d] = c_coh_req_type[((2 - 1) - d) * 3+:3];
				end
		end
	end
	reg [2 - 1:0] w_cand_locked;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_cand_locked[d] = 0 & |r_vld;
					begin : sv2v_autoblock_6
						reg signed [31:0] s;
						for (s = 0; s < 4; s = s + 1)
							if (r_vld[s] && (r_line[s] == line_of(w_cand_addr[d])))
								w_cand_locked[d] = 1'b1;
					end
				end
		end
	end
	reg w_slot_free;
	reg [SLOT_W - 1:0] w_slot_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		w_slot_free = 1'b0;
		w_slot_idx = 1'sb0;
		begin : sv2v_autoblock_7
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if (!r_vld[s]) begin
					w_slot_free = 1'b1;
					w_slot_idx = sv2v_cast_7C1AF_signed(s);
				end
		end
	end
	reg [2 - 1:0] r_arw_vld;
	reg [SLOT_W - 1:0] r_arw_slot [0:2 - 1];
	reg [2 - 1:0] w_cand_ok;
	reg [PORT_W - 1:0] r_rr;
	reg w_grant;
	reg [PORT_W - 1:0] w_grant_dir;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic signed [PORT_W - 1:0] sv2v_cast_65AE2_signed;
		input reg signed [PORT_W - 1:0] inp;
		sv2v_cast_65AE2_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				w_cand_ok[d] = ((w_cand_vld[d] & ~w_cand_locked[d]) & w_slot_free) & ~r_arw_vld[d];
		end
		w_grant = |w_cand_ok;
		w_grant_dir = r_rr;
		begin : sv2v_autoblock_9
			reg signed [31:0] k;
			for (k = 2 - 1; k >= 0; k = k - 1)
				begin : sv2v_autoblock_10
					reg signed [31:0] idx;
					idx = (sv2v_cast_32(r_rr) + k) % 2;
					if (w_cand_ok[idx])
						w_grant_dir = sv2v_cast_65AE2_signed(idx);
				end
		end
	end
	assign c_arready = r_arw_vld;
	wire [2 - 1:0] w_ar_take = c_arvalid & c_arready;
	reg [SLOT_W - 1:0] r_snq [0:2 - 1][0:4 - 1];
	reg [SNQ_W - 1:0] r_snq_cnt [0:2 - 1];
	reg [SLOT_W - 1:0] r_sni [0:2 - 1][0:2 - 1];
	reg [SNI_W - 1:0] r_sni_cnt [0:2 - 1];
	reg [BEAT_INDEX_WIDTH - 1:0] r_cd_beat [0:2 - 1];
	reg [2 - 1:0] w_ac_vld;
	reg [2 - 1:0] w_ac_hs;
	reg [2 - 1:0] w_cr_hs;
	reg [2 - 1:0] w_cd_want;
	reg [2 - 1:0] w_cd_hs;
	reg [SLOT_W - 1:0] w_ac_slot [0:2 - 1];
	reg [SLOT_W - 1:0] w_sni_head [0:2 - 1];
	function automatic signed [SNI_W - 1:0] sv2v_cast_F4A8C_signed;
		input reg signed [SNI_W - 1:0] inp;
		sv2v_cast_F4A8C_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_11
			reg signed [31:0] p;
			for (p = 0; p < 2; p = p + 1)
				begin
					w_ac_slot[p] = r_snq[p][0];
					w_ac_vld[p] = (r_snq_cnt[p] != {SNQ_W {1'sb0}}) && (r_sni_cnt[p] < sv2v_cast_F4A8C_signed(2));
					w_ac_hs[p] = w_ac_vld[p] & s_acready[p];
					w_sni_head[p] = r_sni[p][0];
					w_cr_hs[p] = s_crvalid[p] & (r_sni_cnt[p] != {SNI_W {1'sb0}});
					w_cd_want[p] = s_cdvalid[p] & (r_sni_cnt[p] != {SNI_W {1'sb0}});
				end
		end
	end
	function automatic signed [OFFSET_W - 1:0] sv2v_cast_2EB38_signed;
		input reg signed [OFFSET_W - 1:0] inp;
		sv2v_cast_2EB38_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_12
			reg signed [31:0] p;
			for (p = 0; p < 2; p = p + 1)
				begin
					s_acaddr[((2 - 1) - p) * 8+:8] = {r_line[w_ac_slot[p]], sv2v_cast_2EB38_signed(0)};
					s_acsnoop[((2 - 1) - p) * 4+:4] = map_snoop(r_type[w_ac_slot[p]]);
					s_acprot[((2 - 1) - p) * 3+:3] = 3'b000;
					s_acvalid[p] = w_ac_vld[p];
					s_crready[p] = r_sni_cnt[p] != {SNI_W {1'sb0}};
				end
		end
	end
	reg [PORT_W - 1:0] w_cd_tgt [0:2 - 1];
	reg [PORT_W - 1:0] r_cd_rr [0:2 - 1];
	reg [2 - 1:0] w_buf_we;
	reg [PORT_W - 1:0] w_buf_src [0:2 - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_13
			reg signed [31:0] p;
			for (p = 0; p < 2; p = p + 1)
				w_cd_tgt[p] = r_dir[w_sni_head[p]];
		end
		begin : sv2v_autoblock_14
			reg signed [31:0] a;
			for (a = 0; a < 2; a = a + 1)
				begin
					w_buf_we[a] = 1'b0;
					w_buf_src[a] = r_cd_rr[a];
					begin : sv2v_autoblock_15
						reg signed [31:0] k;
						for (k = 2 - 1; k >= 0; k = k - 1)
							begin : sv2v_autoblock_16
								reg signed [31:0] p;
								p = (sv2v_cast_32(r_cd_rr[a]) + k) % 2;
								if (w_cd_want[p] && (w_cd_tgt[p] == sv2v_cast_65AE2_signed(a))) begin
									w_buf_we[a] = 1'b1;
									w_buf_src[a] = sv2v_cast_65AE2_signed(p);
								end
							end
					end
				end
		end
		begin : sv2v_autoblock_17
			reg signed [31:0] p;
			for (p = 0; p < 2; p = p + 1)
				begin
					s_cdready[p] = (w_cd_want[p] & w_buf_we[w_cd_tgt[p]]) & (w_buf_src[w_cd_tgt[p]] == sv2v_cast_65AE2_signed(p));
					w_cd_hs[p] = s_cdready[p];
				end
		end
	end
	reg w_marc_vld;
	reg [SLOT_W - 1:0] w_marc_slot;
	reg r_mar_vld;
	reg [SLOT_W - 1:0] r_mar_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		w_marc_vld = 1'b0;
		w_marc_slot = 1'sb0;
		begin : sv2v_autoblock_18
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if (((((r_vld[s] && r_ar_taken[s]) && !r_nodata[s]) && !r_mem_issued[s]) && !r_dt[s]) && (0 ? w_gathered[s] : w_ac_all[s])) begin
					w_marc_vld = 1'b1;
					w_marc_slot = sv2v_cast_7C1AF_signed(s);
				end
		end
	end
	assign w_mar_vld = r_mar_vld | w_marc_vld;
	assign w_mar_slot = (r_mar_vld ? r_mar_slot : w_marc_slot);
	wire w_mar_hs = w_mar_vld & mem_arready;
	function automatic [IW - 1:0] sv2v_cast_83959;
		input reg [IW - 1:0] inp;
		sv2v_cast_83959 = inp;
	endfunction
	assign mem_arid = sv2v_cast_83959(w_mar_slot);
	assign mem_araddr = {r_line[w_mar_slot], sv2v_cast_2EB38_signed(0)};
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	assign mem_arlen = sv2v_cast_8_signed(FILL_BEATS - 1);
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign mem_arsize = sv2v_cast_3_signed($clog2(STRB_W));
	assign mem_arburst = 2'b01;
	assign mem_arlock = 1'b0;
	assign mem_arcache = r_arcache[w_mar_slot];
	assign mem_arprot = r_arprot[w_mar_slot];
	assign mem_arqos = 4'b0000;
	assign mem_arregion = 4'b0000;
	assign mem_aruser = r_aruser[w_mar_slot];
	assign mem_arvalid = w_mar_vld;
	wire [SLOT_W - 1:0] w_mr_slot = mem_rid[SLOT_W - 1:0];
	wire w_mr_live = ((mem_rvalid & r_vld[w_mr_slot]) & r_mem_issued[w_mr_slot]) & ~r_mem_done[w_mr_slot];
	wire w_mr_fwd = (w_mr_live & w_gathered[w_mr_slot]) & ~r_dt[w_mr_slot];
	wire w_mr_drop = w_mr_live & r_dt[w_mr_slot];
	wire [PORT_W - 1:0] w_mr_dir = r_dir[w_mr_slot];
	reg [2 - 1:0] r_rpl_vld;
	reg [SLOT_W - 1:0] r_rpl_slot [0:2 - 1];
	reg [BEAT_INDEX_WIDTH - 1:0] r_rpl_beat [0:2 - 1];
	reg [2 - 1:0] r_rpl_hold;
	reg [2 - 1:0] w_rplc_vld;
	reg [SLOT_W - 1:0] w_rplc_slot [0:2 - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_19
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_rplc_vld[d] = 1'b0;
					w_rplc_slot[d] = 1'sb0;
					begin : sv2v_autoblock_20
						reg signed [31:0] s;
						for (s = 4 - 1; s >= 0; s = s - 1)
							if ((((((r_vld[s] && (r_dir[s] == sv2v_cast_65AE2_signed(d))) && w_gathered[s]) && r_ar_taken[s]) && (r_dt[s] || r_nodata[s])) && !r_rpl_done[s]) && !(r_rpl_vld[d] && (r_rpl_slot[d] == sv2v_cast_7C1AF_signed(s)))) begin
								w_rplc_vld[d] = 1'b1;
								w_rplc_slot[d] = sv2v_cast_7C1AF_signed(s);
							end
					end
				end
		end
	end
	reg [BUF_AW - 1:0] w_buf_waddr [0:2 - 1];
	reg [32 - 1:0] w_buf_wdata [0:2 - 1];
	reg [BUF_AW - 1:0] w_rpl_raddr [0:2 - 1];
	wire [32 - 1:0] w_rpl_rdata [0:2 - 1];
	wire [BUF_AW - 1:0] w_abs_raddr;
	wire [32 - 1:0] w_abs_rdata_a [0:2 - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_21
			reg signed [31:0] a;
			for (a = 0; a < 2; a = a + 1)
				begin
					w_buf_waddr[a] = {w_sni_head[w_buf_src[a]], r_cd_beat[w_buf_src[a]]};
					w_buf_wdata[a] = s_cddata[((2 - 1) - w_buf_src[a]) * 32+:32];
				end
		end
		begin : sv2v_autoblock_22
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				w_rpl_raddr[d] = {r_rpl_slot[d], r_rpl_beat[d]};
		end
	end
	genvar _gv_a_1;
	generate
		for (_gv_a_1 = 0; _gv_a_1 < 2; _gv_a_1 = _gv_a_1 + 1) begin : g_buf
			localparam a = _gv_a_1;
			(* ram_style = "distributed" *) reg [32 - 1:0] mem [0:BUF_DEPTH - 1];
			always @(posedge clk)
				if (w_buf_we[a])
					mem[w_buf_waddr[a]] <= w_buf_wdata[a];
			assign w_rpl_rdata[a] = mem[w_rpl_raddr[a]];
			assign w_abs_rdata_a[a] = mem[w_abs_raddr];
		end
	endgenerate
	reg [2 - 1:0] w_mem_want;
	reg [2 - 1:0] w_rpl_pres;
	reg [2 - 1:0] w_mem_pres;
	reg [2 - 1:0] w_rvalid;
	reg [2 - 1:0] w_rpl_hs;
	reg [2 - 1:0] w_mem_hs;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_23
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_mem_want[d] = w_mr_fwd & (w_mr_dir == sv2v_cast_65AE2_signed(d));
					w_rpl_pres[d] = r_rpl_vld[d] & (r_rpl_hold[d] | ~w_mem_want[d]);
					w_mem_pres[d] = w_mem_want[d] & ~w_rpl_pres[d];
					w_rvalid[d] = w_rpl_pres[d] | w_mem_pres[d];
					w_rpl_hs[d] = w_rpl_pres[d] & c_rready[d];
					w_mem_hs[d] = w_mem_pres[d] & c_rready[d];
				end
		end
	end
	wire w_mr_hs = |w_mem_hs | w_mr_drop;
	assign mem_rready = w_mr_drop | ((w_mr_fwd & w_mem_pres[w_mr_dir]) & c_rready[w_mr_dir]);
	reg [2 - 1:0] w_out_rlast;
	function automatic signed [BEAT_INDEX_WIDTH - 1:0] sv2v_cast_9FF7F_signed;
		input reg signed [BEAT_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_9FF7F_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_24
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				if (w_rpl_pres[d]) begin
					c_rid[((2 - 1) - d) * IW+:IW] = r_arid[r_rpl_slot[d]];
					c_rdata[((2 - 1) - d) * 32+:32] = (r_nodata[r_rpl_slot[d]] ? {32 * 1 {1'sb0}} : w_rpl_rdata[d]);
					c_rresp[((2 - 1) - d) * 2+:2] = 2'b00;
					w_out_rlast[d] = r_nodata[r_rpl_slot[d]] | (r_rpl_beat[d] == sv2v_cast_9FF7F_signed(FILL_BEATS - 1));
					c_ruser[((2 - 1) - d) * UW+:UW] = 1'sb0;
				end
				else begin
					c_rid[((2 - 1) - d) * IW+:IW] = r_arid[w_mr_slot];
					c_rdata[((2 - 1) - d) * 32+:32] = mem_rdata;
					c_rresp[((2 - 1) - d) * 2+:2] = mem_rresp;
					w_out_rlast[d] = mem_rlast;
					c_ruser[((2 - 1) - d) * UW+:UW] = mem_ruser;
				end
		end
	end
	assign c_rlast = w_out_rlast;
	assign c_rvalid = w_rvalid;
	localparam [1:0] W_IDLE = 2'd0;
	localparam [1:0] W_AW = 2'd1;
	localparam [1:0] W_W = 2'd2;
	localparam [1:0] W_B = 2'd3;
	reg [1:0] r_wstate;
	reg [WSEL_W - 1:0] r_w_sel;
	reg [SLOT_W - 1:0] r_w_slot;
	reg [WSEL_W - 1:0] r_w_rr;
	reg [BEAT_INDEX_WIDTH - 1:0] r_w_beat;
	reg [2 - 1:0] w_wb_blocked;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_25
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_wb_blocked[d] = 1'b0;
					begin : sv2v_autoblock_26
						reg signed [31:0] s;
						for (s = 0; s < 4; s = s + 1)
							if ((r_vld[s] && (r_line[s] == line_of(c_awaddr[((2 - 1) - d) * 8+:8]))) && (!w_gathered[s] || (r_pd[s] && !r_abs_done[s])))
								w_wb_blocked[d] = 1'b1;
					end
				end
		end
	end
	reg w_absc_vld;
	reg [SLOT_W - 1:0] w_absc_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		w_absc_vld = 1'b0;
		w_absc_slot = 1'sb0;
		begin : sv2v_autoblock_27
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if (((r_vld[s] && w_gathered[s]) && r_pd[s]) && !r_abs_issued[s]) begin
					w_absc_vld = 1'b1;
					w_absc_slot = sv2v_cast_7C1AF_signed(s);
				end
		end
	end
	reg [NW - 1:0] w_wcand;
	reg [WSEL_W - 1:0] w_wsel;
	function automatic signed [WSEL_W - 1:0] sv2v_cast_D6176_signed;
		input reg signed [WSEL_W - 1:0] inp;
		sv2v_cast_D6176_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_28
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				w_wcand[d] = c_awvalid[d] & ~w_wb_blocked[d];
		end
		w_wcand[2] = w_absc_vld;
		w_wsel = r_w_rr;
		begin : sv2v_autoblock_29
			reg signed [31:0] k;
			for (k = NW - 1; k >= 0; k = k - 1)
				begin : sv2v_autoblock_30
					reg signed [31:0] idx;
					idx = (sv2v_cast_32(r_w_rr) + k) % NW;
					if (w_wcand[idx])
						w_wsel = sv2v_cast_D6176_signed(idx);
				end
		end
	end
	wire w_wvalid = |w_wcand;
	wire w_cur_abs = r_w_sel == sv2v_cast_D6176_signed(2);
	function automatic [PORT_W - 1:0] sv2v_cast_65AE2;
		input reg [PORT_W - 1:0] inp;
		sv2v_cast_65AE2 = inp;
	endfunction
	wire [PORT_W - 1:0] w_cur_dir = sv2v_cast_65AE2(r_w_sel);
	wire [32 - 1:0] w_abs_rdata;
	assign w_abs_raddr = {r_w_slot, r_w_beat};
	assign w_abs_rdata = w_abs_rdata_a[r_dir[r_w_slot]];
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign mem_awid = (w_cur_abs ? sv2v_cast_83959(8'ha0 | sv2v_cast_8(r_dir[r_w_slot])) : c_awid[((2 - 1) - w_cur_dir) * IW+:IW]);
	assign mem_awaddr = (w_cur_abs ? {r_line[r_w_slot], sv2v_cast_2EB38_signed(0)} : c_awaddr[((2 - 1) - w_cur_dir) * 8+:8]);
	assign mem_awlen = (w_cur_abs ? sv2v_cast_8_signed(FILL_BEATS - 1) : c_awlen[((2 - 1) - w_cur_dir) * 8+:8]);
	assign mem_awsize = (w_cur_abs ? sv2v_cast_3_signed($clog2(STRB_W)) : c_awsize[((2 - 1) - w_cur_dir) * 3+:3]);
	assign mem_awburst = (w_cur_abs ? 2'b01 : c_awburst[((2 - 1) - w_cur_dir) * 2+:2]);
	assign mem_awlock = (w_cur_abs ? 1'b0 : c_awlock[w_cur_dir]);
	assign mem_awcache = (w_cur_abs ? 4'b0000 : c_awcache[((2 - 1) - w_cur_dir) * 4+:4]);
	assign mem_awprot = (w_cur_abs ? 3'b000 : c_awprot[((2 - 1) - w_cur_dir) * 3+:3]);
	assign mem_awqos = (w_cur_abs ? 4'b0000 : c_awqos[((2 - 1) - w_cur_dir) * 4+:4]);
	assign mem_awregion = (w_cur_abs ? 4'b0000 : c_awregion[((2 - 1) - w_cur_dir) * 4+:4]);
	assign mem_awuser = (w_cur_abs ? {UW {1'sb0}} : c_awuser[((2 - 1) - w_cur_dir) * UW+:UW]);
	assign mem_awvalid = (r_wstate == W_AW) && (w_cur_abs || c_awvalid[w_cur_dir]);
	wire w_wlast = (w_cur_abs ? r_w_beat == sv2v_cast_9FF7F_signed(FILL_BEATS - 1) : c_wlast[w_cur_dir]);
	assign mem_wdata = (w_cur_abs ? w_abs_rdata : c_wdata[((2 - 1) - w_cur_dir) * 32+:32]);
	assign mem_wstrb = (w_cur_abs ? {STRB_W {1'b1}} : c_wstrb[((2 - 1) - w_cur_dir) * STRB_W+:STRB_W]);
	assign mem_wlast = w_wlast;
	assign mem_wuser = 1'sb0;
	assign mem_wvalid = (r_wstate == W_W) && (w_cur_abs || c_wvalid[w_cur_dir]);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_31
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin : sv2v_autoblock_32
					reg mine;
					mine = !w_cur_abs && (w_cur_dir == sv2v_cast_65AE2_signed(d));
					c_awready[d] = ((r_wstate == W_AW) && mine) && mem_awready;
					c_wready[d] = ((r_wstate == W_W) && mine) && mem_wready;
					c_bvalid[d] = ((r_wstate == W_B) && mine) && mem_bvalid;
					c_bid[((2 - 1) - d) * IW+:IW] = mem_bid;
					c_bresp[((2 - 1) - d) * 2+:2] = mem_bresp;
					c_buser[((2 - 1) - d) * UW+:UW] = mem_buser;
				end
		end
	end
	assign mem_bready = (r_wstate == W_B) && (w_cur_abs || c_bready[w_cur_dir]);
	reg [4 - 1:0] w_rack_hit;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_33
			reg signed [31:0] s;
			for (s = 0; s < 4; s = s + 1)
				w_rack_hit[s] = (((r_vld[s] & r_ar_taken[s]) & ~r_rack[s]) & c_coh_done_valid[r_dir[s]]) & (c_coh_done_id[((2 - 1) - r_dir[s]) * IW+:IW] == r_arid[s]);
		end
	end
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_DT = 0;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_PD = 2;
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	function automatic [SNQ_W - 1:0] sv2v_cast_36294;
		input reg [SNQ_W - 1:0] inp;
		sv2v_cast_36294 = inp;
	endfunction
	function automatic [SLOT_W - 1:0] sv2v_cast_7C1AF;
		input reg [SLOT_W - 1:0] inp;
		sv2v_cast_7C1AF = inp;
	endfunction
	function automatic [SNI_W - 1:0] sv2v_cast_F4A8C;
		input reg [SNI_W - 1:0] inp;
		sv2v_cast_F4A8C = inp;
	endfunction
	function automatic [SNI_IW - 1:0] sv2v_cast_C8806;
		input reg [SNI_IW - 1:0] inp;
		sv2v_cast_C8806 = inp;
	endfunction
	function automatic [WSEL_W - 1:0] sv2v_cast_D6176;
		input reg [WSEL_W - 1:0] inp;
		sv2v_cast_D6176 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_vld <= 1'sb0;
			r_nodata <= 1'sb0;
			r_ar_taken <= 1'sb0;
			r_dt <= 1'sb0;
			r_pd <= 1'sb0;
			r_mem_issued <= 1'sb0;
			r_mem_done <= 1'sb0;
			r_rpl_done <= 1'sb0;
			r_abs_issued <= 1'sb0;
			r_abs_done <= 1'sb0;
			r_rack <= 1'sb0;
			r_rr <= 1'sb0;
			r_pend_ovf <= 1'sb0;
			r_arw_vld <= 1'sb0;
			r_mar_vld <= 1'b0;
			r_mar_slot <= 1'sb0;
			r_rpl_vld <= 1'sb0;
			r_rpl_hold <= 1'sb0;
			r_wstate <= W_IDLE;
			r_w_sel <= 1'sb0;
			r_w_slot <= 1'sb0;
			r_w_rr <= 1'sb0;
			r_w_beat <= 1'sb0;
			begin : sv2v_autoblock_34
				reg signed [31:0] s;
				for (s = 0; s < 4; s = s + 1)
					begin
						r_dir[s] <= 1'sb0;
						r_ac_left[s] <= 1'sb0;
						r_cr_left[s] <= 1'sb0;
					end
			end
			begin : sv2v_autoblock_35
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					begin
						r_pend_cnt[d] <= 1'sb0;
						r_arw_slot[d] <= 1'sb0;
						r_snq_cnt[d] <= 1'sb0;
						r_sni_cnt[d] <= 1'sb0;
						r_cd_beat[d] <= 1'sb0;
						r_cd_rr[d] <= 1'sb0;
						r_rpl_slot[d] <= 1'sb0;
						r_rpl_beat[d] <= 1'sb0;
					end
			end
		end
		else begin
			begin : sv2v_autoblock_36
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					begin : sv2v_autoblock_37
						reg push;
						reg pop;
						push = coh_req_vld[d] & ~((w_grant & (w_grant_dir == sv2v_cast_65AE2_signed(d))) & w_cand_live[d]);
						pop = (w_grant & (w_grant_dir == sv2v_cast_65AE2_signed(d))) & ~w_cand_live[d];
						if (pop) begin
							begin : sv2v_autoblock_38
								reg signed [31:0] k;
								for (k = 0; k < 3; k = k + 1)
									begin
										r_pend_addr[d][k] <= r_pend_addr[d][k + 1];
										r_pend_type[d][k] <= r_pend_type[d][k + 1];
									end
							end
							if (push) begin
								r_pend_addr[d][sv2v_cast_2(r_pend_cnt[d]) - 2'd1] <= c_coh_req_addr[((2 - 1) - d) * 8+:8];
								r_pend_type[d][sv2v_cast_2(r_pend_cnt[d]) - 2'd1] <= c_coh_req_type[((2 - 1) - d) * 3+:3];
							end
							else
								r_pend_cnt[d] <= r_pend_cnt[d] - 3'sd1;
						end
						else if (push) begin
							if (r_pend_cnt[d] < sv2v_cast_3_signed(PEND_DEPTH)) begin
								r_pend_addr[d][sv2v_cast_2(r_pend_cnt[d])] <= c_coh_req_addr[((2 - 1) - d) * 8+:8];
								r_pend_type[d][sv2v_cast_2(r_pend_cnt[d])] <= c_coh_req_type[((2 - 1) - d) * 3+:3];
								r_pend_cnt[d] <= r_pend_cnt[d] + 3'sd1;
							end
							else
								r_pend_ovf[d] <= 1'b1;
						end
					end
			end
			if (w_grant) begin
				r_vld[w_slot_idx] <= 1'b1;
				r_dir[w_slot_idx] <= w_grant_dir;
				r_line[w_slot_idx] <= line_of(w_cand_addr[w_grant_dir]);
				r_type[w_slot_idx] <= w_cand_type[w_grant_dir];
				r_nodata[w_slot_idx] <= is_nodata(w_cand_type[w_grant_dir]);
				r_ar_taken[w_slot_idx] <= 1'b0;
				r_ac_left[w_slot_idx] <= sv2v_cast_65AE2_signed(NPEER);
				r_cr_left[w_slot_idx] <= sv2v_cast_65AE2_signed(NPEER);
				r_dt[w_slot_idx] <= 1'b0;
				r_pd[w_slot_idx] <= 1'b0;
				r_mem_issued[w_slot_idx] <= 1'b0;
				r_mem_done[w_slot_idx] <= 1'b0;
				r_rpl_done[w_slot_idx] <= 1'b0;
				r_abs_issued[w_slot_idx] <= 1'b0;
				r_abs_done[w_slot_idx] <= 1'b0;
				r_rack[w_slot_idx] <= 1'b0;
				r_arw_vld[w_grant_dir] <= 1'b1;
				r_arw_slot[w_grant_dir] <= w_slot_idx;
				r_rr <= sv2v_cast_65AE2((sv2v_cast_32(w_grant_dir) + 1) % 2);
			end
			begin : sv2v_autoblock_39
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					if (w_ar_take[d]) begin
						r_ar_taken[r_arw_slot[d]] <= 1'b1;
						r_arid[r_arw_slot[d]] <= c_arid[((2 - 1) - d) * IW+:IW];
						r_arcache[r_arw_slot[d]] <= c_arcache[((2 - 1) - d) * 4+:4];
						r_arprot[r_arw_slot[d]] <= c_arprot[((2 - 1) - d) * 3+:3];
						r_aruser[r_arw_slot[d]] <= c_aruser[((2 - 1) - d) * UW+:UW];
						r_arw_vld[d] <= 1'b0;
					end
			end
			begin : sv2v_autoblock_40
				reg signed [31:0] p;
				for (p = 0; p < 2; p = p + 1)
					begin : sv2v_autoblock_41
						reg push_q;
						push_q = w_grant & (w_grant_dir != sv2v_cast_65AE2_signed(p));
						if (w_ac_hs[p]) begin
							begin : sv2v_autoblock_42
								reg signed [31:0] k;
								for (k = 0; k < (4 - 1); k = k + 1)
									r_snq[p][k] <= r_snq[p][k + 1];
							end
							r_ac_left[w_ac_slot[p]] <= r_ac_left[w_ac_slot[p]] - sv2v_cast_65AE2_signed(1);
						end
						if (push_q)
							r_snq[p][sv2v_cast_7C1AF(r_snq_cnt[p] - sv2v_cast_36294(w_ac_hs[p]))] <= w_slot_idx;
						r_snq_cnt[p] <= (r_snq_cnt[p] + sv2v_cast_36294(push_q)) - sv2v_cast_36294(w_ac_hs[p]);
						if (w_cr_hs[p]) begin
							begin : sv2v_autoblock_43
								reg signed [31:0] k;
								for (k = 0; k < (2 - 1); k = k + 1)
									r_sni[p][k] <= r_sni[p][k + 1];
							end
							r_cr_left[w_sni_head[p]] <= r_cr_left[w_sni_head[p]] - sv2v_cast_65AE2_signed(1);
							if (s_crresp[(((2 - 1) - p) * l1_pkg_AMBER_CRRESP_WIDTH) + l1_pkg_AMBER_CRRESP_DT]) begin
								r_dt[w_sni_head[p]] <= 1'b1;
								r_pd[w_sni_head[p]] <= s_crresp[(((2 - 1) - p) * l1_pkg_AMBER_CRRESP_WIDTH) + l1_pkg_AMBER_CRRESP_PD];
								if (!r_mem_issued[w_sni_head[p]] && !(w_mar_vld && (w_mar_slot == w_sni_head[p])))
									r_mem_done[w_sni_head[p]] <= 1'b1;
							end
							r_cd_beat[p] <= 1'sb0;
						end
						if (w_ac_hs[p])
							r_sni[p][sv2v_cast_C8806(r_sni_cnt[p] - sv2v_cast_F4A8C(w_cr_hs[p]))] <= w_ac_slot[p];
						r_sni_cnt[p] <= (r_sni_cnt[p] + sv2v_cast_F4A8C(w_ac_hs[p])) - sv2v_cast_F4A8C(w_cr_hs[p]);
						if (w_cd_hs[p])
							r_cd_beat[p] <= (s_cdlast[p] ? {BEAT_INDEX_WIDTH {1'sb0}} : r_cd_beat[p] + sv2v_cast_9FF7F_signed(1));
					end
			end
			begin : sv2v_autoblock_44
				reg signed [31:0] a;
				for (a = 0; a < 2; a = a + 1)
					if (w_buf_we[a])
						r_cd_rr[a] <= sv2v_cast_65AE2((sv2v_cast_32(w_buf_src[a]) + 1) % 2);
			end
			if (w_mar_hs) begin
				r_mem_issued[w_mar_slot] <= 1'b1;
				r_mar_vld <= 1'b0;
			end
			else if (w_mar_vld) begin
				r_mar_vld <= 1'b1;
				r_mar_slot <= w_mar_slot;
			end
			if (w_mr_hs && mem_rlast)
				r_mem_done[w_mr_slot] <= 1'b1;
			begin : sv2v_autoblock_45
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					if (r_rpl_vld[d]) begin
						if (w_rpl_hs[d]) begin
							r_rpl_hold[d] <= 1'b0;
							if (w_out_rlast[d]) begin
								r_rpl_vld[d] <= 1'b0;
								r_rpl_done[r_rpl_slot[d]] <= 1'b1;
							end
							else
								r_rpl_beat[d] <= r_rpl_beat[d] + sv2v_cast_9FF7F_signed(1);
						end
						else if (w_rpl_pres[d])
							r_rpl_hold[d] <= 1'b1;
					end
					else if (w_rplc_vld[d]) begin
						r_rpl_vld[d] <= 1'b1;
						r_rpl_slot[d] <= w_rplc_slot[d];
						r_rpl_beat[d] <= 1'sb0;
						r_rpl_hold[d] <= 1'b0;
					end
			end
			(* full_case, parallel_case *)
			case (r_wstate)
				W_IDLE:
					if (w_wvalid) begin
						r_w_sel <= w_wsel;
						r_w_slot <= w_absc_slot;
						r_w_rr <= sv2v_cast_D6176((sv2v_cast_32(w_wsel) + 1) % NW);
						r_w_beat <= 1'sb0;
						r_wstate <= W_AW;
						if (w_wsel == sv2v_cast_D6176_signed(2))
							r_abs_issued[w_absc_slot] <= 1'b1;
					end
				W_AW:
					if (mem_awvalid && mem_awready)
						r_wstate <= W_W;
				W_W:
					if (mem_wvalid && mem_wready) begin
						if (w_wlast)
							r_wstate <= W_B;
						else
							r_w_beat <= r_w_beat + sv2v_cast_9FF7F_signed(1);
					end
				W_B:
					if (mem_bvalid && mem_bready) begin
						r_wstate <= W_IDLE;
						if (w_cur_abs)
							r_abs_done[r_w_slot] <= 1'b1;
					end
				default: r_wstate <= W_IDLE;
			endcase
			begin : sv2v_autoblock_46
				reg signed [31:0] s;
				for (s = 0; s < 4; s = s + 1)
					begin
						if (w_rack_hit[s])
							r_rack[s] <= 1'b1;
						if (w_free_now[s])
							r_vld[s] <= 1'b0;
					end
			end
		end
	assign dbg_busy = |r_vld;
	assign dbg_slot_vld = r_vld;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_47
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				dbg_pend_vld[d] = r_pend_cnt[d] != {3 {1'sb0}};
		end
	end
	assign dbg_abs_pend = |((r_vld & r_pd) & ~r_abs_done);
	assign dbg_grant = w_grant;
	assign dbg_grant_dir = w_grant_dir;
	assign dbg_grant_addr = w_cand_addr[w_grant_dir];
	assign dbg_grant_slot = w_slot_idx;
	reg unused_ar;
	always @(*) begin
		if (_sv2v_0)
			;
		unused_ar = 1'b0;
		begin : sv2v_autoblock_48
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				unused_ar = unused_ar ^ ^{c_arlen[((2 - 1) - d) * 8+:8], c_arsize[((2 - 1) - d) * 3+:3], c_arburst[((2 - 1) - d) * 2+:2], c_arlock[d], c_arqos[((2 - 1) - d) * 4+:4], c_arregion[((2 - 1) - d) * 4+:4], c_wuser[((2 - 1) - d) * UW+:UW]};
		end
		unused_ar = unused_ar ^ ^mem_rid[IW - 1:SLOT_W];
	end
	initial _sv2v_0 = 0;
endmodule
