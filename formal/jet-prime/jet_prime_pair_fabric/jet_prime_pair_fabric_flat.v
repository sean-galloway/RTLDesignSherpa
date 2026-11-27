module jet_prime_pair_fabric (
	clk,
	rst_n,
	c0_arid,
	c0_araddr,
	c0_arlen,
	c0_arsize,
	c0_arburst,
	c0_arlock,
	c0_arcache,
	c0_arprot,
	c0_arqos,
	c0_arregion,
	c0_aruser,
	c0_arvalid,
	c0_arready,
	c0_rid,
	c0_rdata,
	c0_rresp,
	c0_rlast,
	c0_ruser,
	c0_rvalid,
	c0_rready,
	c0_awid,
	c0_awaddr,
	c0_awlen,
	c0_awsize,
	c0_awburst,
	c0_awlock,
	c0_awcache,
	c0_awprot,
	c0_awqos,
	c0_awregion,
	c0_awuser,
	c0_awvalid,
	c0_awready,
	c0_wdata,
	c0_wstrb,
	c0_wlast,
	c0_wuser,
	c0_wvalid,
	c0_wready,
	c0_bid,
	c0_bresp,
	c0_buser,
	c0_bvalid,
	c0_bready,
	c1_arid,
	c1_araddr,
	c1_arlen,
	c1_arsize,
	c1_arburst,
	c1_arlock,
	c1_arcache,
	c1_arprot,
	c1_arqos,
	c1_arregion,
	c1_aruser,
	c1_arvalid,
	c1_arready,
	c1_rid,
	c1_rdata,
	c1_rresp,
	c1_rlast,
	c1_ruser,
	c1_rvalid,
	c1_rready,
	c1_awid,
	c1_awaddr,
	c1_awlen,
	c1_awsize,
	c1_awburst,
	c1_awlock,
	c1_awcache,
	c1_awprot,
	c1_awqos,
	c1_awregion,
	c1_awuser,
	c1_awvalid,
	c1_awready,
	c1_wdata,
	c1_wstrb,
	c1_wlast,
	c1_wuser,
	c1_wvalid,
	c1_wready,
	c1_bid,
	c1_bresp,
	c1_buser,
	c1_bvalid,
	c1_bready,
	s0_acaddr,
	s0_acsnoop,
	s0_acprot,
	s0_acvalid,
	s0_acready,
	s0_crresp,
	s0_crvalid,
	s0_crready,
	s0_cddata,
	s0_cdlast,
	s0_cdvalid,
	s0_cdready,
	s1_acaddr,
	s1_acsnoop,
	s1_acprot,
	s1_acvalid,
	s1_acready,
	s1_crresp,
	s1_crvalid,
	s1_crready,
	s1_cddata,
	s1_cdlast,
	s1_cdvalid,
	s1_cdready,
	c0_coh_req_valid,
	c0_coh_req_addr,
	c0_coh_req_type,
	c1_coh_req_valid,
	c1_coh_req_addr,
	c1_coh_req_type,
	c0_coh_done_valid,
	c0_coh_done_id,
	c1_coh_done_valid,
	c1_coh_done_id,
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
	localparam signed [31:0] l1_pkg_AMBER_SETS = 128;
	localparam signed [31:0] l1_pkg_AMBER_WAYS = 4;
	localparam signed [31:0] l1_pkg_AMBER_LINE_BYTES = 64;
	localparam signed [31:0] l1_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] STRB_W = 32 / 8;
	localparam signed [31:0] FILL_BEATS = 16 / STRB_W;
	localparam signed [31:0] BEAT_INDEX_WIDTH = $clog2(FILL_BEATS);
	localparam signed [31:0] IW = 3;
	localparam signed [31:0] UW = 1;
	localparam signed [31:0] SLOT_W = (4 > 1 ? $clog2(4) : 1);
	localparam signed [31:0] OFFSET_W = $clog2(16);
	localparam signed [31:0] LINE_W = 8 - OFFSET_W;
	input wire clk;
	input wire rst_n;
	input wire [IW - 1:0] c0_arid;
	input wire [8 - 1:0] c0_araddr;
	input wire [7:0] c0_arlen;
	input wire [2:0] c0_arsize;
	input wire [1:0] c0_arburst;
	input wire c0_arlock;
	input wire [3:0] c0_arcache;
	input wire [2:0] c0_arprot;
	input wire [3:0] c0_arqos;
	input wire [3:0] c0_arregion;
	input wire [UW - 1:0] c0_aruser;
	input wire c0_arvalid;
	output wire c0_arready;
	output wire [IW - 1:0] c0_rid;
	output wire [32 - 1:0] c0_rdata;
	output wire [1:0] c0_rresp;
	output wire c0_rlast;
	output wire [UW - 1:0] c0_ruser;
	output wire c0_rvalid;
	input wire c0_rready;
	input wire [IW - 1:0] c0_awid;
	input wire [8 - 1:0] c0_awaddr;
	input wire [7:0] c0_awlen;
	input wire [2:0] c0_awsize;
	input wire [1:0] c0_awburst;
	input wire c0_awlock;
	input wire [3:0] c0_awcache;
	input wire [2:0] c0_awprot;
	input wire [3:0] c0_awqos;
	input wire [3:0] c0_awregion;
	input wire [UW - 1:0] c0_awuser;
	input wire c0_awvalid;
	output wire c0_awready;
	input wire [32 - 1:0] c0_wdata;
	input wire [STRB_W - 1:0] c0_wstrb;
	input wire c0_wlast;
	input wire [UW - 1:0] c0_wuser;
	input wire c0_wvalid;
	output wire c0_wready;
	output wire [IW - 1:0] c0_bid;
	output wire [1:0] c0_bresp;
	output wire [UW - 1:0] c0_buser;
	output wire c0_bvalid;
	input wire c0_bready;
	input wire [IW - 1:0] c1_arid;
	input wire [8 - 1:0] c1_araddr;
	input wire [7:0] c1_arlen;
	input wire [2:0] c1_arsize;
	input wire [1:0] c1_arburst;
	input wire c1_arlock;
	input wire [3:0] c1_arcache;
	input wire [2:0] c1_arprot;
	input wire [3:0] c1_arqos;
	input wire [3:0] c1_arregion;
	input wire [UW - 1:0] c1_aruser;
	input wire c1_arvalid;
	output wire c1_arready;
	output wire [IW - 1:0] c1_rid;
	output wire [32 - 1:0] c1_rdata;
	output wire [1:0] c1_rresp;
	output wire c1_rlast;
	output wire [UW - 1:0] c1_ruser;
	output wire c1_rvalid;
	input wire c1_rready;
	input wire [IW - 1:0] c1_awid;
	input wire [8 - 1:0] c1_awaddr;
	input wire [7:0] c1_awlen;
	input wire [2:0] c1_awsize;
	input wire [1:0] c1_awburst;
	input wire c1_awlock;
	input wire [3:0] c1_awcache;
	input wire [2:0] c1_awprot;
	input wire [3:0] c1_awqos;
	input wire [3:0] c1_awregion;
	input wire [UW - 1:0] c1_awuser;
	input wire c1_awvalid;
	output wire c1_awready;
	input wire [32 - 1:0] c1_wdata;
	input wire [STRB_W - 1:0] c1_wstrb;
	input wire c1_wlast;
	input wire [UW - 1:0] c1_wuser;
	input wire c1_wvalid;
	output wire c1_wready;
	output wire [IW - 1:0] c1_bid;
	output wire [1:0] c1_bresp;
	output wire [UW - 1:0] c1_buser;
	output wire c1_bvalid;
	input wire c1_bready;
	output wire [8 - 1:0] s0_acaddr;
	output wire [3:0] s0_acsnoop;
	output wire [2:0] s0_acprot;
	output wire s0_acvalid;
	input wire s0_acready;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_WIDTH = 5;
	input wire [4:0] s0_crresp;
	input wire s0_crvalid;
	output wire s0_crready;
	input wire [32 - 1:0] s0_cddata;
	input wire s0_cdlast;
	input wire s0_cdvalid;
	output wire s0_cdready;
	output wire [8 - 1:0] s1_acaddr;
	output wire [3:0] s1_acsnoop;
	output wire [2:0] s1_acprot;
	output wire s1_acvalid;
	input wire s1_acready;
	input wire [4:0] s1_crresp;
	input wire s1_crvalid;
	output wire s1_crready;
	input wire [32 - 1:0] s1_cddata;
	input wire s1_cdlast;
	input wire s1_cdvalid;
	output wire s1_cdready;
	input wire c0_coh_req_valid;
	input wire [8 - 1:0] c0_coh_req_addr;
	input wire [2:0] c0_coh_req_type;
	input wire c1_coh_req_valid;
	input wire [8 - 1:0] c1_coh_req_addr;
	input wire [2:0] c1_coh_req_type;
	input wire c0_coh_done_valid;
	input wire [IW - 1:0] c0_coh_done_id;
	input wire c1_coh_done_valid;
	input wire [IW - 1:0] c1_coh_done_id;
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
	output wire [1:0] dbg_pend_vld;
	output wire dbg_abs_pend;
	output wire dbg_grant;
	output wire dbg_grant_dir;
	output wire [8 - 1:0] dbg_grant_addr;
	output wire [SLOT_W - 1:0] dbg_grant_slot;
	initial begin
		if ((16 & (16 - 1)) != 0)
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:388:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 16 must be a power of two");
		if (((FILL_BEATS & (FILL_BEATS - 1)) != 0) || (FILL_BEATS < 2))
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:390:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 16 / 32*8 must be a power of two >= 2");
		if ((32 % 8) != 0)
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:392:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 32 must be a multiple of 8");
		if ((4 < 2) || ((1 << SLOT_W) < 4))
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:394:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 4 must be >= 2");
		if ((1 << IW) < 4)
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:396:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 2**3 must cover 4 (the memory read IDs)");
		if (2 < 1)
			$display("Error [%0t] .flat_build/prep/jet_prime_pair_fabric.sv:398:13 - jet_prime_pair_fabric.<unnamed_block>.<unnamed_block>\n msg: ", $time, "jet_prime_pair_fabric: 2 must be >= 1");
	end
	localparam [3:0] ACSNOOP_READ_SHARED = 4'h1;
	localparam [3:0] ACSNOOP_READ_UNIQUE = 4'h7;
	localparam [3:0] ACSNOOP_CLEAN_INVALID = 4'h9;
	localparam [3:0] ACSNOOP_MAKE_INVALID = 4'hc;
	function automatic [3:0] map_snoop;
		input reg [2:0] req_type;
		case (req_type)
			3'b000, 3'b110: map_snoop = ACSNOOP_READ_SHARED;
			3'b001: map_snoop = ACSNOOP_READ_UNIQUE;
			3'b010: map_snoop = ACSNOOP_CLEAN_INVALID;
			default: map_snoop = ACSNOOP_MAKE_INVALID;
		endcase
	endfunction
	function automatic is_nodata;
		input reg [2:0] req_type;
		is_nodata = (req_type == 3'b010) || (req_type == 3'b011);
	endfunction
	function automatic [LINE_W - 1:0] line_of;
		input reg [8 - 1:0] addr;
		line_of = addr[8 - 1-:LINE_W];
	endfunction
	localparam signed [31:0] SNQ_W = SLOT_W + 1;
	localparam signed [31:0] SNI_W = $clog2(2 + 1);
	localparam signed [31:0] SNI_IW = (2 > 1 ? $clog2(2) : 1);
	localparam signed [31:0] PEND_DEPTH = 4;
	localparam signed [31:0] BUF_AW = SLOT_W + BEAT_INDEX_WIDTH;
	wire [1:0] c_arvalid;
	wire [1:0] c_arready;
	wire [1:0] c_rready;
	wire [IW - 1:0] c_arid [0:1];
	wire [8 - 1:0] c_araddr [0:1];
	wire [7:0] c_arlen [0:1];
	wire [3:0] c_arcache [0:1];
	wire [2:0] c_arprot [0:1];
	wire [UW - 1:0] c_aruser [0:1];
	assign c_arvalid = {c1_arvalid, c0_arvalid};
	assign c_rready = {c1_rready, c0_rready};
	assign c_arid[0] = c0_arid;
	assign c_arid[1] = c1_arid;
	assign c_araddr[0] = c0_araddr;
	assign c_araddr[1] = c1_araddr;
	assign c_arlen[0] = c0_arlen;
	assign c_arlen[1] = c1_arlen;
	assign c_arcache[0] = c0_arcache;
	assign c_arcache[1] = c1_arcache;
	assign c_arprot[0] = c0_arprot;
	assign c_arprot[1] = c1_arprot;
	assign c_aruser[0] = c0_aruser;
	assign c_aruser[1] = c1_aruser;
	wire [1:0] c_awvalid;
	wire [1:0] c_wvalid;
	wire [1:0] c_bready;
	wire [IW - 1:0] c_awid [0:1];
	wire [8 - 1:0] c_awaddr [0:1];
	wire [7:0] c_awlen [0:1];
	wire [2:0] c_awsize [0:1];
	wire [1:0] c_awburst [0:1];
	wire c_awlock [0:1];
	wire [3:0] c_awcache [0:1];
	wire [2:0] c_awprot [0:1];
	wire [3:0] c_awqos [0:1];
	wire [3:0] c_awregion [0:1];
	wire [UW - 1:0] c_awuser [0:1];
	wire [32 - 1:0] c_wdata [0:1];
	wire [STRB_W - 1:0] c_wstrb [0:1];
	wire c_wlast [0:1];
	assign c_awvalid = {c1_awvalid, c0_awvalid};
	assign c_wvalid = {c1_wvalid, c0_wvalid};
	assign c_bready = {c1_bready, c0_bready};
	assign c_awid[0] = c0_awid;
	assign c_awid[1] = c1_awid;
	assign c_awaddr[0] = c0_awaddr;
	assign c_awaddr[1] = c1_awaddr;
	assign c_awlen[0] = c0_awlen;
	assign c_awlen[1] = c1_awlen;
	assign c_awsize[0] = c0_awsize;
	assign c_awsize[1] = c1_awsize;
	assign c_awburst[0] = c0_awburst;
	assign c_awburst[1] = c1_awburst;
	assign c_awlock[0] = c0_awlock;
	assign c_awlock[1] = c1_awlock;
	assign c_awcache[0] = c0_awcache;
	assign c_awcache[1] = c1_awcache;
	assign c_awprot[0] = c0_awprot;
	assign c_awprot[1] = c1_awprot;
	assign c_awqos[0] = c0_awqos;
	assign c_awqos[1] = c1_awqos;
	assign c_awregion[0] = c0_awregion;
	assign c_awregion[1] = c1_awregion;
	assign c_awuser[0] = c0_awuser;
	assign c_awuser[1] = c1_awuser;
	assign c_wdata[0] = c0_wdata;
	assign c_wdata[1] = c1_wdata;
	assign c_wstrb[0] = c0_wstrb;
	assign c_wstrb[1] = c1_wstrb;
	assign c_wlast[0] = c0_wlast;
	assign c_wlast[1] = c1_wlast;
	wire [1:0] acready;
	wire [1:0] crvalid;
	wire [1:0] cdvalid;
	wire [1:0] cdlast;
	wire [4:0] crresp_w [0:1];
	wire [32 - 1:0] cddata_w [0:1];
	assign acready = {s1_acready, s0_acready};
	assign crvalid = {s1_crvalid, s0_crvalid};
	assign cdvalid = {s1_cdvalid, s0_cdvalid};
	assign cdlast = {s1_cdlast, s0_cdlast};
	assign crresp_w[0] = s0_crresp;
	assign crresp_w[1] = s1_crresp;
	assign cddata_w[0] = s0_cddata;
	assign cddata_w[1] = s1_cddata;
	wire [1:0] coh_req_vld;
	wire [8 - 1:0] coh_req_addr [0:1];
	wire [2:0] coh_req_type [0:1];
	assign coh_req_vld[0] = c0_coh_req_valid && (c0_coh_req_type != 3'b100);
	assign coh_req_vld[1] = c1_coh_req_valid && (c1_coh_req_type != 3'b100);
	assign coh_req_addr[0] = c0_coh_req_addr;
	assign coh_req_addr[1] = c1_coh_req_addr;
	assign coh_req_type[0] = c0_coh_req_type;
	assign coh_req_type[1] = c1_coh_req_type;
	wire [1:0] coh_done_vld;
	wire [IW - 1:0] coh_done_id [0:1];
	assign coh_done_vld = {c1_coh_done_valid, c0_coh_done_valid};
	assign coh_done_id[0] = c0_coh_done_id;
	assign coh_done_id[1] = c1_coh_done_id;
	reg [4 - 1:0] r_vld;
	reg [4 - 1:0] r_dir;
	reg [LINE_W - 1:0] r_line [0:4 - 1];
	reg [2:0] r_type [0:4 - 1];
	reg [4 - 1:0] r_nodata;
	reg [4 - 1:0] r_ar_taken;
	reg [IW - 1:0] r_arid [0:4 - 1];
	reg [3:0] r_arcache [0:4 - 1];
	reg [2:0] r_arprot [0:4 - 1];
	reg [UW - 1:0] r_aruser [0:4 - 1];
	reg [4 - 1:0] r_ac_done;
	reg [4 - 1:0] r_cr_done;
	reg [4 - 1:0] r_dt;
	reg [4 - 1:0] r_pd;
	reg [4 - 1:0] r_mem_issued;
	reg [4 - 1:0] r_mem_done;
	reg [4 - 1:0] r_rpl_done;
	reg [4 - 1:0] r_abs_issued;
	reg [4 - 1:0] r_abs_done;
	reg [4 - 1:0] r_rack;
	reg [4 - 1:0] w_delivered;
	reg [4 - 1:0] w_free_now;
	wire w_mar_vld;
	wire [SLOT_W - 1:0] w_mar_slot;
	function automatic signed [SLOT_W - 1:0] sv2v_cast_7C1AF_signed;
		input reg signed [SLOT_W - 1:0] inp;
		sv2v_cast_7C1AF_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] s;
			for (s = 0; s < 4; s = s + 1)
				begin
					w_delivered[s] = (r_dt[s] | r_nodata[s] ? r_rpl_done[s] : r_mem_done[s]);
					w_free_now[s] = (((((r_vld[s] & r_cr_done[s]) & w_delivered[s]) & (~r_mem_issued[s] | r_mem_done[s])) & ~(w_mar_vld & (w_mar_slot == sv2v_cast_7C1AF_signed(s)))) & (~r_pd[s] | r_abs_done[s])) & r_rack[s];
				end
		end
	end
	reg [2:0] r_pend_cnt [0:1];
	reg [8 - 1:0] r_pend_addr [0:1][0:3];
	reg [2:0] r_pend_type [0:1][0:3];
	reg [1:0] r_pend_ovf;
	reg [1:0] w_cand_vld;
	reg [8 - 1:0] w_cand_addr [0:1];
	reg [2:0] w_cand_type [0:1];
	reg [1:0] w_cand_live;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				if (r_pend_cnt[d] != 3'd0) begin
					w_cand_vld[d] = 1'b1;
					w_cand_live[d] = 1'b0;
					w_cand_addr[d] = r_pend_addr[d][0];
					w_cand_type[d] = r_pend_type[d][0];
				end
				else begin
					w_cand_vld[d] = coh_req_vld[d];
					w_cand_live[d] = 1'b1;
					w_cand_addr[d] = coh_req_addr[d];
					w_cand_type[d] = coh_req_type[d];
				end
		end
	end
	reg [1:0] w_cand_locked;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_cand_locked[d] = 1'b0;
					begin : sv2v_autoblock_4
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
		begin : sv2v_autoblock_5
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if (!r_vld[s]) begin
					w_slot_free = 1'b1;
					w_slot_idx = sv2v_cast_7C1AF_signed(s);
				end
		end
	end
	reg [1:0] r_arw_vld;
	reg [SLOT_W - 1:0] r_arw_slot [0:1];
	reg [1:0] w_cand_ok;
	reg r_rr;
	reg w_grant;
	reg w_grant_dir;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_6
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				w_cand_ok[d] = ((w_cand_vld[d] & ~w_cand_locked[d]) & w_slot_free) & ~r_arw_vld[d];
		end
		if (w_cand_ok[r_rr])
			w_grant_dir = r_rr;
		else
			w_grant_dir = ~r_rr;
		w_grant = w_cand_ok[0] | w_cand_ok[1];
	end
	assign c_arready[0] = r_arw_vld[0];
	assign c_arready[1] = r_arw_vld[1];
	assign c0_arready = c_arready[0];
	assign c1_arready = c_arready[1];
	wire [1:0] w_ar_take = c_arvalid & c_arready;
	reg [SLOT_W - 1:0] r_snq [0:1][0:4 - 1];
	reg [SNQ_W - 1:0] r_snq_cnt [0:1];
	reg [SLOT_W - 1:0] r_sni [0:1][0:2 - 1];
	reg [SNI_W - 1:0] r_sni_cnt [0:1];
	reg [BEAT_INDEX_WIDTH - 1:0] r_cd_beat [0:1];
	reg [1:0] w_ac_vld;
	reg [1:0] w_ac_hs;
	reg [1:0] w_cr_hs;
	reg [1:0] w_cd_hs;
	reg [SLOT_W - 1:0] w_ac_slot [0:1];
	reg [SLOT_W - 1:0] w_sni_head [0:1];
	function automatic signed [SNI_W - 1:0] sv2v_cast_F4A8C_signed;
		input reg signed [SNI_W - 1:0] inp;
		sv2v_cast_F4A8C_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] p;
			for (p = 0; p < 2; p = p + 1)
				begin
					w_ac_slot[p] = r_snq[p][0];
					w_ac_vld[p] = (r_snq_cnt[p] != {SNQ_W {1'sb0}}) && (r_sni_cnt[p] < sv2v_cast_F4A8C_signed(2));
					w_ac_hs[p] = w_ac_vld[p] & acready[p];
					w_sni_head[p] = r_sni[p][0];
					w_cr_hs[p] = crvalid[p] & (r_sni_cnt[p] != {SNI_W {1'sb0}});
					w_cd_hs[p] = cdvalid[p] & (r_sni_cnt[p] != {SNI_W {1'sb0}});
				end
		end
	end
	function automatic signed [OFFSET_W - 1:0] sv2v_cast_2EB38_signed;
		input reg signed [OFFSET_W - 1:0] inp;
		sv2v_cast_2EB38_signed = inp;
	endfunction
	assign s0_acaddr = {r_line[w_ac_slot[0]], sv2v_cast_2EB38_signed(0)};
	assign s1_acaddr = {r_line[w_ac_slot[1]], sv2v_cast_2EB38_signed(0)};
	assign s0_acsnoop = map_snoop(r_type[w_ac_slot[0]]);
	assign s1_acsnoop = map_snoop(r_type[w_ac_slot[1]]);
	assign s0_acprot = 3'b000;
	assign s1_acprot = 3'b000;
	assign s0_acvalid = w_ac_vld[0];
	assign s1_acvalid = w_ac_vld[1];
	assign s0_crready = r_sni_cnt[0] != {SNI_W {1'sb0}};
	assign s1_crready = r_sni_cnt[1] != {SNI_W {1'sb0}};
	assign s0_cdready = r_sni_cnt[0] != {SNI_W {1'sb0}};
	assign s1_cdready = r_sni_cnt[1] != {SNI_W {1'sb0}};
	wire w_wfly_vld;
	reg [LINE_W - 1:0] r_wfly_line;
	reg w_marc_vld;
	reg [SLOT_W - 1:0] w_marc_slot;
	reg r_mar_vld;
	reg [SLOT_W - 1:0] r_mar_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		w_marc_vld = 1'b0;
		w_marc_slot = 1'sb0;
		begin : sv2v_autoblock_8
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if ((((((r_vld[s] && r_ar_taken[s]) && !r_nodata[s]) && !r_mem_issued[s]) && r_ac_done[s]) && !(r_cr_done[s] && r_dt[s])) && !(w_wfly_vld && (r_wfly_line == r_line[s]))) begin
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
	wire w_mr_fwd = (mem_rvalid & r_cr_done[w_mr_slot]) & ~r_dt[w_mr_slot];
	wire w_mr_drop = (mem_rvalid & r_cr_done[w_mr_slot]) & r_dt[w_mr_slot];
	wire w_mr_dir = r_dir[w_mr_slot];
	reg [1:0] r_rpl_vld;
	reg [SLOT_W - 1:0] r_rpl_slot [0:1];
	reg [BEAT_INDEX_WIDTH - 1:0] r_rpl_beat [0:1];
	reg [1:0] r_rpl_hold;
	reg [1:0] w_rplc_vld;
	reg [SLOT_W - 1:0] w_rplc_slot [0:1];
	function automatic signed [0:0] sv2v_cast_1_signed;
		input reg signed [0:0] inp;
		sv2v_cast_1_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_9
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_rplc_vld[d] = 1'b0;
					w_rplc_slot[d] = 1'sb0;
					begin : sv2v_autoblock_10
						reg signed [31:0] s;
						for (s = 4 - 1; s >= 0; s = s - 1)
							if ((((((r_vld[s] && (r_dir[s] == sv2v_cast_1_signed(d))) && r_cr_done[s]) && r_ar_taken[s]) && (r_dt[s] || r_nodata[s])) && !r_rpl_done[s]) && !(r_rpl_vld[d] && (r_rpl_slot[d] == sv2v_cast_7C1AF_signed(s)))) begin
								w_rplc_vld[d] = 1'b1;
								w_rplc_slot[d] = sv2v_cast_7C1AF_signed(s);
							end
					end
				end
		end
	end
	localparam signed [31:0] BUF_DEPTH = 4 * FILL_BEATS;
	(* ram_style = "distributed" *) reg [32 - 1:0] r_buf0 [0:BUF_DEPTH - 1];
	(* ram_style = "distributed" *) reg [32 - 1:0] r_buf1 [0:BUF_DEPTH - 1];
	reg [BUF_AW - 1:0] w_rpl_raddr [0:1];
	reg [32 - 1:0] w_rpl_rdata [0:1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_11
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				w_rpl_raddr[d] = {r_rpl_slot[d], r_rpl_beat[d]};
		end
		w_rpl_rdata[0] = r_buf1[w_rpl_raddr[0]];
		w_rpl_rdata[1] = r_buf0[w_rpl_raddr[1]];
	end
	reg [1:0] w_mem_want;
	reg [1:0] w_rpl_pres;
	reg [1:0] w_mem_pres;
	reg [1:0] w_rvalid;
	reg [1:0] w_rpl_hs;
	reg [1:0] w_mem_hs;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_12
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_mem_want[d] = w_mr_fwd & (w_mr_dir == sv2v_cast_1_signed(d));
					w_rpl_pres[d] = r_rpl_vld[d] & (r_rpl_hold[d] | ~w_mem_want[d]);
					w_mem_pres[d] = w_mem_want[d] & ~w_rpl_pres[d];
					w_rvalid[d] = w_rpl_pres[d] | w_mem_pres[d];
					w_rpl_hs[d] = w_rpl_pres[d] & c_rready[d];
					w_mem_hs[d] = w_mem_pres[d] & c_rready[d];
				end
		end
	end
	wire w_mr_hs = (w_mem_hs[0] | w_mem_hs[1]) | w_mr_drop;
	assign mem_rready = w_mr_drop | ((w_mr_fwd & w_mem_pres[w_mr_dir]) & c_rready[w_mr_dir]);
	reg [IW - 1:0] r_out_rid [0:1];
	reg [32 - 1:0] r_out_rdata [0:1];
	reg [1:0] r_out_rresp [0:1];
	reg r_out_rlast [0:1];
	function automatic signed [BEAT_INDEX_WIDTH - 1:0] sv2v_cast_9FF7F_signed;
		input reg signed [BEAT_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_9FF7F_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_13
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				if (w_rpl_pres[d]) begin
					r_out_rid[d] = r_arid[r_rpl_slot[d]];
					r_out_rdata[d] = (r_nodata[r_rpl_slot[d]] ? {32 {1'sb0}} : w_rpl_rdata[d]);
					r_out_rresp[d] = 2'b00;
					r_out_rlast[d] = r_nodata[r_rpl_slot[d]] | (r_rpl_beat[d] == sv2v_cast_9FF7F_signed(FILL_BEATS - 1));
				end
				else begin
					r_out_rid[d] = r_arid[w_mr_slot];
					r_out_rdata[d] = mem_rdata;
					r_out_rresp[d] = mem_rresp;
					r_out_rlast[d] = mem_rlast;
				end
		end
	end
	assign c0_rid = r_out_rid[0];
	assign c1_rid = r_out_rid[1];
	assign c0_rdata = r_out_rdata[0];
	assign c1_rdata = r_out_rdata[1];
	assign c0_rresp = r_out_rresp[0];
	assign c1_rresp = r_out_rresp[1];
	assign c0_rlast = r_out_rlast[0];
	assign c1_rlast = r_out_rlast[1];
	assign c0_ruser = (w_rpl_pres[0] ? {UW {1'sb0}} : mem_ruser);
	assign c1_ruser = (w_rpl_pres[1] ? {UW {1'sb0}} : mem_ruser);
	assign c0_rvalid = w_rvalid[0];
	assign c1_rvalid = w_rvalid[1];
	localparam [1:0] W_IDLE = 2'd0;
	localparam [1:0] W_AW = 2'd1;
	localparam [1:0] W_W = 2'd2;
	localparam [1:0] W_B = 2'd3;
	reg [1:0] r_wstate;
	reg [1:0] r_w_sel;
	reg [SLOT_W - 1:0] r_w_slot;
	reg [1:0] r_w_rr;
	reg [BEAT_INDEX_WIDTH - 1:0] r_w_beat;
	reg [1:0] r_aw_pres;
	reg [1:0] r_aw_yield;
	wire w_aw_same_line;
	wire [1:0] w_aw_younger;
	assign w_aw_same_line = (c_awvalid[0] & c_awvalid[1]) & (line_of(c_awaddr[0]) == line_of(c_awaddr[1]));
	assign w_aw_younger[0] = w_aw_same_line & (r_aw_yield[0] | (r_aw_pres[1] & ~r_aw_pres[0]));
	assign w_aw_younger[1] = w_aw_same_line & (r_aw_yield[1] | (r_aw_pres[0] & ~r_aw_pres[1]));
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_aw_pres <= 1'sb0;
			r_aw_yield <= 1'sb0;
		end
		else begin
			r_aw_pres <= c_awvalid & ~{c1_awready, c0_awready};
			r_aw_yield <= w_aw_younger;
		end
	reg [1:0] w_wb_blocked;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_14
			reg signed [31:0] d;
			for (d = 0; d < 2; d = d + 1)
				begin
					w_wb_blocked[d] = w_aw_younger[d];
					begin : sv2v_autoblock_15
						reg signed [31:0] s;
						for (s = 0; s < 4; s = s + 1)
							if ((r_vld[s] && (r_line[s] == line_of(c_awaddr[d]))) && (!r_cr_done[s] || (r_pd[s] && !r_abs_done[s])))
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
		begin : sv2v_autoblock_16
			reg signed [31:0] s;
			for (s = 4 - 1; s >= 0; s = s - 1)
				if (((r_vld[s] && r_cr_done[s]) && r_pd[s]) && !r_abs_issued[s]) begin
					w_absc_vld = 1'b1;
					w_absc_slot = sv2v_cast_7C1AF_signed(s);
				end
		end
	end
	wire [2:0] w_wcand;
	assign w_wcand = {w_absc_vld, c_awvalid[1] && !w_wb_blocked[1], c_awvalid[0] && !w_wb_blocked[0]};
	reg [1:0] w_wsel;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_wsel = r_w_rr;
		begin : sv2v_autoblock_17
			reg signed [31:0] k;
			for (k = 2; k >= 0; k = k - 1)
				if (w_wcand[(sv2v_cast_32(r_w_rr) + k) % 3])
					w_wsel = sv2v_cast_2((sv2v_cast_32(r_w_rr) + k) % 3);
		end
	end
	wire w_wvalid = |w_wcand;
	assign w_wfly_vld = r_wstate != W_IDLE;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_wfly_line <= 1'sb0;
		else if ((r_wstate == W_IDLE) && w_wvalid)
			r_wfly_line <= (w_wsel == 2'd2 ? r_line[w_absc_slot] : line_of(c_awaddr[w_wsel[0]]));
	wire w_cur_abs = r_w_sel == 2'd2;
	wire w_cur_dir = r_w_sel[0];
	wire [BUF_AW - 1:0] w_abs_raddr;
	wire [32 - 1:0] w_abs_rdata;
	assign w_abs_raddr = {r_w_slot, r_w_beat};
	assign w_abs_rdata = (r_dir[r_w_slot] ? r_buf0[w_abs_raddr] : r_buf1[w_abs_raddr]);
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign mem_awid = (w_cur_abs ? sv2v_cast_83959(8'ha0 | sv2v_cast_8(r_dir[r_w_slot])) : c_awid[w_cur_dir]);
	assign mem_awaddr = (w_cur_abs ? {r_line[r_w_slot], sv2v_cast_2EB38_signed(0)} : c_awaddr[w_cur_dir]);
	assign mem_awlen = (w_cur_abs ? sv2v_cast_8_signed(FILL_BEATS - 1) : c_awlen[w_cur_dir]);
	assign mem_awsize = (w_cur_abs ? sv2v_cast_3_signed($clog2(STRB_W)) : c_awsize[w_cur_dir]);
	assign mem_awburst = (w_cur_abs ? 2'b01 : c_awburst[w_cur_dir]);
	assign mem_awlock = (w_cur_abs ? 1'b0 : c_awlock[w_cur_dir]);
	assign mem_awcache = (w_cur_abs ? 4'b0000 : c_awcache[w_cur_dir]);
	assign mem_awprot = (w_cur_abs ? 3'b000 : c_awprot[w_cur_dir]);
	assign mem_awqos = (w_cur_abs ? 4'b0000 : c_awqos[w_cur_dir]);
	assign mem_awregion = (w_cur_abs ? 4'b0000 : c_awregion[w_cur_dir]);
	assign mem_awuser = (w_cur_abs ? {UW {1'sb0}} : c_awuser[w_cur_dir]);
	assign mem_awvalid = (r_wstate == W_AW) && (w_cur_abs || c_awvalid[w_cur_dir]);
	wire w_wlast = (w_cur_abs ? r_w_beat == sv2v_cast_9FF7F_signed(FILL_BEATS - 1) : c_wlast[w_cur_dir]);
	assign mem_wdata = (w_cur_abs ? w_abs_rdata : c_wdata[w_cur_dir]);
	assign mem_wstrb = (w_cur_abs ? {STRB_W {1'b1}} : c_wstrb[w_cur_dir]);
	assign mem_wlast = w_wlast;
	assign mem_wuser = 1'sb0;
	assign mem_wvalid = (r_wstate == W_W) && (w_cur_abs || c_wvalid[w_cur_dir]);
	assign c0_awready = (((r_wstate == W_AW) && !w_cur_abs) && (w_cur_dir == 1'b0)) && mem_awready;
	assign c1_awready = (((r_wstate == W_AW) && !w_cur_abs) && (w_cur_dir == 1'b1)) && mem_awready;
	assign c0_wready = (((r_wstate == W_W) && !w_cur_abs) && (w_cur_dir == 1'b0)) && mem_wready;
	assign c1_wready = (((r_wstate == W_W) && !w_cur_abs) && (w_cur_dir == 1'b1)) && mem_wready;
	assign c0_bvalid = (((r_wstate == W_B) && !w_cur_abs) && (w_cur_dir == 1'b0)) && mem_bvalid;
	assign c1_bvalid = (((r_wstate == W_B) && !w_cur_abs) && (w_cur_dir == 1'b1)) && mem_bvalid;
	assign c0_bid = mem_bid;
	assign c1_bid = mem_bid;
	assign c0_bresp = mem_bresp;
	assign c1_bresp = mem_bresp;
	assign c0_buser = mem_buser;
	assign c1_buser = mem_buser;
	assign mem_bready = (r_wstate == W_B) && (w_cur_abs || c_bready[w_cur_dir]);
	reg [4 - 1:0] w_rack_hit;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_18
			reg signed [31:0] s;
			for (s = 0; s < 4; s = s + 1)
				w_rack_hit[s] = (((r_vld[s] & r_ar_taken[s]) & ~r_rack[s]) & coh_done_vld[r_dir[s]]) & (coh_done_id[r_dir[s]] == r_arid[s]);
		end
	end
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_DT = 0;
	localparam signed [31:0] l1_pkg_AMBER_CRRESP_PD = 2;
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
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_vld <= 1'sb0;
			r_dir <= 1'sb0;
			r_nodata <= 1'sb0;
			r_ar_taken <= 1'sb0;
			r_ac_done <= 1'sb0;
			r_cr_done <= 1'sb0;
			r_dt <= 1'sb0;
			r_pd <= 1'sb0;
			r_mem_issued <= 1'sb0;
			r_mem_done <= 1'sb0;
			r_rpl_done <= 1'sb0;
			r_abs_issued <= 1'sb0;
			r_abs_done <= 1'sb0;
			r_rack <= 1'sb0;
			r_rr <= 1'b0;
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
			begin : sv2v_autoblock_19
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					begin
						r_pend_cnt[d] <= 1'sb0;
						r_arw_slot[d] <= 1'sb0;
						r_snq_cnt[d] <= 1'sb0;
						r_sni_cnt[d] <= 1'sb0;
						r_cd_beat[d] <= 1'sb0;
						r_rpl_slot[d] <= 1'sb0;
						r_rpl_beat[d] <= 1'sb0;
					end
			end
		end
		else begin
			begin : sv2v_autoblock_20
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					begin : sv2v_autoblock_21
						reg push;
						reg pop;
						push = coh_req_vld[d] & ~((w_grant & (w_grant_dir == sv2v_cast_1_signed(d))) & w_cand_live[d]);
						pop = (w_grant & (w_grant_dir == sv2v_cast_1_signed(d))) & ~w_cand_live[d];
						if (pop) begin
							begin : sv2v_autoblock_22
								reg signed [31:0] k;
								for (k = 0; k < 3; k = k + 1)
									begin
										r_pend_addr[d][k] <= r_pend_addr[d][k + 1];
										r_pend_type[d][k] <= r_pend_type[d][k + 1];
									end
							end
							if (push) begin
								r_pend_addr[d][sv2v_cast_2(r_pend_cnt[d]) - 2'd1] <= coh_req_addr[d];
								r_pend_type[d][sv2v_cast_2(r_pend_cnt[d]) - 2'd1] <= coh_req_type[d];
							end
							else
								r_pend_cnt[d] <= r_pend_cnt[d] - 3'd1;
						end
						else if (push) begin
							if (r_pend_cnt[d] < sv2v_cast_3_signed(PEND_DEPTH)) begin
								r_pend_addr[d][sv2v_cast_2(r_pend_cnt[d])] <= coh_req_addr[d];
								r_pend_type[d][sv2v_cast_2(r_pend_cnt[d])] <= coh_req_type[d];
								r_pend_cnt[d] <= r_pend_cnt[d] + 3'd1;
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
				r_ac_done[w_slot_idx] <= 1'b0;
				r_cr_done[w_slot_idx] <= 1'b0;
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
				r_rr <= ~w_grant_dir;
			end
			begin : sv2v_autoblock_23
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					if (w_ar_take[d]) begin
						r_ar_taken[r_arw_slot[d]] <= 1'b1;
						r_arid[r_arw_slot[d]] <= c_arid[d];
						r_arcache[r_arw_slot[d]] <= c_arcache[d];
						r_arprot[r_arw_slot[d]] <= c_arprot[d];
						r_aruser[r_arw_slot[d]] <= c_aruser[d];
						r_arw_vld[d] <= 1'b0;
					end
			end
			begin : sv2v_autoblock_24
				reg signed [31:0] p;
				for (p = 0; p < 2; p = p + 1)
					begin : sv2v_autoblock_25
						reg push_q;
						push_q = w_grant & (w_grant_dir == sv2v_cast_1_signed(1 - p));
						if (w_ac_hs[p]) begin
							begin : sv2v_autoblock_26
								reg signed [31:0] k;
								for (k = 0; k < (4 - 1); k = k + 1)
									r_snq[p][k] <= r_snq[p][k + 1];
							end
							r_ac_done[w_ac_slot[p]] <= 1'b1;
						end
						if (push_q)
							r_snq[p][sv2v_cast_7C1AF(r_snq_cnt[p] - sv2v_cast_36294(w_ac_hs[p]))] <= w_slot_idx;
						r_snq_cnt[p] <= (r_snq_cnt[p] + sv2v_cast_36294(push_q)) - sv2v_cast_36294(w_ac_hs[p]);
						if (w_cr_hs[p]) begin
							begin : sv2v_autoblock_27
								reg signed [31:0] k;
								for (k = 0; k < (2 - 1); k = k + 1)
									r_sni[p][k] <= r_sni[p][k + 1];
							end
							r_cr_done[w_sni_head[p]] <= 1'b1;
							r_dt[w_sni_head[p]] <= crresp_w[p][l1_pkg_AMBER_CRRESP_DT];
							r_pd[w_sni_head[p]] <= crresp_w[p][l1_pkg_AMBER_CRRESP_DT] & crresp_w[p][l1_pkg_AMBER_CRRESP_PD];
							if ((crresp_w[p][l1_pkg_AMBER_CRRESP_DT] && !r_mem_issued[w_sni_head[p]]) && !(w_mar_vld && (w_mar_slot == w_sni_head[p])))
								r_mem_done[w_sni_head[p]] <= 1'b1;
							r_cd_beat[p] <= 1'sb0;
						end
						if (w_ac_hs[p])
							r_sni[p][sv2v_cast_C8806(r_sni_cnt[p] - sv2v_cast_F4A8C(w_cr_hs[p]))] <= w_ac_slot[p];
						r_sni_cnt[p] <= (r_sni_cnt[p] + sv2v_cast_F4A8C(w_ac_hs[p])) - sv2v_cast_F4A8C(w_cr_hs[p]);
						if (w_cd_hs[p])
							r_cd_beat[p] <= (cdlast[p] ? {BEAT_INDEX_WIDTH {1'sb0}} : r_cd_beat[p] + sv2v_cast_9FF7F_signed(1));
					end
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
			begin : sv2v_autoblock_28
				reg signed [31:0] d;
				for (d = 0; d < 2; d = d + 1)
					if (r_rpl_vld[d]) begin
						if (w_rpl_hs[d]) begin
							r_rpl_hold[d] <= 1'b0;
							if (r_out_rlast[d]) begin
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
						r_w_rr <= sv2v_cast_2((sv2v_cast_32(w_wsel) + 1) % 3);
						r_w_beat <= 1'sb0;
						r_wstate <= W_AW;
						if (w_wsel == 2'd2)
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
			begin : sv2v_autoblock_29
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
	always @(posedge clk)
		if (w_cd_hs[0])
			r_buf0[{w_sni_head[0], r_cd_beat[0]}] <= cddata_w[0];
	always @(posedge clk)
		if (w_cd_hs[1])
			r_buf1[{w_sni_head[1], r_cd_beat[1]}] <= cddata_w[1];
	assign dbg_busy = |r_vld;
	assign dbg_slot_vld = r_vld;
	assign dbg_pend_vld = {r_pend_cnt[1] != 3'd0, r_pend_cnt[0] != 3'd0};
	assign dbg_abs_pend = |((r_vld & r_pd) & ~r_abs_done);
	assign dbg_grant = w_grant;
	assign dbg_grant_dir = w_grant_dir;
	assign dbg_grant_addr = w_cand_addr[w_grant_dir];
	assign dbg_grant_slot = w_slot_idx;
	wire unused_ar;
	assign unused_ar = &{1'b0, c_arlen[0], c0_arsize, c0_arburst, c0_arlock, c0_arqos, c0_arregion, c_arlen[1], c1_arsize, c1_arburst, c1_arlock, c1_arqos, c1_arregion, c0_wuser, c1_wuser, mem_rid[IW - 1:SLOT_W]};
	initial _sv2v_0 = 0;
endmodule
