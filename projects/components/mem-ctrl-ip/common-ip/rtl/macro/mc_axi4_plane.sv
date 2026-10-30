// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_axi4_plane
// Purpose: The family AXI4 host interface. Bolts the common AXI burst
//          splitters onto the front of the wr/rd intakes. The write-data CAM
//          and rd-cmd CAM now live in mc_storage_plane; this module exposes
//          the raw intake pushes and the snarf probe/hit/data stream as
//          inter-plane ports, and keeps the in-flight read return ring.
//
//   host AXI4 -> [wr/rd splitter] -> mc_wr_intake -> mc_storage_plane (wr CAM)
//                                 -> mc_rd_intake -> mc_storage_plane (rd CAM)
//   snarf: rd_intake probe goes to storage; hit + data stream return here.
//   external: inter-plane ports to mc_storage_plane on both sides.
//
// Documentation: docs/uarch/PUMICE_AXI4_PLANE_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_axi4_plane #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_USER_WIDTH    = 1,
    // NOTE pumice_core instantiates this with .DRAM_BEAT_WIDTH(DW) -- the AXI
    // data width, NOT the DRAM beat width. The front end is deliberately
    // DFI-word granular (one AXI beat == one DFI word), so the two coincide
    // here and the name misleads. Kept only to size DRAM_BURST_BYTES below;
    // it is no longer passed down, because the intakes were reading it as a
    // DRAM quantity when it is an AXI one.
    parameter int DRAM_BEAT_WIDTH   = 64,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BYTE_OFFSET_WIDTH = 3,
    // ANDESITE BG DELTA: bank-group intake mapping (DDR4). HAS_BG=0 keeps
    // generations 2/3 bit-identical; andesite passes 1/2.
    parameter int BG_WIDTH = 1,
    parameter bit HAS_BG   = 0,
    // AXI beats in one DRAM burst. This is what pumice_core passes as
    // BURST_WORDS -- NOT the JEDEC burst length, despite having been called
    // AXI_BEATS_PER_BURST here and documented as "DRAM beats" downstream. Same identifier,
    // three different quantities across the design (JEDEC device beats in
    // pumice_core, pumice beats in pumice_dfi_plane, AXI beats here), which
    // is how a ragged-burst check got derived against the wrong units.
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,
    parameter int N_SCHED_LU      = 4,
    parameter int AGE_WIDTH       = 16,
    // Reads the controller can hold IN FLIGHT (mc_rd_return_ring DEPTH).
    parameter int RD_RET_DEPTH    = 32,
    // Lean-intake knobs (granite; the defaults are the pumice form):
    parameter bit HAS_SNARF        = 1'b1, // 0 = no snarf probe / stage / source arbiter in mc_rd_intake
    parameter bit RD_AR_STAGE_REG  = HAS_SNARF, // registered AR decode stage in mc_rd_intake (see AR_STAGE_REG)
    parameter bit RD_MERGE_MARK_REG = 1'b0,    // mc_rd_return_ring MERGE_MARK_REG
    parameter int RD_FIFO_DEPTH    = 16,   // 0 = no rd-data FIFO (the ring feeds the R skid directly)
    parameter int WDATA_FIFO_DEPTH = 16,   // 0 = no wr-data FIFO (the W skid feeds the store directly)
    parameter int SKID_DEPTH_R     = 4,    // axi4_slave_rd R skid
    parameter int SKID_DEPTH_W     = 4,    // axi4_slave_wr W skid
    parameter bit SHARED_ADDR_MAP  = 1'b0, // 1 = one address mapper for both intakes, reads first
    parameter bit HALF_AGG         = 1'b0, // 1 = mc_axi4_half_agg at the host edge: two adjacent half-width single beats become one
                                           //     full-width beat (one DRAM burst, not two). granite TASK-005; 0 = none (pumice)
    parameter int HALF_AGG_HOLD    = 4,    // cycles a lone lo waits for its hi (HALF_AGG only)
    parameter int HALF_AGG_DEPTH   = RD_RET_DEPTH, // side-queue depth = commands in flight per direction; below the plane's outstanding capacity it throttles full-width traffic (proxy: +8 rd cycles at 4)

    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int UW   = AXI_USER_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    // Split each host burst at DRAM-burst-byte boundaries -> 1 DRAM burst each.
    parameter int DRAM_BURST_BYTES = AXI_BEATS_PER_BURST * (DRAM_BEAT_WIDTH / 8)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    input  logic [4:0]               bank_lsb_i,
    input  logic                     hash_en_i,
    input  logic [7:0]               hash_seed_i,

    //=========================================================================
    // Host AXI4 (pre-split)
    //=========================================================================
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic [UW-1:0]  s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [DW-1:0]  s_axi_wdata,  input logic [SW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic [UW-1:0] s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic [UW-1:0]  s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic [UW-1:0]  s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic [UW-1:0]  s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready,

    //=========================================================================
    // WR intake -> storage plane (WR data CAM) push interface
    //=========================================================================
    output logic                aw_push_valid_o,
    input  logic                aw_push_ready_i,
    output logic [BKW-1:0]      aw_push_bank_o,
    output logic [ROW_WIDTH-1:0]aw_push_row_o,
    output logic [COL_WIDTH-1:0]aw_push_col_o,
    output logic [IW-1:0]       aw_push_id_o,
    output logic [3:0]          aw_push_qos_o,
    output logic                aw_push_agg_o,
    output logic                aw_push_last_o,

    output logic                wd_valid_o,
    input  logic                wd_ready_i,
    output logic [DW-1:0]       wd_data_o,
    output logic [SW-1:0]       wd_strb_o,
    output logic                wd_last_o,

    // commit-done notification from storage WR CAM -> WR intake
    input  logic                wr_done_valid_i,
    input  logic [IW-1:0]       wr_done_id_i,

    //=========================================================================
    // RD intake <-> storage plane (WR data CAM snarf)
    //=========================================================================
    output logic                snarf_probe_valid_o,
    output logic [BKW-1:0]      snarf_probe_bank_o,
    output logic [ROW_WIDTH-1:0]snarf_probe_row_o,
    output logic [COL_WIDTH-1:0]snarf_probe_col_o,
    output logic [IW-1:0]       snarf_probe_id_o,
    output logic [7:0]          snarf_probe_len_o,
    input  logic                snarf_hit_i,
    output logic                snarf_accept_o,
    input  logic                snarf_rd_valid_i,
    output logic                snarf_rd_ready_o,
    input  logic [DW-1:0]       snarf_rd_data_i,
    input  logic                snarf_rd_last_i,

    //=========================================================================
    // RD intake -> storage plane (RD cmd CAM) push interface
    //=========================================================================
    output logic                ar_push_valid_o,
    input  logic                ar_push_ready_i,
    output logic [BKW-1:0]      ar_push_bank_o,
    output logic [ROW_WIDTH-1:0]ar_push_row_o,
    output logic [COL_WIDTH-1:0]ar_push_col_o,
    output logic [IW-1:0]       ar_push_id_o,
    output logic [3:0]          ar_push_qos_o,

    //=========================================================================
    // Return ring <-> storage plane (RD cmd CAM)
    //=========================================================================
    output logic                rt_alloc_ready_o,
    output logic [$clog2(RD_RET_DEPTH)-1:0] rt_alloc_ticket_o,
    output logic                rd_iss_ready_o,
    input  logic                rd_iss_valid_i,
    input  logic [$clog2(RD_RET_DEPTH)-1:0] rd_iss_ticket_i,
    input  logic                rd_cam_ins_ready_i,
    // read combining: the CAM's insert this cycle shadows an older ticket
    // (tie 0 on a store without a read combiner)
    input  logic                rt_alloc_merge_i,
    input  logic [$clog2(RD_RET_DEPTH)-1:0] rt_alloc_src_i,

    //=========================================================================
    // DFI return stream -> return ring
    //=========================================================================
    input  logic                rd_dfi_ret_valid_i,
    output logic                rd_dfi_ret_ready_o,
    input  logic [DW-1:0]       rd_dfi_ret_data_i,
    input  logic [1:0]          rd_dfi_ret_resp_i,
    input  logic                rd_dfi_ret_last_i,

    output logic                busy_o
);

    import mc_common_pkg::*;

    // ======================================================================
    // Split -> intake AXI nets
    // ======================================================================
    logic [IW-1:0] sw_awid;   logic [AW-1:0] sw_awaddr;  logic [7:0] sw_awlen;
    logic [2:0]    sw_awsize; logic [1:0]    sw_awburst; logic       sw_awlock;
    logic [3:0]    sw_awcache;logic [2:0]    sw_awprot;  logic [3:0] sw_awqos;
    logic [3:0]    sw_awregion;logic [UW-1:0] sw_awuser; logic       sw_awvalid, sw_awready;
    logic [DW-1:0] sw_wdata;  logic [SW-1:0] sw_wstrb;   logic sw_wlast;
    logic [UW-1:0] sw_wuser;  logic          sw_wvalid,  sw_wready;

    // Return ring -> rd_intake drain nets (declared early for decl-order lint).
    logic                drain_valid, drain_ready, drain_last;
    logic [DW-1:0]       drain_data;
    logic [1:0]          drain_resp;

    logic [IW-1:0] sr_arid;   logic [AW-1:0] sr_araddr;  logic [7:0] sr_arlen;
    logic [2:0]    sr_arsize; logic [1:0]    sr_arburst; logic       sr_arlock;
    logic [3:0]    sr_arcache;logic [2:0]    sr_arprot;  logic [3:0] sr_arqos;
    logic [3:0]    sr_arregion;logic [UW-1:0] sr_aruser; logic       sr_arvalid, sr_arready;

    // aggregation sideband: chopper/splitter -> intake -> CAM. agg/last ride
    // with each sub-command so the return path collapses B/RLAST from stored
    // bits, with no separate snoop-and-count aggregator module.
    logic sw_aw_agg, sw_aw_last;   // wr_split -> wr_intake
    logic sr_ar_agg, sr_ar_last;   // rd chopper -> rd_intake

    // ======================================================================
    // host edge: the half-width aggregator (HALF_AGG) or straight wires
    // ======================================================================
    logic [IW-1:0] ha_awid;   logic [AW-1:0] ha_awaddr;  logic [7:0] ha_awlen;  logic [2:0] ha_awsize;
    logic [1:0]    ha_awburst; logic ha_awlock; logic [3:0] ha_awcache; logic [2:0] ha_awprot;
    logic [3:0]    ha_awqos;  logic [3:0] ha_awregion; logic [UW-1:0] ha_awuser; logic ha_awvalid, ha_awready;
    logic [DW-1:0] ha_wdata;  logic [SW-1:0] ha_wstrb; logic ha_wlast; logic [UW-1:0] ha_wuser; logic ha_wvalid, ha_wready;
    logic [IW-1:0] ha_bid;    logic [1:0] ha_bresp; logic [UW-1:0] ha_buser; logic ha_bvalid, ha_bready;
    logic [IW-1:0] ha_arid;   logic [AW-1:0] ha_araddr;  logic [7:0] ha_arlen;  logic [2:0] ha_arsize;
    logic [1:0]    ha_arburst; logic ha_arlock; logic [3:0] ha_arcache; logic [2:0] ha_arprot;
    logic [3:0]    ha_arqos;  logic [3:0] ha_arregion; logic [UW-1:0] ha_aruser; logic ha_arvalid, ha_arready;
    logic [IW-1:0] ha_rid;    logic [DW-1:0] ha_rdata; logic [1:0] ha_rresp; logic ha_rlast; logic [UW-1:0] ha_ruser; logic ha_rvalid, ha_rready;

    generate
    if (HALF_AGG) begin : g_half_agg
        mc_axi4_half_agg #(
            .AXI_ID_WIDTH   (IW),
            .AXI_ADDR_WIDTH (AW),
            .AXI_DATA_WIDTH (DW),
            .AXI_USER_WIDTH (UW),
            .HOLD_CYCLES    (HALF_AGG_HOLD),
            .AGG_FIFO_DEPTH (HALF_AGG_DEPTH)
        ) u_half_agg (
            .aclk        (aclk),
            .aresetn     (aresetn),
            .fub_awid    (s_axi_awid),    .fub_awaddr  (s_axi_awaddr),  .fub_awlen   (s_axi_awlen),
            .fub_awsize  (s_axi_awsize),  .fub_awburst (s_axi_awburst), .fub_awlock  (s_axi_awlock),
            .fub_awcache (s_axi_awcache), .fub_awprot  (s_axi_awprot),  .fub_awqos   (s_axi_awqos),
            .fub_awregion(s_axi_awregion),.fub_awuser  (s_axi_awuser),  .fub_awvalid (s_axi_awvalid),
            .fub_awready (s_axi_awready),
            .fub_wdata   (s_axi_wdata),   .fub_wstrb   (s_axi_wstrb),   .fub_wlast   (s_axi_wlast),
            .fub_wuser   (s_axi_wuser),   .fub_wvalid  (s_axi_wvalid),  .fub_wready  (s_axi_wready),
            .fub_bid     (s_axi_bid),     .fub_bresp   (s_axi_bresp),   .fub_buser   (s_axi_buser),
            .fub_bvalid  (s_axi_bvalid),  .fub_bready  (s_axi_bready),
            .fub_arid    (s_axi_arid),    .fub_araddr  (s_axi_araddr),  .fub_arlen   (s_axi_arlen),
            .fub_arsize  (s_axi_arsize),  .fub_arburst (s_axi_arburst), .fub_arlock  (s_axi_arlock),
            .fub_arcache (s_axi_arcache), .fub_arprot  (s_axi_arprot),  .fub_arqos   (s_axi_arqos),
            .fub_arregion(s_axi_arregion),.fub_aruser  (s_axi_aruser),  .fub_arvalid (s_axi_arvalid),
            .fub_arready (s_axi_arready),
            .fub_rid     (s_axi_rid),     .fub_rdata   (s_axi_rdata),   .fub_rresp   (s_axi_rresp),
            .fub_rlast   (s_axi_rlast),   .fub_ruser   (s_axi_ruser),   .fub_rvalid  (s_axi_rvalid),
            .fub_rready  (s_axi_rready),
            .m_awid      (ha_awid),       .m_awaddr    (ha_awaddr),     .m_awlen     (ha_awlen),
            .m_awsize    (ha_awsize),     .m_awburst   (ha_awburst),    .m_awlock    (ha_awlock),
            .m_awcache   (ha_awcache),    .m_awprot    (ha_awprot),     .m_awqos     (ha_awqos),
            .m_awregion  (ha_awregion),   .m_awuser    (ha_awuser),     .m_awvalid   (ha_awvalid),
            .m_awready   (ha_awready),
            .m_wdata     (ha_wdata),      .m_wstrb     (ha_wstrb),      .m_wlast     (ha_wlast),
            .m_wuser     (ha_wuser),      .m_wvalid    (ha_wvalid),     .m_wready    (ha_wready),
            .m_bid       (ha_bid),        .m_bresp     (ha_bresp),      .m_buser     (ha_buser),
            .m_bvalid    (ha_bvalid),     .m_bready    (ha_bready),
            .m_arid      (ha_arid),       .m_araddr    (ha_araddr),     .m_arlen     (ha_arlen),
            .m_arsize    (ha_arsize),     .m_arburst   (ha_arburst),    .m_arlock    (ha_arlock),
            .m_arcache   (ha_arcache),    .m_arprot    (ha_arprot),     .m_arqos     (ha_arqos),
            .m_arregion  (ha_arregion),   .m_aruser    (ha_aruser),     .m_arvalid   (ha_arvalid),
            .m_arready   (ha_arready),
            .m_rid       (ha_rid),        .m_rdata     (ha_rdata),      .m_rresp     (ha_rresp),
            .m_rlast     (ha_rlast),      .m_ruser     (ha_ruser),      .m_rvalid    (ha_rvalid),
            .m_rready    (ha_rready)
        );
    end else begin : g_no_half_agg
        assign ha_awid = s_axi_awid;   assign ha_awaddr = s_axi_awaddr;   assign ha_awlen = s_axi_awlen;
        assign ha_awsize = s_axi_awsize; assign ha_awburst = s_axi_awburst; assign ha_awlock = s_axi_awlock;
        assign ha_awcache = s_axi_awcache; assign ha_awprot = s_axi_awprot; assign ha_awqos = s_axi_awqos;
        assign ha_awregion = s_axi_awregion; assign ha_awuser = s_axi_awuser; assign ha_awvalid = s_axi_awvalid;
        assign s_axi_awready = ha_awready;
        assign ha_wdata = s_axi_wdata; assign ha_wstrb = s_axi_wstrb; assign ha_wlast = s_axi_wlast;
        assign ha_wuser = s_axi_wuser; assign ha_wvalid = s_axi_wvalid; assign s_axi_wready = ha_wready;
        assign s_axi_bid = ha_bid; assign s_axi_bresp = ha_bresp; assign s_axi_buser = ha_buser;
        assign s_axi_bvalid = ha_bvalid; assign ha_bready = s_axi_bready;
        assign ha_arid = s_axi_arid;   assign ha_araddr = s_axi_araddr;   assign ha_arlen = s_axi_arlen;
        assign ha_arsize = s_axi_arsize; assign ha_arburst = s_axi_arburst; assign ha_arlock = s_axi_arlock;
        assign ha_arcache = s_axi_arcache; assign ha_arprot = s_axi_arprot; assign ha_arqos = s_axi_arqos;
        assign ha_arregion = s_axi_arregion; assign ha_aruser = s_axi_aruser; assign ha_arvalid = s_axi_arvalid;
        assign s_axi_arready = ha_arready;
        assign s_axi_rid = ha_rid; assign s_axi_rdata = ha_rdata; assign s_axi_rresp = ha_rresp;
        assign s_axi_rlast = ha_rlast; assign s_axi_ruser = ha_ruser; assign s_axi_rvalid = ha_rvalid;
        assign ha_rready = s_axi_rready;
    end
    endgenerate

    // ---- WR request side: chop AW into DFI-burst sub-commands + reframe W ---
    mc_wr_splitter #(
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW),
        .AXI_BEATS_PER_BURST   (AXI_BEATS_PER_BURST)
    ) u_wr_split (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .fub_awid    (ha_awid),
        .fub_awaddr  (ha_awaddr),
        .fub_awlen   (ha_awlen),
        .fub_awsize  (ha_awsize),
        .fub_awburst (ha_awburst),
        .fub_awlock  (ha_awlock),
        .fub_awcache (ha_awcache),
        .fub_awprot  (ha_awprot),
        .fub_awqos   (ha_awqos),
        .fub_awregion(ha_awregion),
        .fub_awuser  (ha_awuser),
        .fub_awvalid (ha_awvalid),
        .fub_awready (ha_awready),
        .fub_wdata   (ha_wdata),
        .fub_wstrb   (ha_wstrb),
        .fub_wlast   (ha_wlast),
        .fub_wuser   (ha_wuser),
        .fub_wvalid  (ha_wvalid),
        .fub_wready  (ha_wready),
        .m_awid      (sw_awid),
        .m_awaddr    (sw_awaddr),
        .m_awlen     (sw_awlen),
        .m_awsize    (sw_awsize),
        .m_awburst   (sw_awburst),
        .m_awlock    (sw_awlock),
        .m_awcache   (sw_awcache),
        .m_awprot    (sw_awprot),
        .m_awqos     (sw_awqos),
        .m_awregion  (sw_awregion),
        .m_awuser    (sw_awuser),
        .m_awvalid   (sw_awvalid),
        .m_awready   (sw_awready),
        .m_wdata     (sw_wdata),
        .m_wstrb     (sw_wstrb),
        .m_wlast     (sw_wlast),
        .m_wuser     (sw_wuser),
        .m_wvalid    (sw_wvalid),
        .m_wready    (sw_wready),
        .m_aw_agg    (sw_aw_agg),
        .m_aw_last   (sw_aw_last)
    );

    // ---- RD request side: chop AR into DFI-burst sub-commands ---------------
    mc_axi_burst_chopper #(
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_USER_WIDTH(UW),
        .STRB_BYTES    (SW),
        .AXI_BEATS_PER_BURST   (AXI_BEATS_PER_BURST)
    ) u_rd_split (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .fub_axid    (ha_arid),
        .fub_axaddr  (ha_araddr),
        .fub_axlen   (ha_arlen),
        .fub_axsize  (ha_arsize),
        .fub_axburst (ha_arburst),
        .fub_axlock  (ha_arlock),
        .fub_axcache (ha_arcache),
        .fub_axprot  (ha_arprot),
        .fub_axqos   (ha_arqos),
        .fub_axregion(ha_arregion),
        .fub_axuser  (ha_aruser),
        .fub_axvalid (ha_arvalid),
        .fub_axready (ha_arready),
        .m_axid      (sr_arid),
        .m_axaddr    (sr_araddr),
        .m_axlen     (sr_arlen),
        .m_axsize    (sr_arsize),
        .m_axburst   (sr_arburst),
        .m_axlock    (sr_arlock),
        .m_axcache   (sr_arcache),
        .m_axprot    (sr_arprot),
        .m_axqos     (sr_arqos),
        .m_axregion  (sr_arregion),
        .m_axuser    (sr_aruser),
        .m_axvalid   (sr_arvalid),
        .m_axready   (sr_arready),
        .m_ax_agg    (sr_ar_agg),
        .m_ax_last   (sr_ar_last)
    );

    // ======================================================================
    // intakes
    // ======================================================================
    logic w_wri_busy, w_rdi_busy;
    // shared-mapper request / grant / decode nets (SHARED_ADDR_MAP)
    logic                 w_map_req_rd, w_map_req_wr, w_map_grant_rd, w_map_grant_wr;
    logic [AW-1:0]        w_map_addr_rd, w_map_addr_wr;
    logic [RKW-1:0]       w_map_rank;
    logic [BKW-1:0]       w_map_bank;
    logic [ROW_WIDTH-1:0] w_map_row;
    logic [COL_WIDTH-1:0] w_map_col;

    // ---- WR intake ----
    mc_wr_intake #(
        .AXI_ID_WIDTH     (IW),
        .AXI_ADDR_WIDTH   (AW),
        .AXI_DATA_WIDTH   (DW),
        .AXI_USER_WIDTH   (UW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .BG_WIDTH        (BG_WIDTH),
        .HAS_BG          (HAS_BG),
        .AXI_BEATS_PER_BURST               (AXI_BEATS_PER_BURST),
        .WDATA_FIFO_DEPTH (WDATA_FIFO_DEPTH),
        .SKID_DEPTH_W     (SKID_DEPTH_W),
        .HAS_ADDR_MAP     (!SHARED_ADDR_MAP)
    ) u_wr_intake (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .bank_lsb_i    (bank_lsb_i),
        .hash_en_i     (hash_en_i),
        .hash_seed_i   (hash_seed_i),
        .s_axi_awid    (sw_awid),
        .s_axi_awaddr  (sw_awaddr),
        .s_axi_awlen   (sw_awlen),
        .s_axi_awsize  (sw_awsize),
        .s_axi_awburst (sw_awburst),
        .s_axi_awlock  (sw_awlock),
        .s_axi_awcache (sw_awcache),
        .s_axi_awprot  (sw_awprot),
        .s_axi_awqos   (sw_awqos),
        .s_axi_awregion(sw_awregion),
        .s_axi_awuser  (sw_awuser),
        .s_axi_awvalid (sw_awvalid),
        .s_axi_awready (sw_awready),
        .aw_agg_i      (sw_aw_agg),
        .aw_last_i     (sw_aw_last),
        .s_axi_wdata   (sw_wdata),
        .s_axi_wstrb   (sw_wstrb),
        .s_axi_wlast   (sw_wlast),
        .s_axi_wuser   (sw_wuser),
        .s_axi_wvalid  (sw_wvalid),
        .s_axi_wready  (sw_wready),
        // consolidated B straight to the host (one B per host burst)
        .s_axi_bid      (ha_bid),
        .s_axi_bresp    (ha_bresp),
        .s_axi_buser    (ha_buser),
        .s_axi_bvalid   (ha_bvalid),
        .s_axi_bready   (ha_bready),
        .aw_push_valid_o(aw_push_valid_o),
        .aw_push_ready_i(aw_push_ready_i),
        .aw_push_rank_o (),
        .aw_push_bank_o (aw_push_bank_o),
        .aw_push_row_o  (aw_push_row_o),
        .aw_push_col_o  (aw_push_col_o),
        .aw_push_id_o   (aw_push_id_o),
        .aw_push_qos_o  (aw_push_qos_o),
        .aw_push_err_o  (),
        .aw_push_agg_o  (aw_push_agg_o),
        .aw_push_last_o (aw_push_last_o),
        .wdata_valid_o  (wd_valid_o),
        .wdata_ready_i  (wd_ready_i),
        .wdata_o        (wd_data_o),
        .wstrb_o        (wd_strb_o),
        .wlast_o        (wd_last_o),
        .wr_done_valid_i(wr_done_valid_i),
        .wr_done_id_i   (wr_done_id_i),
        .wr_done_resp_i (2'b00),
        .busy_o         (w_wri_busy),
        .map_req_o      (w_map_req_wr),
        .map_addr_o     (w_map_addr_wr),
        .map_grant_i    (w_map_grant_wr),
        .map_rank_i     (w_map_rank),
        .map_bank_i     (w_map_bank),
        .map_row_i      (w_map_row),
        .map_col_i      (w_map_col)
    );

    // ---- RD intake ----
    mc_rd_intake #(
        .AXI_ID_WIDTH     (IW),
        .AXI_ADDR_WIDTH   (AW),
        .AXI_DATA_WIDTH   (DW),
        .AXI_USER_WIDTH   (UW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .BG_WIDTH        (BG_WIDTH),
        .HAS_BG          (HAS_BG),
        .AXI_BEATS_PER_BURST               (AXI_BEATS_PER_BURST),
        // one order-FIFO slot per read the ring can hold in flight, plus the
        // snarf hits that never enter the ring
        .ORDER_FIFO_DEPTH (RD_RET_DEPTH + 8),
        .RD_FIFO_DEPTH    (RD_FIFO_DEPTH),
        .SKID_DEPTH_R     (SKID_DEPTH_R),
        .HAS_SNARF        (HAS_SNARF),
        .AR_STAGE_REG     (RD_AR_STAGE_REG),
        .HAS_ADDR_MAP     (!SHARED_ADDR_MAP)
    ) u_rd_intake (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .bank_lsb_i    (bank_lsb_i),
        .hash_en_i     (hash_en_i),
        .hash_seed_i   (hash_seed_i),
        .s_axi_arid    (sr_arid),
        .s_axi_araddr  (sr_araddr),
        .s_axi_arlen   (sr_arlen),
        .s_axi_arsize  (sr_arsize),
        .s_axi_arburst (sr_arburst),
        .s_axi_arlock  (sr_arlock),
        .s_axi_arcache (sr_arcache),
        .s_axi_arprot  (sr_arprot),
        .s_axi_arqos   (sr_arqos),
        .s_axi_arregion(sr_arregion),
        .s_axi_aruser  (sr_aruser),
        .s_axi_arvalid (sr_arvalid),
        .s_axi_arready (sr_arready),
        .ar_agg_i      (sr_ar_agg),
        .ar_last_i     (sr_ar_last),
        // collapsed R straight to the host (one RLAST per host burst)
        .s_axi_rid          (ha_rid),
        .s_axi_rdata        (ha_rdata),
        .s_axi_rresp        (ha_rresp),
        .s_axi_rlast        (ha_rlast),
        .s_axi_ruser        (ha_ruser),
        .s_axi_rvalid       (ha_rvalid),
        .s_axi_rready       (ha_rready),
        .ar_push_valid_o    (ar_push_valid_o),
        .ar_push_ready_i    (ar_push_ready_i),
        .ar_push_rank_o     (),
        .ar_push_bank_o     (ar_push_bank_o),
        .ar_push_row_o      (ar_push_row_o),
        .ar_push_col_o      (ar_push_col_o),
        .ar_push_id_o       (ar_push_id_o),
        .ar_push_qos_o      (ar_push_qos_o),
        .snarf_probe_valid_o(snarf_probe_valid_o),
        .snarf_probe_rank_o (),
        .snarf_probe_bank_o (snarf_probe_bank_o),
        .snarf_probe_row_o  (snarf_probe_row_o),
        .snarf_probe_col_o  (snarf_probe_col_o),
        .snarf_probe_id_o   (snarf_probe_id_o),
        .snarf_probe_len_o  (snarf_probe_len_o),
        .snarf_hit_i        (snarf_hit_i),
        .snarf_accept_o     (snarf_accept_o),
        .snarf_rd_valid_i   (snarf_rd_valid_i),
        .snarf_rd_ready_o   (snarf_rd_ready_o),
        .snarf_rd_data_i    (snarf_rd_data_i),
        .snarf_rd_last_i    (snarf_rd_last_i),
        .dfi_rd_valid_i     (drain_valid),
        .dfi_rd_ready_o     (drain_ready),
        .dfi_rd_data_i      (drain_data),
        .dfi_rd_last_i      (drain_last),
        .dfi_rd_resp_i      (drain_resp),
        .busy_o             (w_rdi_busy),
        .map_req_o          (w_map_req_rd),
        .map_addr_o         (w_map_addr_rd),
        .map_grant_i        (w_map_grant_rd),
        .map_rank_i         (w_map_rank),
        .map_bank_i         (w_map_bank),
        .map_row_i          (w_map_row),
        .map_col_i          (w_map_col)
    );

    // ---- shared address mapper (SHARED_ADDR_MAP) -----------------------------
    // One decoder. Each intake requests it when it has a command to decode
    // (no ready term in the request: the decode feeds ready); when both ask,
    // the grant alternates, so neither side starves. An intake stalls its
    // own handshake while it does not hold the grant.
    generate if (SHARED_ADDR_MAP) begin : g_shared_map
        logic [AW-1:0] w_map_addr;
        logic          r_turn_rd;   // 1 = reads win the next contended cycle
        assign w_map_grant_rd = w_map_req_rd && (!w_map_req_wr ||  r_turn_rd);
        assign w_map_grant_wr = w_map_req_wr && (!w_map_req_rd || !r_turn_rd);
        assign w_map_addr     = w_map_grant_rd ? w_map_addr_rd : w_map_addr_wr;
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))            r_turn_rd <= 1'b1;
            else if (w_map_req_rd && w_map_req_wr) r_turn_rd <= !r_turn_rd;
        )
        mc_addr_mapper #(
            .AXI_ADDR_WIDTH   (AW),
            .NUM_RANKS        (NUM_RANKS),
            .NUM_BANKS        (NUM_BANKS),
            .ROW_WIDTH        (ROW_WIDTH),
            .COL_WIDTH        (COL_WIDTH),
            .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
            .BG_WIDTH        (BG_WIDTH),
            .HAS_BG          (HAS_BG)
        ) u_addr_mapper (
            .axi_addr_i (w_map_addr),
            .bank_lsb_i (bank_lsb_i),
            .hash_en_i  (hash_en_i),
            .hash_seed_i(hash_seed_i),
            .rank_o     (w_map_rank),
            .bg_o       (),
            .bank_o     (w_map_bank),
            .row_o      (w_map_row),
            .col_o      (w_map_col)
        );
    end else begin : g_own_maps
        assign w_map_grant_rd = 1'b0;
        assign w_map_grant_wr = 1'b0;
        assign w_map_rank = '0; assign w_map_bank = '0; assign w_map_row = '0; assign w_map_col = '0;
        wire _unused_shared = &{1'b0, w_map_req_rd, w_map_req_wr, w_map_addr_rd, w_map_addr_wr};
    end endgenerate

    // ---- RD return ring (in-flight reads) ----
    logic w_rdr_busy;

    mc_rd_return_ring #(
        .DEPTH              (RD_RET_DEPTH),
        .AXI_DATA_WIDTH     (DW),
        .AXI_BEATS_PER_BURST(AXI_BEATS_PER_BURST),
        .MERGE_MARK_REG     (RD_MERGE_MARK_REG)
    ) u_rd_ring (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .alloc_valid_i   (ar_push_valid_o && rd_cam_ins_ready_i),
        .alloc_ready_o   (rt_alloc_ready_o),
        .alloc_ticket_o  (rt_alloc_ticket_o),
        .alloc_merge_i   (rt_alloc_merge_i),
        .alloc_src_i     (rt_alloc_src_i),
        .issue_valid_i   (rd_iss_valid_i),
        .issue_ready_o   (rd_iss_ready_o),
        .issue_ticket_i  (rd_iss_ticket_i),
        .dfi_ret_valid_i (rd_dfi_ret_valid_i),
        .dfi_ret_ready_o (rd_dfi_ret_ready_o),
        .dfi_ret_data_i  (rd_dfi_ret_data_i),
        .dfi_ret_resp_i  (rd_dfi_ret_resp_i),
        .dfi_ret_last_i  (rd_dfi_ret_last_i),
        .drain_valid_o   (drain_valid),
        .drain_ready_i   (drain_ready),
        .drain_data_o    (drain_data),
        .drain_resp_o    (drain_resp),
        .drain_last_o    (drain_last),
        .occ_o           (),
        .busy_o          (w_rdr_busy)
    );

    assign busy_o = w_wri_busy || w_rdi_busy || w_rdr_busy;

endmodule : mc_axi4_plane
