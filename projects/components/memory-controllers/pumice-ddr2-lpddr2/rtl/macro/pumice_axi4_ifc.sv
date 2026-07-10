// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_axi4_ifc
// Purpose: The pumice AXI4 host interface. Bolts the common AXI burst
//          splitters onto the front of the dumb wr/rd intakes, and holds the
//          wr-data CAM (write buffer + snarf source) and rd-cmd CAM (read
//          reorder buffer). Presents the host AXI4 face and exposes the
//          scheduler + DFI-data ports outward.
//
//   host AXI4 -> [wr/rd splitter] -> pumice_wr_intake -> pumice_wr_data_cam
//                                 -> pumice_rd_intake -> pumice_rd_cmd_cam
//   snarf: rd_intake probes wr CAM; hit -> streamed from wr CAM SRAM.
//   external: scheduler lookup/oldest/commit(issue) ports on both CAMs,
//             wr commit-data out (to wr_beat_sequencer), rd DFI-return in.
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_axi4_ifc #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int DRAM_BEAT_WIDTH   = 64,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BYTE_OFFSET_WIDTH = 3,
    parameter bit SYNTH_ROW_MAJOR       = 1'b1,
    parameter bit SYNTH_BANK_INTERLEAVE = 1'b1,
    parameter bit SYNTH_XOR_HASH        = 1'b0,
    parameter int BL              = 4,
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SRAM_SLOTS    = 8,
    parameter int N_SCHED_LU      = 4,
    parameter int AGE_WIDTH       = 16,

    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int UW   = AXI_USER_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    // Split each host burst at DRAM-burst-byte boundaries -> 1 DRAM burst each.
    parameter int DRAM_BURST_BYTES = BL * (DRAM_BEAT_WIDTH / 8)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    input  pumice_pkg::addr_map_scheme_e scheme_active_i,
    input  logic [7:0]               xor_seed_i,

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
    // WR CAM scheduler + commit-data ports (to scheduler / wr_beat_sequencer)
    //=========================================================================
    output logic                          wr_oldest_valid_o,
    output logic [BKW-1:0]                wr_oldest_bank_o,
    output logic [ROW_WIDTH-1:0]          wr_oldest_row_o,
    output logic [COL_WIDTH-1:0]          wr_oldest_col_o,
    output logic [IW-1:0]                 wr_oldest_id_o,
    output logic [PTRW-1:0]               wr_oldest_slot_o,
    input  logic [N_SCHED_LU-1:0]             wr_sched_lu_valid_i,
    input  logic [N_SCHED_LU*BKW-1:0]         wr_sched_lu_bank_i,
    input  logic [N_SCHED_LU*ROW_WIDTH-1:0]   wr_sched_lu_row_i,
    output logic [N_SCHED_LU-1:0]             wr_sched_lu_hit_o,
    output logic [N_SCHED_LU*PTRW-1:0]        wr_sched_lu_slot_o,
    output logic [N_SCHED_LU*COL_WIDTH-1:0]   wr_sched_lu_col_o,
    output logic [N_SCHED_LU*IW-1:0]          wr_sched_lu_id_o,
    output logic [N_SCHED_LU*AGE_WIDTH-1:0]   wr_sched_lu_age_o,
    input  logic                          wr_commit_valid_i,
    output logic                          wr_commit_ready_o,
    input  logic [PTRW-1:0]               wr_commit_slot_i,
    output logic                          wr_cm_rd_valid_o,
    input  logic                          wr_cm_rd_ready_i,
    output logic [DW-1:0]                 wr_cm_rd_data_o,
    output logic [SW-1:0]                 wr_cm_rd_strb_o,
    output logic                          wr_cm_rd_last_o,

    //=========================================================================
    // RD CAM scheduler + DFI-return ports (to scheduler / DFI read path)
    //=========================================================================
    output logic                          rd_oldest_valid_o,
    output logic [BKW-1:0]                rd_oldest_bank_o,
    output logic [ROW_WIDTH-1:0]          rd_oldest_row_o,
    output logic [COL_WIDTH-1:0]          rd_oldest_col_o,
    output logic [IW-1:0]                 rd_oldest_id_o,
    output logic [PTRW-1:0]               rd_oldest_slot_o,
    input  logic [N_SCHED_LU-1:0]             rd_sched_lu_valid_i,
    input  logic [N_SCHED_LU*BKW-1:0]         rd_sched_lu_bank_i,
    input  logic [N_SCHED_LU*ROW_WIDTH-1:0]   rd_sched_lu_row_i,
    output logic [N_SCHED_LU-1:0]             rd_sched_lu_hit_o,
    output logic [N_SCHED_LU*PTRW-1:0]        rd_sched_lu_slot_o,
    output logic [N_SCHED_LU*COL_WIDTH-1:0]   rd_sched_lu_col_o,
    output logic [N_SCHED_LU*IW-1:0]          rd_sched_lu_id_o,
    output logic [N_SCHED_LU*AGE_WIDTH-1:0]   rd_sched_lu_age_o,
    input  logic                          rd_issue_valid_i,
    output logic                          rd_issue_ready_o,
    input  logic [PTRW-1:0]               rd_issue_slot_i,
    input  logic                          rd_dfi_ret_valid_i,
    output logic                          rd_dfi_ret_ready_o,
    input  logic [DW-1:0]                 rd_dfi_ret_data_i,
    input  logic [1:0]                    rd_dfi_ret_resp_i,
    input  logic                          rd_dfi_ret_last_i,

    output logic                          busy_o
);

    import pumice_pkg::*;

    localparam logic [11:0] ALIGN_MASK = 12'(DRAM_BURST_BYTES - 1);

    // ======================================================================
    // Split -> intake AXI nets
    // ======================================================================
    logic [IW-1:0] sw_awid;   logic [AW-1:0] sw_awaddr;  logic [7:0] sw_awlen;
    logic [2:0]    sw_awsize; logic [1:0]    sw_awburst; logic       sw_awlock;
    logic [3:0]    sw_awcache;logic [2:0]    sw_awprot;  logic [3:0] sw_awqos;
    logic [3:0]    sw_awregion;logic [UW-1:0] sw_awuser; logic       sw_awvalid, sw_awready;
    logic [DW-1:0] sw_wdata;  logic [SW-1:0] sw_wstrb;   logic sw_wlast;
    logic [UW-1:0] sw_wuser;  logic          sw_wvalid,  sw_wready;
    logic [IW-1:0] sw_bid;    logic [1:0]    sw_bresp;   logic [UW-1:0] sw_buser;
    logic          sw_bvalid, sw_bready;

    logic [IW-1:0] sr_arid;   logic [AW-1:0] sr_araddr;  logic [7:0] sr_arlen;
    logic [2:0]    sr_arsize; logic [1:0]    sr_arburst; logic       sr_arlock;
    logic [3:0]    sr_arcache;logic [2:0]    sr_arprot;  logic [3:0] sr_arqos;
    logic [3:0]    sr_arregion;logic [UW-1:0] sr_aruser; logic       sr_arvalid, sr_arready;
    logic [IW-1:0] sr_rid;    logic [DW-1:0] sr_rdata;   logic [1:0] sr_rresp;
    logic          sr_rlast;  logic [UW-1:0] sr_ruser;   logic sr_rvalid, sr_rready;

    axi_master_wr_splitter #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW)
    ) u_wr_split (
        .aclk(aclk), .aresetn(aresetn), .alignment_mask(ALIGN_MASK), .block_ready(1'b0),
        .fub_awid(s_axi_awid), .fub_awaddr(s_axi_awaddr), .fub_awlen(s_axi_awlen),
        .fub_awsize(s_axi_awsize), .fub_awburst(s_axi_awburst), .fub_awlock(s_axi_awlock),
        .fub_awcache(s_axi_awcache), .fub_awprot(s_axi_awprot), .fub_awqos(s_axi_awqos),
        .fub_awregion(s_axi_awregion), .fub_awuser(s_axi_awuser),
        .fub_awvalid(s_axi_awvalid), .fub_awready(s_axi_awready),
        .fub_wdata(s_axi_wdata), .fub_wstrb(s_axi_wstrb), .fub_wlast(s_axi_wlast),
        .fub_wuser(s_axi_wuser), .fub_wvalid(s_axi_wvalid), .fub_wready(s_axi_wready),
        .fub_bid(s_axi_bid), .fub_bresp(s_axi_bresp), .fub_buser(s_axi_buser),
        .fub_bvalid(s_axi_bvalid), .fub_bready(s_axi_bready),
        .fub_split_addr(), .fub_split_id(), .fub_split_cnt(), .fub_split_valid(),
        .fub_split_ready(1'b1),
        .m_axi_awid(sw_awid), .m_axi_awaddr(sw_awaddr), .m_axi_awlen(sw_awlen),
        .m_axi_awsize(sw_awsize), .m_axi_awburst(sw_awburst), .m_axi_awlock(sw_awlock),
        .m_axi_awcache(sw_awcache), .m_axi_awprot(sw_awprot), .m_axi_awqos(sw_awqos),
        .m_axi_awregion(sw_awregion), .m_axi_awuser(sw_awuser),
        .m_axi_awvalid(sw_awvalid), .m_axi_awready(sw_awready),
        .m_axi_wdata(sw_wdata), .m_axi_wstrb(sw_wstrb), .m_axi_wlast(sw_wlast),
        .m_axi_wuser(sw_wuser), .m_axi_wvalid(sw_wvalid), .m_axi_wready(sw_wready),
        .m_axi_bid(sw_bid), .m_axi_bresp(sw_bresp), .m_axi_buser(sw_buser),
        .m_axi_bvalid(sw_bvalid), .m_axi_bready(sw_bready)
    );

    axi_master_rd_splitter #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW)
    ) u_rd_split (
        .aclk(aclk), .aresetn(aresetn), .alignment_mask(ALIGN_MASK), .block_ready(1'b0),
        .fub_arid(s_axi_arid), .fub_araddr(s_axi_araddr), .fub_arlen(s_axi_arlen),
        .fub_arsize(s_axi_arsize), .fub_arburst(s_axi_arburst), .fub_arlock(s_axi_arlock),
        .fub_arcache(s_axi_arcache), .fub_arprot(s_axi_arprot), .fub_arqos(s_axi_arqos),
        .fub_arregion(s_axi_arregion), .fub_aruser(s_axi_aruser),
        .fub_arvalid(s_axi_arvalid), .fub_arready(s_axi_arready),
        .fub_rid(s_axi_rid), .fub_rdata(s_axi_rdata), .fub_rresp(s_axi_rresp),
        .fub_rlast(s_axi_rlast), .fub_ruser(s_axi_ruser),
        .fub_rvalid(s_axi_rvalid), .fub_rready(s_axi_rready),
        .fub_split_addr(), .fub_split_id(), .fub_split_cnt(), .fub_split_valid(),
        .fub_split_ready(1'b1),
        .m_axi_arid(sr_arid), .m_axi_araddr(sr_araddr), .m_axi_arlen(sr_arlen),
        .m_axi_arsize(sr_arsize), .m_axi_arburst(sr_arburst), .m_axi_arlock(sr_arlock),
        .m_axi_arcache(sr_arcache), .m_axi_arprot(sr_arprot), .m_axi_arqos(sr_arqos),
        .m_axi_arregion(sr_arregion), .m_axi_aruser(sr_aruser),
        .m_axi_arvalid(sr_arvalid), .m_axi_arready(sr_arready),
        .m_axi_rid(sr_rid), .m_axi_rdata(sr_rdata), .m_axi_rresp(sr_rresp),
        .m_axi_rlast(sr_rlast), .m_axi_ruser(sr_ruser),
        .m_axi_rvalid(sr_rvalid), .m_axi_rready(sr_rready)
    );

    // ======================================================================
    // intake <-> CAM nets
    // ======================================================================
    // wr_intake -> wr_cam
    logic                aw_push_valid, aw_push_ready;
    logic [BKW-1:0]      aw_push_bank;  logic [ROW_WIDTH-1:0] aw_push_row;
    logic [COL_WIDTH-1:0] aw_push_col;  logic [IW-1:0]        aw_push_id;
    logic                wd_valid, wd_ready, wd_last;
    logic [DW-1:0]       wd_data;       logic [SW-1:0]        wd_strb;
    logic                wr_done_valid; logic [IW-1:0]        wr_done_id;

    // rd_intake <-> wr_cam (snarf) and rd_cam
    logic                snarf_probe_valid, snarf_hit, snarf_accept;
    logic [BKW-1:0]      snarf_bank;    logic [ROW_WIDTH-1:0] snarf_row;
    logic [COL_WIDTH-1:0] snarf_col;
    logic                snarf_rd_valid, snarf_rd_ready, snarf_rd_last;
    logic [DW-1:0]       snarf_rd_data;
    logic                ar_push_valid, ar_push_ready;
    logic [BKW-1:0]      ar_push_bank;  logic [ROW_WIDTH-1:0] ar_push_row;
    logic [COL_WIDTH-1:0] ar_push_col;  logic [IW-1:0]        ar_push_id;
    logic                drain_valid, drain_ready, drain_last;
    logic [DW-1:0]       drain_data;    logic [1:0]           drain_resp;

    logic w_wri_busy, w_rdi_busy, w_wrc_busy, w_rdc_busy;

    // ---- WR intake ----
    pumice_wr_intake #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH), .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .SYNTH_ROW_MAJOR(SYNTH_ROW_MAJOR), .SYNTH_BANK_INTERLEAVE(SYNTH_BANK_INTERLEAVE),
        .SYNTH_XOR_HASH(SYNTH_XOR_HASH), .BL(BL)
    ) u_wr_intake (
        .aclk(aclk), .aresetn(aresetn),
        .scheme_active_i(scheme_active_i), .xor_seed_i(xor_seed_i),
        .s_axi_awid(sw_awid), .s_axi_awaddr(sw_awaddr), .s_axi_awlen(sw_awlen),
        .s_axi_awsize(sw_awsize), .s_axi_awburst(sw_awburst), .s_axi_awlock(sw_awlock),
        .s_axi_awcache(sw_awcache), .s_axi_awprot(sw_awprot), .s_axi_awqos(sw_awqos),
        .s_axi_awregion(sw_awregion), .s_axi_awuser(sw_awuser),
        .s_axi_awvalid(sw_awvalid), .s_axi_awready(sw_awready),
        .s_axi_wdata(sw_wdata), .s_axi_wstrb(sw_wstrb), .s_axi_wlast(sw_wlast),
        .s_axi_wuser(sw_wuser), .s_axi_wvalid(sw_wvalid), .s_axi_wready(sw_wready),
        .s_axi_bid(sw_bid), .s_axi_bresp(sw_bresp), .s_axi_buser(sw_buser),
        .s_axi_bvalid(sw_bvalid), .s_axi_bready(sw_bready),
        .aw_push_valid_o(aw_push_valid), .aw_push_ready_i(aw_push_ready),
        .aw_push_rank_o(), .aw_push_bank_o(aw_push_bank), .aw_push_row_o(aw_push_row),
        .aw_push_col_o(aw_push_col), .aw_push_id_o(aw_push_id), .aw_push_err_o(),
        .wdata_valid_o(wd_valid), .wdata_ready_i(wd_ready),
        .wdata_o(wd_data), .wstrb_o(wd_strb), .wlast_o(wd_last),
        .wr_done_valid_i(wr_done_valid), .wr_done_id_i(wr_done_id), .wr_done_resp_i(2'b00),
        .busy_o(w_wri_busy)
    );

    // ---- WR data CAM ----
    pumice_wr_data_cam #(
        .NUM_ENTRIES(NUM_ENTRIES), .N_SCHED_LU(N_SCHED_LU), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .AXI_ID_WIDTH(IW),
        .AXI_DATA_WIDTH(DW), .BL(BL), .AGE_WIDTH(AGE_WIDTH), .N_SRAM_SLOTS(N_SRAM_SLOTS)
    ) u_wr_cam (
        .aclk(aclk), .aresetn(aresetn),
        .ins_valid_i(aw_push_valid), .ins_ready_o(aw_push_ready),
        .ins_bank_i(aw_push_bank), .ins_row_i(aw_push_row),
        .ins_col_i(aw_push_col), .ins_id_i(aw_push_id),
        .wd_valid_i(wd_valid), .wd_ready_o(wd_ready),
        .wd_data_i(wd_data), .wd_strb_i(wd_strb), .wd_last_i(wd_last),
        .snarf_probe_valid_i(snarf_probe_valid), .snarf_probe_bank_i(snarf_bank),
        .snarf_probe_row_i(snarf_row), .snarf_probe_col_i(snarf_col),
        .snarf_hit_o(snarf_hit), .snarf_accept_i(snarf_accept),
        .snarf_rd_valid_o(snarf_rd_valid), .snarf_rd_ready_i(snarf_rd_ready),
        .snarf_rd_data_o(snarf_rd_data), .snarf_rd_last_o(snarf_rd_last),
        .oldest_valid_o(wr_oldest_valid_o), .oldest_bank_o(wr_oldest_bank_o),
        .oldest_row_o(wr_oldest_row_o), .oldest_col_o(wr_oldest_col_o),
        .oldest_id_o(wr_oldest_id_o), .oldest_slot_o(wr_oldest_slot_o),
        .sched_lu_valid_i(wr_sched_lu_valid_i), .sched_lu_bank_i(wr_sched_lu_bank_i),
        .sched_lu_row_i(wr_sched_lu_row_i), .sched_lu_hit_o(wr_sched_lu_hit_o),
        .sched_lu_slot_o(wr_sched_lu_slot_o), .sched_lu_col_o(wr_sched_lu_col_o),
        .sched_lu_id_o(wr_sched_lu_id_o), .sched_lu_age_o(wr_sched_lu_age_o),
        .commit_valid_i(wr_commit_valid_i), .commit_ready_o(wr_commit_ready_o),
        .commit_slot_i(wr_commit_slot_i),
        .cm_rd_valid_o(wr_cm_rd_valid_o), .cm_rd_ready_i(wr_cm_rd_ready_i),
        .cm_rd_data_o(wr_cm_rd_data_o), .cm_rd_strb_o(wr_cm_rd_strb_o),
        .cm_rd_last_o(wr_cm_rd_last_o),
        .commit_done_valid_o(wr_done_valid), .commit_done_id_o(wr_done_id),
        .busy_o(w_wrc_busy)
    );

    // ---- RD intake ----
    pumice_rd_intake #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH), .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .SYNTH_ROW_MAJOR(SYNTH_ROW_MAJOR), .SYNTH_BANK_INTERLEAVE(SYNTH_BANK_INTERLEAVE),
        .SYNTH_XOR_HASH(SYNTH_XOR_HASH), .BL(BL)
    ) u_rd_intake (
        .aclk(aclk), .aresetn(aresetn),
        .scheme_active_i(scheme_active_i), .xor_seed_i(xor_seed_i),
        .s_axi_arid(sr_arid), .s_axi_araddr(sr_araddr), .s_axi_arlen(sr_arlen),
        .s_axi_arsize(sr_arsize), .s_axi_arburst(sr_arburst), .s_axi_arlock(sr_arlock),
        .s_axi_arcache(sr_arcache), .s_axi_arprot(sr_arprot), .s_axi_arqos(sr_arqos),
        .s_axi_arregion(sr_arregion), .s_axi_aruser(sr_aruser),
        .s_axi_arvalid(sr_arvalid), .s_axi_arready(sr_arready),
        .s_axi_rid(sr_rid), .s_axi_rdata(sr_rdata), .s_axi_rresp(sr_rresp),
        .s_axi_rlast(sr_rlast), .s_axi_ruser(sr_ruser),
        .s_axi_rvalid(sr_rvalid), .s_axi_rready(sr_rready),
        .ar_push_valid_o(ar_push_valid), .ar_push_ready_i(ar_push_ready),
        .ar_push_rank_o(), .ar_push_bank_o(ar_push_bank), .ar_push_row_o(ar_push_row),
        .ar_push_col_o(ar_push_col), .ar_push_id_o(ar_push_id),
        .snarf_probe_valid_o(snarf_probe_valid), .snarf_probe_rank_o(),
        .snarf_probe_bank_o(snarf_bank), .snarf_probe_row_o(snarf_row),
        .snarf_probe_col_o(snarf_col), .snarf_hit_i(snarf_hit),
        .snarf_accept_o(snarf_accept),
        .snarf_rd_valid_i(snarf_rd_valid), .snarf_rd_ready_o(snarf_rd_ready),
        .snarf_rd_data_i(snarf_rd_data), .snarf_rd_last_i(snarf_rd_last),
        .dfi_rd_valid_i(drain_valid), .dfi_rd_ready_o(drain_ready),
        .dfi_rd_data_i(drain_data), .dfi_rd_last_i(drain_last), .dfi_rd_resp_i(drain_resp),
        .busy_o(w_rdi_busy)
    );

    // ---- RD cmd CAM ----
    pumice_rd_cmd_cam #(
        .NUM_ENTRIES(NUM_ENTRIES), .N_SCHED_LU(N_SCHED_LU), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .AXI_ID_WIDTH(IW),
        .AXI_DATA_WIDTH(DW), .BL(BL), .AGE_WIDTH(AGE_WIDTH), .N_SRAM_SLOTS(N_SRAM_SLOTS)
    ) u_rd_cam (
        .aclk(aclk), .aresetn(aresetn),
        .ins_valid_i(ar_push_valid), .ins_ready_o(ar_push_ready),
        .ins_bank_i(ar_push_bank), .ins_row_i(ar_push_row),
        .ins_col_i(ar_push_col), .ins_id_i(ar_push_id),
        .sched_lu_valid_i(rd_sched_lu_valid_i), .sched_lu_bank_i(rd_sched_lu_bank_i),
        .sched_lu_row_i(rd_sched_lu_row_i), .sched_lu_hit_o(rd_sched_lu_hit_o),
        .sched_lu_slot_o(rd_sched_lu_slot_o), .sched_lu_col_o(rd_sched_lu_col_o),
        .sched_lu_id_o(rd_sched_lu_id_o), .sched_lu_age_o(rd_sched_lu_age_o),
        .oldest_valid_o(rd_oldest_valid_o), .oldest_bank_o(rd_oldest_bank_o),
        .oldest_row_o(rd_oldest_row_o), .oldest_col_o(rd_oldest_col_o),
        .oldest_id_o(rd_oldest_id_o), .oldest_slot_o(rd_oldest_slot_o),
        .issue_valid_i(rd_issue_valid_i), .issue_ready_o(rd_issue_ready_o),
        .issue_slot_i(rd_issue_slot_i),
        .dfi_ret_valid_i(rd_dfi_ret_valid_i), .dfi_ret_ready_o(rd_dfi_ret_ready_o),
        .dfi_ret_data_i(rd_dfi_ret_data_i), .dfi_ret_resp_i(rd_dfi_ret_resp_i),
        .dfi_ret_last_i(rd_dfi_ret_last_i),
        .drain_valid_o(drain_valid), .drain_ready_i(drain_ready),
        .drain_data_o(drain_data), .drain_id_o(), .drain_resp_o(drain_resp),
        .drain_last_o(drain_last),
        .busy_o(w_rdc_busy)
    );

    assign busy_o = w_wri_busy || w_rdi_busy || w_wrc_busy || w_rdc_busy;

endmodule : pumice_axi4_ifc
