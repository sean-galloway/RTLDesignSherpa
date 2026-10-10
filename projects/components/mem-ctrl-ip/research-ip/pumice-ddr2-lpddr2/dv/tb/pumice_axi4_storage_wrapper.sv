// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_axi4_storage_wrapper
// Purpose: Test wrapper that re-assembles mc_axi4_layer + mc_storage_layer
//          so the legacy test_pumice_axi4_layer.py can exercise the split
//          stack with no TB changes. Bit-identical to the pre-extraction
//          monolithic mc_axi4_layer.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_axi4_storage_wrapper #(
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
    parameter int BG_WIDTH = 1,
    parameter bit HAS_BG   = 0,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,
    parameter int N_SCHED_LU      = 4,
    parameter int AGE_WIDTH       = 16,
    parameter int RD_RET_DEPTH    = 32,

    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int UW   = AXI_USER_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int DRAM_BURST_BYTES = AXI_BEATS_PER_BURST * (DRAM_BEAT_WIDTH / 8)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    input  logic [4:0]               bank_lsb_i,
    input  logic                     hash_en_i,
    input  logic [7:0]               hash_seed_i,

    // Host AXI4 (same as mc_axi4_layer)
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

    // Scheduler + DFI-return ports (same as legacy mc_axi4_layer)
    output logic [NUM_ENTRIES-1:0]              wr_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              wr_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            wr_sch_qos_o,
    output logic [15:0]                         wr_sch_head_rel_o,
    input  logic                          wr_commit_valid_i,
    output logic                          wr_commit_ready_o,
    input  logic [PTRW-1:0]               wr_commit_slot_i,
    output logic                          wr_cm_rd_valid_o,
    input  logic                          wr_cm_rd_ready_i,
    output logic [DW-1:0]                 wr_cm_rd_data_o,
    output logic [SW-1:0]                 wr_cm_rd_strb_o,
    output logic                          wr_cm_rd_last_o,

    output logic [NUM_ENTRIES-1:0]              rd_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              rd_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            rd_sch_qos_o,
    output logic [15:0]                         rd_sch_head_rel_o,
    input  logic [7:0]                          sched_age_thresh_i,
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

    // Inter-layer nets
    logic                aw_push_valid, aw_push_ready;
    logic [BKW-1:0]      aw_push_bank;  logic [ROW_WIDTH-1:0] aw_push_row;
    logic [COL_WIDTH-1:0] aw_push_col;  logic [IW-1:0]        aw_push_id;
    logic                aw_push_agg,   aw_push_last;
    logic                wd_valid, wd_ready, wd_last;
    logic [DW-1:0]       wd_data;       logic [SW-1:0]        wd_strb;
    logic                wr_done_valid; logic [IW-1:0]        wr_done_id;

    logic                snarf_probe_valid, snarf_hit, snarf_accept;
    logic [BKW-1:0]      snarf_bank;    logic [ROW_WIDTH-1:0] snarf_row;
    logic [COL_WIDTH-1:0] snarf_col;
    logic [IW-1:0]       snarf_id;      logic [7:0]           snarf_len;
    logic                snarf_rd_valid, snarf_rd_ready, snarf_rd_last;
    logic [DW-1:0]       snarf_rd_data;
    logic                ar_push_valid, ar_push_ready;
    logic                rt_alloc_ready, rd_cam_ins_ready;
    logic [$clog2(RD_RET_DEPTH)-1:0] rt_alloc_ticket, rd_iss_ticket;
    logic                rd_iss_valid, rd_iss_ready;
    logic [BKW-1:0]      ar_push_bank;  logic [ROW_WIDTH-1:0] ar_push_row;
    logic [COL_WIDTH-1:0] ar_push_col;  logic [IW-1:0]        ar_push_id;
    logic [3:0]           ar_push_qos;   logic [3:0]           aw_push_qos;

    logic w_axi_busy, w_storage_busy;

    mc_axi4_layer #(
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH  (DRAM_BEAT_WIDTH),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .BG_WIDTH         (BG_WIDTH),
        .HAS_BG           (HAS_BG),
        .AXI_BEATS_PER_BURST   (AXI_BEATS_PER_BURST),
        .NUM_ENTRIES      (NUM_ENTRIES),
        .N_SRAM_SLOTS     (N_SRAM_SLOTS),
        .RD_RET_DEPTH     (RD_RET_DEPTH),
        .N_SCHED_LU       (N_SCHED_LU),
        .AGE_WIDTH        (AGE_WIDTH)
    ) u_axi4 (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .bank_lsb_i    (bank_lsb_i),
        .hash_en_i     (hash_en_i),
        .hash_seed_i   (hash_seed_i),
        .s_axi_awid    (s_axi_awid),
        .s_axi_awaddr  (s_axi_awaddr),
        .s_axi_awlen   (s_axi_awlen),
        .s_axi_awsize  (s_axi_awsize),
        .s_axi_awburst (s_axi_awburst),
        .s_axi_awlock  (s_axi_awlock),
        .s_axi_awcache (s_axi_awcache),
        .s_axi_awprot  (s_axi_awprot),
        .s_axi_awqos   (s_axi_awqos),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awuser  (s_axi_awuser),
        .s_axi_awvalid (s_axi_awvalid),
        .s_axi_awready (s_axi_awready),
        .s_axi_wdata   (s_axi_wdata),
        .s_axi_wstrb   (s_axi_wstrb),
        .s_axi_wlast   (s_axi_wlast),
        .s_axi_wuser   (s_axi_wuser),
        .s_axi_wvalid  (s_axi_wvalid),
        .s_axi_wready  (s_axi_wready),
        .s_axi_bid     (s_axi_bid),
        .s_axi_bresp   (s_axi_bresp),
        .s_axi_buser   (s_axi_buser),
        .s_axi_bvalid  (s_axi_bvalid),
        .s_axi_bready  (s_axi_bready),
        .s_axi_arid    (s_axi_arid),
        .s_axi_araddr  (s_axi_araddr),
        .s_axi_arlen   (s_axi_arlen),
        .s_axi_arsize  (s_axi_arsize),
        .s_axi_arburst (s_axi_arburst),
        .s_axi_arlock  (s_axi_arlock),
        .s_axi_arcache (s_axi_arcache),
        .s_axi_arprot  (s_axi_arprot),
        .s_axi_arqos   (s_axi_arqos),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_aruser  (s_axi_aruser),
        .s_axi_arvalid (s_axi_arvalid),
        .s_axi_arready (s_axi_arready),
        .s_axi_rid     (s_axi_rid),
        .s_axi_rdata   (s_axi_rdata),
        .s_axi_rresp   (s_axi_rresp),
        .s_axi_rlast   (s_axi_rlast),
        .s_axi_ruser   (s_axi_ruser),
        .s_axi_rvalid  (s_axi_rvalid),
        .s_axi_rready  (s_axi_rready),
        // storage seam
        .aw_push_valid_o    (aw_push_valid),
        .aw_push_ready_i    (aw_push_ready),
        .aw_push_bank_o     (aw_push_bank),
        .aw_push_row_o      (aw_push_row),
        .aw_push_col_o      (aw_push_col),
        .aw_push_id_o       (aw_push_id),
        .aw_push_qos_o      (aw_push_qos),
        .aw_push_agg_o      (aw_push_agg),
        .aw_push_last_o     (aw_push_last),
        .wd_valid_o         (wd_valid),
        .wd_ready_i         (wd_ready),
        .wd_data_o          (wd_data),
        .wd_strb_o          (wd_strb),
        .wd_last_o          (wd_last),
        .wr_done_valid_i    (wr_done_valid),
        .wr_done_id_i       (wr_done_id),
        .snarf_probe_valid_o(snarf_probe_valid),
        .snarf_probe_bank_o (snarf_bank),
        .snarf_probe_row_o  (snarf_row),
        .snarf_probe_col_o  (snarf_col),
        .snarf_probe_id_o   (snarf_id),
        .snarf_probe_len_o  (snarf_len),
        .snarf_hit_i        (snarf_hit),
        .snarf_accept_o     (snarf_accept),
        .snarf_rd_valid_i   (snarf_rd_valid),
        .snarf_rd_ready_o   (snarf_rd_ready),
        .snarf_rd_data_i    (snarf_rd_data),
        .snarf_rd_last_i    (snarf_rd_last),
        .ar_push_valid_o    (ar_push_valid),
        .ar_push_ready_i    (ar_push_ready),
        .ar_push_bank_o     (ar_push_bank),
        .ar_push_row_o      (ar_push_row),
        .ar_push_col_o      (ar_push_col),
        .ar_push_id_o       (ar_push_id),
        .ar_push_qos_o      (ar_push_qos),
        .rt_alloc_ready_o   (rt_alloc_ready),
        .rt_alloc_ticket_o  (rt_alloc_ticket),
        .rd_iss_ready_o     (rd_iss_ready),
        .rd_iss_valid_i     (rd_iss_valid),
        .rd_iss_ticket_i    (rd_iss_ticket),
        .rd_cam_ins_ready_i (rd_cam_ins_ready),
        .rd_dfi_ret_valid_i (rd_dfi_ret_valid_i),
        .rd_dfi_ret_ready_o (rd_dfi_ret_ready_o),
        .rd_dfi_ret_data_i  (rd_dfi_ret_data_i),
        .rd_dfi_ret_resp_i  (rd_dfi_ret_resp_i),
        .rd_dfi_ret_last_i  (rd_dfi_ret_last_i),
        .busy_o             (w_axi_busy)
    );

    mc_storage_layer #(
        .AXI_ID_WIDTH  (IW),
        .AXI_DATA_WIDTH(DW),
        .NUM_RANKS     (NUM_RANKS),
        .NUM_BANKS     (NUM_BANKS),
        .ROW_WIDTH     (ROW_WIDTH),
        .COL_WIDTH     (COL_WIDTH),
        .AXI_BEATS_PER_BURST   (AXI_BEATS_PER_BURST),
        .NUM_ENTRIES   (NUM_ENTRIES),
        .N_SRAM_SLOTS  (N_SRAM_SLOTS),
        .N_SCHED_LU    (N_SCHED_LU),
        .AGE_WIDTH     (AGE_WIDTH),
        .RD_RET_DEPTH  (RD_RET_DEPTH)
    ) u_storage (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .aw_push_valid_i    (aw_push_valid),
        .aw_push_ready_o    (aw_push_ready),
        .aw_push_bank_i     (aw_push_bank),
        .aw_push_row_i      (aw_push_row),
        .aw_push_col_i      (aw_push_col),
        .aw_push_id_i       (aw_push_id),
        .aw_push_qos_i      (aw_push_qos),
        .aw_push_agg_i      (aw_push_agg),
        .aw_push_last_i     (aw_push_last),
        .wd_valid_i         (wd_valid),
        .wd_ready_o         (wd_ready),
        .wd_data_i          (wd_data),
        .wd_strb_i          (wd_strb),
        .wd_last_i          (wd_last),
        .wr_done_valid_o    (wr_done_valid),
        .wr_done_id_o       (wr_done_id),
        .snarf_probe_valid_i(snarf_probe_valid),
        .snarf_probe_bank_i (snarf_bank),
        .snarf_probe_row_i  (snarf_row),
        .snarf_probe_col_i  (snarf_col),
        .snarf_probe_id_i   (snarf_id),
        .snarf_probe_len_i  (snarf_len),
        .snarf_hit_o        (snarf_hit),
        .snarf_accept_i     (snarf_accept),
        .snarf_rd_valid_o   (snarf_rd_valid),
        .snarf_rd_ready_i   (snarf_rd_ready),
        .snarf_rd_data_o    (snarf_rd_data),
        .snarf_rd_last_o    (snarf_rd_last),
        .ar_push_valid_i    (ar_push_valid),
        .ar_push_ready_o    (ar_push_ready),
        .ar_push_bank_i     (ar_push_bank),
        .ar_push_row_i      (ar_push_row),
        .ar_push_col_i      (ar_push_col),
        .ar_push_id_i       (ar_push_id),
        .ar_push_qos_i      (ar_push_qos),
        .rt_alloc_ready_i   (rt_alloc_ready),
        .rt_alloc_ticket_i  (rt_alloc_ticket),
        .rd_iss_ready_i     (rd_iss_ready),
        .rd_iss_valid_o     (rd_iss_valid),
        .rd_iss_ticket_o    (rd_iss_ticket),
        .rd_cam_ins_ready_o (rd_cam_ins_ready),
        .sched_age_thresh_i (sched_age_thresh_i),
        .wr_commit_valid_i  (wr_commit_valid_i),
        .wr_commit_ready_o  (wr_commit_ready_o),
        .wr_commit_slot_i   (wr_commit_slot_i),
        .rd_issue_valid_i   (rd_issue_valid_i),
        .rd_issue_ready_o   (rd_issue_ready_o),
        .rd_issue_slot_i    (rd_issue_slot_i),
        .wr_sch_valid_o     (wr_sch_valid_o),
        .wr_sch_bank_o      (wr_sch_bank_o),
        .wr_sch_row_o       (wr_sch_row_o),
        .wr_sch_col_o       (wr_sch_col_o),
        .wr_sch_older_o     (wr_sch_older_o),
        .wr_sch_age_exceed_o(wr_sch_age_exceed_o),
        .wr_sch_qos_o       (wr_sch_qos_o),
        .wr_sch_head_rel_o  (wr_sch_head_rel_o),
        .rd_sch_valid_o     (rd_sch_valid_o),
        .rd_sch_bank_o      (rd_sch_bank_o),
        .rd_sch_row_o       (rd_sch_row_o),
        .rd_sch_col_o       (rd_sch_col_o),
        .rd_sch_older_o     (rd_sch_older_o),
        .rd_sch_age_exceed_o(rd_sch_age_exceed_o),
        .rd_sch_qos_o       (rd_sch_qos_o),
        .rd_sch_head_rel_o  (rd_sch_head_rel_o),
        .wr_cm_rd_valid_o   (wr_cm_rd_valid_o),
        .wr_cm_rd_ready_i   (wr_cm_rd_ready_i),
        .wr_cm_rd_data_o    (wr_cm_rd_data_o),
        .wr_cm_rd_strb_o    (wr_cm_rd_strb_o),
        .wr_cm_rd_last_o    (wr_cm_rd_last_o),
        .busy_o             (w_storage_busy)
    );

    assign busy_o = w_axi_busy || w_storage_busy;

endmodule : pumice_axi4_storage_wrapper
