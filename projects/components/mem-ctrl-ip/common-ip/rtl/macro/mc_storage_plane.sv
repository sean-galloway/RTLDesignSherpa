// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_storage_plane
// Purpose: Common storage plane for the memory-controller family. Holds the
//          wr-data CAM (write buffer + snarf source) and rd-cmd CAM (read
//          reorder buffer). Presents the scheduler-facing advisory snapshot
//          and accepts the rd-snoop probe from the upstream AXI4 plane.
//
//   upstream AXI4 plane (intakes + return ring) -> mc_storage_plane -> scheduler
//   snarf: rd_intake probe is supplied by the AXI4 plane; hit + data stream
//   are returned to the AXI4 plane for the read return path.
//
// Documentation: docs/uarch/PUMICE_AXI4_PLANE_UARCH.md (storage seam section)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_storage_plane #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,
    parameter int N_SCHED_LU      = 4,
    parameter int AGE_WIDTH       = 16,
    // Reads the controller can hold IN FLIGHT (mc_rd_return_ring DEPTH).
    // Independent of NUM_ENTRIES (the scheduling window): a read's CAM entry
    // frees at issue, its ring slot at R-drain. Power of 2.
    parameter int RD_RET_DEPTH    = 32,
    parameter bit WR_MERGE_EN     = 1'b0,  // mc_wr_data_cam MERGE_EN: write combining (pumice TASK-060)
    parameter bit RD_MERGE_EN     = 1'b0,  // mc_rd_cmd_cam MERGE_EN: read combining through the return ring (pumice TASK-060)

    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    //=========================================================================
    // WR intake -> WR data CAM
    //=========================================================================
    input  logic                aw_push_valid_i,
    output logic                aw_push_ready_o,
    input  logic [BKW-1:0]      aw_push_bank_i,
    input  logic [ROW_WIDTH-1:0]aw_push_row_i,
    input  logic [COL_WIDTH-1:0]aw_push_col_i,
    input  logic [IW-1:0]       aw_push_id_i,
    input  logic [3:0]          aw_push_qos_i,
    input  logic                aw_push_agg_i,
    input  logic                aw_push_last_i,

    input  logic                wd_valid_i,
    output logic                wd_ready_o,
    input  logic [DW-1:0]       wd_data_i,
    input  logic [SW-1:0]       wd_strb_i,
    input  logic                wd_last_i,

    // commit-done notification back to the WR intake
    output logic                wr_done_valid_o,
    output logic [IW-1:0]       wr_done_id_o,
    output logic [31:0]         stat_merge_o,      // write merges performed (free-running)
    output logic [31:0]         stat_rd_merge_o,   // read merges performed (free-running)

    //=========================================================================
    // RD intake -> WR data CAM (snarf probe / hit / data stream)
    //=========================================================================
    input  logic                snarf_probe_valid_i,
    input  logic [BKW-1:0]      snarf_probe_bank_i,
    input  logic [ROW_WIDTH-1:0]snarf_probe_row_i,
    input  logic [COL_WIDTH-1:0]snarf_probe_col_i,
    input  logic [IW-1:0]       snarf_probe_id_i,
    input  logic [7:0]          snarf_probe_len_i,
    output logic                snarf_hit_o,
    input  logic                snarf_accept_i,
    output logic                snarf_rd_valid_o,
    input  logic                snarf_rd_ready_i,
    output logic [DW-1:0]       snarf_rd_data_o,
    output logic                snarf_rd_last_o,

    //=========================================================================
    // RD intake -> RD cmd CAM
    //=========================================================================
    input  logic                ar_push_valid_i,
    output logic                ar_push_ready_o,
    input  logic [BKW-1:0]      ar_push_bank_i,
    input  logic [ROW_WIDTH-1:0]ar_push_row_i,
    input  logic [COL_WIDTH-1:0]ar_push_col_i,
    input  logic [IW-1:0]       ar_push_id_i,
    input  logic [3:0]          ar_push_qos_i,

    //=========================================================================
    // Return ring <-> RD cmd CAM
    //=========================================================================
    // Admission: a read is admitted when BOTH the CAM and the ring have room.
    input  logic                rt_alloc_ready_i,
    input  logic [$clog2(RD_RET_DEPTH)-1:0] rt_alloc_ticket_i,
    input  logic                rd_iss_ready_i,
    output logic                rd_iss_valid_o,
    output logic [$clog2(RD_RET_DEPTH)-1:0] rd_iss_ticket_o,
    output logic                rd_cam_ins_ready_o,
    // Read combining (RD_MERGE_EN): the insert this cycle rides an older live
    // read's burst; the ring allocates its ticket as a shadow of rd_ins_merge_ticket_o.
    output logic                rd_ins_merge_o,
    output logic [$clog2(RD_RET_DEPTH)-1:0] rd_ins_merge_ticket_o,

    //=========================================================================
    // Scheduler -> CAMs
    //=========================================================================
    // SCHED_POLICY.age_thresh -> both CAMs (MC cycles / 16; 0 = off)
    input  logic [7:0]          sched_age_thresh_i,

    input  logic                wr_commit_valid_i,
    output logic                wr_commit_ready_o,
    output logic                wr_commit_ready_now_o,    // the accept condition, registers only (no commit_valid term)
    input  logic [PTRW-1:0]     wr_commit_slot_i,

    input  logic                rd_issue_valid_i,
    output logic                rd_issue_ready_o,
    input  logic [PTRW-1:0]     rd_issue_slot_i,

    //=========================================================================
    // WR CAM scheduler + commit-data ports (to scheduler / wr_beat_sequencer)
    //=========================================================================
    output logic [NUM_ENTRIES-1:0]              wr_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              wr_sch_pend_o,   // allocated, data not landed (scheduler close-on-drain)
    output logic [NUM_ENTRIES-1:0]              wr_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            wr_sch_qos_o,
    output logic [15:0]                         wr_sch_head_rel_o,

    //=========================================================================
    // RD CAM scheduler ports (to scheduler)
    //=========================================================================
    output logic [NUM_ENTRIES-1:0]              rd_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              rd_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            rd_sch_qos_o,
    output logic [15:0]                         rd_sch_head_rel_o,

    //=========================================================================
    // WR commit-data out (to scheduler / wr_beat_sequencer)
    //=========================================================================
    output logic                wr_cm_rd_valid_o,
    input  logic                wr_cm_rd_ready_i,
    output logic [DW-1:0]       wr_cm_rd_data_o,
    output logic [SW-1:0]       wr_cm_rd_strb_o,
    output logic                wr_cm_rd_last_o,

    //=========================================================================
    // Per-bank head records (the storage -> scheduler plane contract).
    // REGISTERED snapshots, one cycle behind the CAM state: {head, 2nd} per
    // (direction, bank), derived from the CAMs' vectors + age matrices by
    // mc_bank_head_records. Additive beside the per-entry *_sch_* vectors
    // the FRFCFS research core still consumes.
    //=========================================================================
    // scheduler's registered row image (bank timers), for the records' hit flag
    input  logic [NUM_BANKS-1:0]                bank_row_active_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      bank_open_row_i,
    output mc_common_pkg::mc_head_rec_t [NUM_BANKS-1:0] wr_head_o,
    output mc_common_pkg::mc_head_rec_t [NUM_BANKS-1:0] wr_head2_o,
    output mc_common_pkg::mc_head_rec_t [NUM_BANKS-1:0] rd_head_o,
    output mc_common_pkg::mc_head_rec_t [NUM_BANKS-1:0] rd_head2_o,

    output logic                busy_o
);

    import mc_common_pkg::*;

    // ---- WR data CAM ----
    logic w_wrc_busy;
    logic [NUM_ENTRIES-1:0] w_wr_sch_pend;   // allocated, data not landed (records + scheduler)
    assign wr_sch_pend_o = w_wr_sch_pend;
    mc_wr_data_cam #(
        .NUM_ENTRIES   (NUM_ENTRIES),
        .N_SCHED_LU    (N_SCHED_LU),
        .NUM_BANKS     (NUM_BANKS),
        .ROW_WIDTH     (ROW_WIDTH),
        .COL_WIDTH     (COL_WIDTH),
        .AXI_ID_WIDTH  (IW),
        .AXI_DATA_WIDTH(DW),
        .AXI_BEATS_PER_BURST            (AXI_BEATS_PER_BURST),
        .AGE_WIDTH     (AGE_WIDTH),
        .N_SRAM_SLOTS  (N_SRAM_SLOTS),
        .MERGE_EN      (WR_MERGE_EN)
    ) u_wr_cam (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .ins_valid_i        (aw_push_valid_i),
        .ins_ready_o        (aw_push_ready_o),
        .ins_bank_i         (aw_push_bank_i),
        .ins_row_i          (aw_push_row_i),
        .ins_col_i          (aw_push_col_i),
        .ins_id_i           (aw_push_id_i),
        .ins_qos_i          (aw_push_qos_i),
        .ins_agg_i          (aw_push_agg_i),
        .ins_last_i         (aw_push_last_i),
        .wd_valid_i         (wd_valid_i),
        .wd_ready_o         (wd_ready_o),
        .wd_data_i          (wd_data_i),
        .wd_strb_i          (wd_strb_i),
        .wd_last_i          (wd_last_i),
        .snarf_probe_valid_i(snarf_probe_valid_i),
        .snarf_probe_bank_i (snarf_probe_bank_i),
        .snarf_probe_row_i  (snarf_probe_row_i),
        .snarf_probe_col_i  (snarf_probe_col_i),
        .snarf_probe_id_i   (snarf_probe_id_i),
        .snarf_probe_len_i  (snarf_probe_len_i),
        .snarf_hit_o        (snarf_hit_o),
        .snarf_accept_i     (snarf_accept_i),
        .snarf_rd_valid_o   (snarf_rd_valid_o),
        .snarf_rd_ready_i   (snarf_rd_ready_i),
        .snarf_rd_data_o    (snarf_rd_data_o),
        .snarf_rd_last_o    (snarf_rd_last_o),
        // legacy sched-lookup / oldest ports unused: the scheduler reads the
        // sch_* per-entry vectors and does the match/argmax itself. Tied off
        // (inputs 0, outputs open) -> pruned by synthesis.
        .oldest_valid_o     (),
        .oldest_bank_o      (),
        .oldest_row_o       (),
        .oldest_col_o       (),
        .oldest_id_o        (),
        .oldest_slot_o      (),
        .sched_lu_valid_i   ('0),
        .sched_lu_bank_i    ('0),
        .sched_lu_row_i     ('0),
        .sched_lu_hit_o     (),
        .sched_lu_slot_o    (),
        .sched_lu_col_o     (),
        .sched_lu_id_o      (),
        .sched_lu_age_o     (),
        .sch_valid_o        (wr_sch_valid_o),
        .sch_pend_o         (w_wr_sch_pend),
        .sch_bank_o         (wr_sch_bank_o),
        .sch_row_o          (wr_sch_row_o),
        .sch_col_o          (wr_sch_col_o),
        .sch_older_o        (wr_sch_older_o),
        .age_thresh_i       (sched_age_thresh_i),
        .sch_age_exceed_o   (wr_sch_age_exceed_o),
        .sch_qos_o          (wr_sch_qos_o),
        .sch_head_rel_o     (wr_sch_head_rel_o),
        .commit_valid_i     (wr_commit_valid_i),
        .commit_ready_o     (wr_commit_ready_o),
        .commit_ready_now_o (wr_commit_ready_now_o),
        .commit_slot_i      (wr_commit_slot_i),
        .cm_rd_valid_o      (wr_cm_rd_valid_o),
        .cm_rd_ready_i      (wr_cm_rd_ready_i),
        .cm_rd_data_o       (wr_cm_rd_data_o),
        .cm_rd_strb_o       (wr_cm_rd_strb_o),
        .cm_rd_last_o       (wr_cm_rd_last_o),
        .commit_done_valid_o(wr_done_valid_o),
        .commit_done_id_o   (wr_done_id_o),
        .stat_merge_o       (stat_merge_o),
        .busy_o             (w_wrc_busy)
    );

    // ---- RD cmd CAM (scheduling window) ----
    // A read is admitted when BOTH have room; the ring's tail ticket rides
    // into the CAM entry and comes back out on issue.
    assign ar_push_ready_o = rd_cam_ins_ready_o && rt_alloc_ready_i;

    logic w_rdc_busy;
    mc_rd_cmd_cam #(
        .NUM_ENTRIES   (NUM_ENTRIES),
        .N_SCHED_LU    (N_SCHED_LU),
        .NUM_BANKS     (NUM_BANKS),
        .ROW_WIDTH     (ROW_WIDTH),
        .COL_WIDTH     (COL_WIDTH),
        .AXI_ID_WIDTH  (IW),
        .AGE_WIDTH     (AGE_WIDTH),
        .RD_RET_DEPTH  (RD_RET_DEPTH),
        .MERGE_EN      (RD_MERGE_EN)
    ) u_rd_cam (
        .aclk       (aclk),
        .aresetn    (aresetn),
        .ins_valid_i(ar_push_valid_i && rt_alloc_ready_i),
        .ins_ready_o(rd_cam_ins_ready_o),
        .ins_bank_i (ar_push_bank_i),
        .ins_row_i  (ar_push_row_i),
        .ins_col_i  (ar_push_col_i),
        .ins_id_i   (ar_push_id_i),
        .ins_qos_i  (ar_push_qos_i),
        .ins_ticket_i(rt_alloc_ticket_i),
        .ins_merge_o       (rd_ins_merge_o),
        .ins_merge_ticket_o(rd_ins_merge_ticket_o),
        .stat_merge_o      (stat_rd_merge_o),
        // legacy sched-lookup / oldest ports unused (scheduler reads sch_*).
        .sched_lu_valid_i('0),
        .sched_lu_bank_i ('0),
        .sched_lu_row_i  ('0),
        .sched_lu_hit_o  (),
        .sched_lu_slot_o (),
        .sched_lu_col_o  (),
        .sched_lu_id_o   (),
        .sched_lu_age_o  (),
        .oldest_valid_o  (),
        .oldest_bank_o   (),
        .oldest_row_o    (),
        .oldest_col_o    (),
        .oldest_id_o     (),
        .oldest_slot_o   (),
        .sch_valid_o     (rd_sch_valid_o),
        .sch_bank_o      (rd_sch_bank_o),
        .sch_row_o       (rd_sch_row_o),
        .sch_col_o       (rd_sch_col_o),
        .sch_older_o     (rd_sch_older_o),
        .age_thresh_i    (sched_age_thresh_i),
        .sch_age_exceed_o(rd_sch_age_exceed_o),
        .sch_qos_o       (rd_sch_qos_o),
        .sch_head_rel_o  (rd_sch_head_rel_o),
        .issue_valid_i   (rd_issue_valid_i),
        .issue_ready_o   (rd_issue_ready_o),
        .issue_slot_i    (rd_issue_slot_i),
        .iss_valid_o     (rd_iss_valid_o),
        .iss_ready_i     (rd_iss_ready_i),
        .iss_ticket_o    (rd_iss_ticket_o),
        .busy_o          (w_rdc_busy)
    );

    // ---- per-bank head records, registered at the plane edge ----
    mc_bank_head_records #(
        .NUM_ENTRIES (NUM_ENTRIES),
        .NUM_BANKS   (NUM_BANKS),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH)
    ) u_wr_heads (
        .clk              (aclk),
        .rst_n            (aresetn),
        .bank_row_active_i(bank_row_active_i),
        .bank_open_row_i  (bank_open_row_i),
        .sch_valid_i      (wr_sch_valid_o),
        .sch_pend_i       (w_wr_sch_pend),
        .sch_bank_i       (wr_sch_bank_o),
        .sch_row_i        (wr_sch_row_o),
        .sch_col_i        (wr_sch_col_o),
        .sch_older_i      (wr_sch_older_o),
        .sch_age_exceed_i (wr_sch_age_exceed_o),
        .head_o           (wr_head_o),
        .head2_o          (wr_head2_o)
    );

    mc_bank_head_records #(
        .NUM_ENTRIES (NUM_ENTRIES),
        .NUM_BANKS   (NUM_BANKS),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH)
    ) u_rd_heads (
        .clk              (aclk),
        .rst_n            (aresetn),
        .bank_row_active_i(bank_row_active_i),
        .bank_open_row_i  (bank_open_row_i),
        .sch_valid_i      (rd_sch_valid_o),
        .sch_pend_i       ('0),                 // a read is schedulable at insert
        .sch_bank_i       (rd_sch_bank_o),
        .sch_row_i        (rd_sch_row_o),
        .sch_col_i        (rd_sch_col_o),
        .sch_older_i      (rd_sch_older_o),
        .sch_age_exceed_i (rd_sch_age_exceed_o),
        .head_o           (rd_head_o),
        .head2_o          (rd_head2_o)
    );

    assign busy_o = w_wrc_busy || w_rdc_busy;

endmodule : mc_storage_plane
