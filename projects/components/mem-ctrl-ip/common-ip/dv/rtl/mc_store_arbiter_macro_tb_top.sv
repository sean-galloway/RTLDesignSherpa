// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Macro contract testbench: mc_xddr2_entry_store + the REAL mc_cmd_arbiter.
//
// Why this exists: the store<->arbiter commit/issue ready contract is
// STRUCTURAL ("sink has room"), and the arbiter's column mask gates the whole
// pick pool on that one scalar. A slot-qualified ready closes a combinational
// circle that permanently wedges the scheduler once a committed slot drains
// while the arbiter's slot pointer still references it -- invisible at N=1
// (the next push self-heals) and invisible to any fub-level test of the store
// alone. Only store+arbiter co-simulation at NUM_ENTRIES>=2 with MORE than N
// chunks per direction exercises it. See the 2026-10-13/14 granite hang:
// 9 commits, then a permanent stall with 7 filled entries schedulable.
//
// All DRAM-side inputs are tied permissive (page always open to row 0 on
// every bank, every timer ok, DFI command bus always ready) so the pick pool
// lives or dies purely on the commit/issue contract under test.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_store_arbiter_macro_tb_top
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES         = 8,
    parameter int AXI_ID_WIDTH        = 8,
    parameter int AXI_DATA_WIDTH      = 64,
    parameter int NUM_RANKS           = 1,
    parameter int NUM_BANKS           = 8,
    parameter int ROW_WIDTH           = 14,
    parameter int COL_WIDTH           = 10,
    parameter int AXI_BEATS_PER_BURST = 1,
    parameter int RD_RET_DEPTH        = 32,
    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int RTW  = $clog2(RD_RET_DEPTH)
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    // WR descriptor push (from cocotb)
    input  logic                 aw_push_valid,
    output logic                 aw_push_ready,
    input  logic [BKW-1:0]       aw_push_bank,
    input  logic [ROW_WIDTH-1:0] aw_push_row,
    input  logic [COL_WIDTH-1:0] aw_push_col,
    input  logic [IW-1:0]        aw_push_id,
    input  logic [3:0]           aw_push_qos,
    input  logic                 aw_push_agg,
    input  logic                 aw_push_last,

    // WR data beats (from cocotb)
    input  logic                 wd_valid,
    output logic                 wd_ready,
    input  logic [DW-1:0]        wd_data,
    input  logic [SW-1:0]        wd_strb,
    input  logic                 wd_last,

    // RD descriptor push (from cocotb)
    input  logic                 ar_push_valid,
    output logic                 ar_push_ready,
    input  logic [BKW-1:0]       ar_push_bank,
    input  logic [ROW_WIDTH-1:0] ar_push_row,
    input  logic [COL_WIDTH-1:0] ar_push_col,
    input  logic [IW-1:0]        ar_push_id,
    input  logic [3:0]           ar_push_qos,

    // Observability
    output logic                 wr_done_valid,
    output logic [IW-1:0]        wr_done_id,
    output logic [31:0]          commit_count,
    output logic [31:0]          drain_count,
    output logic [31:0]          rd_issue_count,
    output logic [31:0]          cmd_count
);

    // ------------------------------------------------------------------
    // DUT wiring: store <-> arbiter (the contract under test)
    // ------------------------------------------------------------------
    logic                     wr_commit_valid, wr_commit_ready;
    logic [PTRW-1:0]          wr_commit_slot;
    logic                     rd_issue_valid, rd_issue_ready;
    logic [PTRW-1:0]          rd_issue_slot;

    logic [NUM_ENTRIES-1:0]             wr_sch_valid, rd_sch_valid;
    logic [NUM_ENTRIES*BKW-1:0]         wr_sch_bank,  rd_sch_bank;
    logic [NUM_ENTRIES*ROW_WIDTH-1:0]   wr_sch_row,   rd_sch_row;
    logic [NUM_ENTRIES*COL_WIDTH-1:0]   wr_sch_col,   rd_sch_col;
    logic [NUM_ENTRIES*NUM_ENTRIES-1:0] wr_sch_older, rd_sch_older;
    logic [NUM_ENTRIES-1:0]             wr_age_exceed, rd_age_exceed;
    logic [NUM_ENTRIES*4-1:0]           wr_sch_qos, rd_sch_qos;
    logic [15:0]                        wr_head_rel, rd_head_rel;

    logic                cm_valid, cm_ready, cm_last;
    logic [DW-1:0]       cm_data;
    logic [SW-1:0]       cm_strb;

    logic rd_iss_valid, rd_cam_ins_ready;

    mc_xddr2_entry_store #(
        .NUM_ENTRIES        (NUM_ENTRIES),
        .AXI_ID_WIDTH       (IW),
        .AXI_DATA_WIDTH     (DW),
        .NUM_RANKS          (NUM_RANKS),
        .NUM_BANKS          (NUM_BANKS),
        .ROW_WIDTH          (ROW_WIDTH),
        .COL_WIDTH          (COL_WIDTH),
        .AXI_BEATS_PER_BURST(AXI_BEATS_PER_BURST),
        .RD_RET_DEPTH       (RD_RET_DEPTH)
    ) u_store (
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
        .snarf_probe_valid_i(1'b0),
        .snarf_probe_bank_i ('0),
        .snarf_probe_row_i  ('0),
        .snarf_probe_col_i  ('0),
        .snarf_probe_id_i   ('0),
        .snarf_probe_len_i  (8'd0),
        .snarf_hit_o        (),
        .snarf_accept_i     (1'b0),
        .snarf_rd_valid_o   (),
        .snarf_rd_ready_i   (1'b0),
        .snarf_rd_data_o    (),
        .snarf_rd_last_o    (),
        .ar_push_valid_i    (ar_push_valid),
        .ar_push_ready_o    (ar_push_ready),
        .ar_push_bank_i     (ar_push_bank),
        .ar_push_row_i      (ar_push_row),
        .ar_push_col_i      (ar_push_col),
        .ar_push_id_i       (ar_push_id),
        .ar_push_qos_i      (ar_push_qos),
        .rt_alloc_ready_i   (1'b1),
        .rt_alloc_ticket_i  ('0),
        .rd_iss_ready_i     (1'b1),
        .rd_iss_valid_o     (rd_iss_valid),
        .rd_iss_ticket_o    (),
        .rd_cam_ins_ready_o (rd_cam_ins_ready),
        .sched_age_thresh_i (8'd0),
        .wr_commit_valid_i  (wr_commit_valid),
        .wr_commit_ready_o  (wr_commit_ready),
        .wr_commit_slot_i   (wr_commit_slot),
        .rd_issue_valid_i   (rd_issue_valid),
        .rd_issue_ready_o   (rd_issue_ready),
        .rd_issue_slot_i    (rd_issue_slot),
        .wr_sch_valid_o     (wr_sch_valid),
        .wr_sch_bank_o      (wr_sch_bank),
        .wr_sch_row_o       (wr_sch_row),
        .wr_sch_col_o       (wr_sch_col),
        .wr_sch_older_o     (wr_sch_older),
        .wr_sch_age_exceed_o(wr_age_exceed),
        .wr_sch_qos_o       (wr_sch_qos),
        .wr_sch_head_rel_o  (wr_head_rel),
        .rd_sch_valid_o     (rd_sch_valid),
        .rd_sch_bank_o      (rd_sch_bank),
        .rd_sch_row_o       (rd_sch_row),
        .rd_sch_col_o       (rd_sch_col),
        .rd_sch_older_o     (rd_sch_older),
        .rd_sch_age_exceed_o(rd_age_exceed),
        .rd_sch_qos_o       (rd_sch_qos),
        .rd_sch_head_rel_o  (rd_head_rel),
        .wr_cm_rd_valid_o   (cm_valid),
        .wr_cm_rd_ready_i   (cm_ready),
        .wr_cm_rd_data_o    (cm_data),
        .wr_cm_rd_strb_o    (cm_strb),
        .wr_cm_rd_last_o    (cm_last),
        .busy_o             ()
    );

    logic        cmd_valid;
    dram_op_e    cmd_op;
    logic        cmd_ap;

    mc_cmd_arbiter #(
        .NUM_RANKS  (NUM_RANKS),
        .NUM_BANKS  (NUM_BANKS),
        .ROW_WIDTH  (ROW_WIDTH),
        .COL_WIDTH  (COL_WIDTH),
        .AXI_ID_WIDTH(IW),
        .NUM_ENTRIES(NUM_ENTRIES)
    ) u_arb (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (PAGE_POLICY_OPEN),
        .sched_order_mode_i (2'd0),
        .sched_row_sel_i    (2'd0),
        .sched_col_sel_i    (2'd0),
        .sched_access_pref_i(2'd0),
        .sched_wr_high_wm_i (8'd0),
        .sched_wr_batch_max_i(8'd0),
        .sched_wr_low_wm_i  (8'd0),
        .sched_prio_sub_i   (2'd0),
        .sched_qos_en_i     (1'b0),
        .rd_sch_qos_i       (rd_sch_qos),
        .wr_sch_qos_i       (wr_sch_qos),
        .rd_sch_age_exceed_i(rd_age_exceed),
        .wr_sch_age_exceed_i(wr_age_exceed),
        .rd_sch_head_rel_i  (rd_head_rel),
        .wr_sch_head_rel_i  (wr_head_rel),
        .ap_mode_en_i       (1'b0),
        .ap_close_i         ('0),
        .timeout_pre_req_i  (1'b0),
        .timeout_pre_bank_i ('0),
        .init_done_i        (1'b1),
        .init_cmd_valid_i   (1'b0),
        .init_cmd_op_i      (dram_op_e'(0)),
        .init_cmd_bank_i    ('0),
        .init_cmd_row_i     ('0),
        .refresh_req_i      (1'b0),
        .refresh_drain_i    (1'b0),
        .refresh_kind_i     (1'b0),
        .refresh_bank_i     ('0),
        .refresh_grant_o    (),
        .t_rfc_i            (16'd0),
        .t_rfc_pb_i         (8'd0),
        .zq_req_i           (1'b0),
        .zq_grant_o         (),
        .t_zqcs_i           (16'd0),
        .maint_req_i        (1'b0),
        .maint_grant_o      (),
        .maint_op_i         (dram_op_e'(0)),
        .maint_bank_i       ('0),
        .maint_row_i        ('0),
        .maint_col_i        ('0),
        .maint_extra_i      ('0),
        .maint_busy_i       (1'b0),
        .bank_act_ready_i   ('1),
        .bank_rdwr_ready_i  ('1),
        .bank_pre_ready_i   ('1),
        .bank_act_ready_la_i('1),
        .bank_rdwr_ready_la_i('1),
        .bank_pre_ready_la_i('1),
        .bank_row_active_i  ('1),
        .bank_open_row_i    ('0),
        .tfaw_ok_i          ('1),
        .trrd_ok_i          ('1),
        .twtr_ok_i          (1'b1),
        .trtw_ok_i          (1'b1),
        .tccd_ok_i          (1'b1),
        .tccd_l_ok_i        (1'b1),
        .trrd_l_ok_i        (1'b1),
        .pick_group_o       (),
        .t_ccd_i            (8'd0),
        .wr_sch_valid_i     (wr_sch_valid),
        .wr_sch_bank_i      (wr_sch_bank),
        .wr_sch_row_i       (wr_sch_row),
        .wr_sch_col_i       (wr_sch_col),
        .wr_sch_older_i     (wr_sch_older),
        .wr_commit_ready_i  (wr_commit_ready),
        .wr_commit_valid_o  (wr_commit_valid),
        .wr_commit_slot_o   (wr_commit_slot),
        .rd_sch_valid_i     (rd_sch_valid),
        .rd_sch_bank_i      (rd_sch_bank),
        .rd_sch_row_i       (rd_sch_row),
        .rd_sch_col_i       (rd_sch_col),
        .rd_sch_older_i     (rd_sch_older),
        .rd_issue_ready_i   (rd_issue_ready),
        .rd_issue_valid_o   (rd_issue_valid),
        .rd_issue_slot_o    (rd_issue_slot),
        .evt_act_o          (),
        .evt_rd_o           (),
        .evt_wr_o           (),
        .evt_pre_o          (),
        .evt_ap_o           (),
        .evt_rank_o         (),
        .evt_bank_o         (),
        .evt_row_o          (),
        .cmd_valid_o        (cmd_valid),
        .cmd_ready_i        (cm_ready),   // real shape: cmd bus paces with the drain
        .cmd_op_o           (cmd_op),
        .cmd_rank_o         (),
        .cmd_bank_o         (),
        .cmd_row_o          (),
        .cmd_col_o          (),
        .cmd_ap_o           (cmd_ap),
        .cmd_extra_o        (),
        .stall_bp_o         (),
        .stall_refresh_o    (),
        .stall_turnaround_o (),
        .stall_tccd_o       (),
        .stall_actlimit_o   (),
        .stall_banktimer_o  (),
        .stall_noreq_o      (),
        .stall_zq_o         ()
    );

    // DFI-side drain paced one beat per 4 cycles -- matching the real DFI
    // acceptance rate. At full-speed (1/cycle) the arbiter's pick pipeline
    // never empties between commits and the stale-pointer condition never
    // co-occurs; the full-harness hang needed the real (slow) command pacing.
    logic [1:0] r_cm_gate;
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) r_cm_gate <= '0;
        else                        r_cm_gate <= r_cm_gate + 1'b1;
    end)
    assign cm_ready = (r_cm_gate == 2'd0);

    // ------------------------------------------------------------------
    // Contract counters (checked by the cocotb test)
    // ------------------------------------------------------------------
    logic [31:0] r_commit_count, r_drain_count, r_rd_issue_count, r_cmd_count;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_commit_count  <= '0;
            r_drain_count   <= '0;
            r_rd_issue_count<= '0;
            r_cmd_count     <= '0;
        end else begin
            if (wr_commit_valid && wr_commit_ready) r_commit_count <= r_commit_count + 1;
            if (cm_valid && cm_ready)               r_drain_count  <= r_drain_count + 1;
            if (rd_iss_valid)                       r_rd_issue_count <= r_rd_issue_count + 1;
            if (cmd_valid)                          r_cmd_count <= r_cmd_count + 1;
        end
    end)

    assign commit_count   = r_commit_count;
    assign drain_count    = r_drain_count;
    assign rd_issue_count = r_rd_issue_count;
    assign cmd_count      = r_cmd_count;

endmodule : mc_store_arbiter_macro_tb_top
