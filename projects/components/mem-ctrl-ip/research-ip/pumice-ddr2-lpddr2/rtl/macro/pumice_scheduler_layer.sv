// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_scheduler_layer
// Purpose: Thin pumice wrapper around the common mc_scheduler_layer core.
//          Instantiates the rock-specific init_sequencer, mode_register,
//          refresh_ctrl, page_policy, and command-history checker, and maps
//          the pumice training channel onto the generic maintenance slot.
//
//          PHY/nphases-agnostic; single-issue; single controller clock (aclk).
//          The CAM sched-lookup / oldest / commit / issue ports are EXTERNAL
//          (the CAMs live in pumice_axi4_layer).
//
// Documentation: docs/uarch/PUMICE_SCHEDULER_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_scheduler_layer
    import pumice_pkg::*;
    import mc_common_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    parameter int CMD_HISTORY_EN = 0,
    parameter int HIST_T_RCD  = 0,
    parameter int HIST_T_RP   = 0,
    parameter int HIST_T_RAS  = 0,
    parameter int HIST_T_RFC  = 8,
    parameter int HIST_T_WTR  = 0,
    parameter int HIST_T_RRD  = 0,
    parameter int HIST_T_FAW  = 0,
    parameter int HIST_T_RTW  = 0,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int CMD_FIFO_DEPTH = 16,
    parameter int CMD_DELAY      = 6,
    parameter int N_LU  = NUM_BANKS,
    parameter int RKW   = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int IW    = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,

    input  page_policy_e              page_policy_i,

    input  logic [1:0]                sched_order_mode_i,
    input  logic [1:0]                sched_row_sel_i,
    input  logic [1:0]                sched_col_sel_i,
    input  logic [1:0]                sched_access_pref_i,
    input  logic [7:0]                sched_wr_high_wm_i,
    input  logic [7:0]                sched_wr_batch_max_i,
    input  logic [7:0]                sched_wr_low_wm_i,
    input  logic [1:0]                sched_prio_sub_i,
    input  logic                      sched_qos_en_i,
    input  logic [2:0]                page_mode_i,
    input  logic [7:0]                page_tr_init_i,

    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stat_page_hit_o,
    output logic [31:0]               stat_row_hit_o [NUM_BANKS],
    output logic [31:0]               stat_page_miss_o,
    output logic [31:0]               stat_page_empty_o,
    output logic [31:0]               stat_act_o,
    output logic [31:0]               stat_pre_o,
    output logic [31:0]               stat_ref_o,
    output logic [31:0]               stat_ref_busy_o,
    input  memtype_e                  memtype_i,
    input  logic [7:0]                t_rcd_i,
    input  logic [7:0]                t_rp_i,
    input  logic [7:0]                t_ras_i,
    input  logic [7:0]                t_rc_i,
    input  logic [7:0]                t_wr_i,
    input  logic [7:0]                t_rtp_i,
    input  logic [7:0]                t_faw_i,
    input  logic [7:0]                t_rrd_i,
    input  logic [7:0]                t_wtr_i,
    input  logic [7:0]                t_rtw_i,
    input  logic [7:0]                t_ccd_i,
    input  logic [15:0]               t_refi_i,
    input  logic                      refi_reload_i,
    input  logic [15:0]               t_rfc_i,
    input  logic [3:0]                refresh_burst_i,
    input  logic [3:0]                ref_postpone_i,
    input  logic [3:0]                ref_pullin_i,
    input  logic [1:0]                ref_mode_i,
    input  logic [15:0]               ref_trefi_pb_i,
    input  logic [7:0]                ref_trfc_pb_i,
    input  logic [15:0]               t_init_wait_i,
    input  logic [15:0]               t_dll_wait_i,
    input  logic [7:0]                t_mrd_wait_i,
    input  logic [7:0]                t_rp_wait_i,
    input  logic [7:0]                t_rfc_wait_i,
    input  logic [15:0]               mr0_i,
    input  logic [15:0]               mr1_i,
    input  logic [15:0]               mr2_i,
    input  logic [15:0]               mr3_i,
    input  logic                      init_restart_i,

    output logic                      dfi_init_start_o,
    input  logic                      dfi_init_complete_i,
    output logic                      init_done_o,

    output logic [3:0]                cl_o,
    output logic [3:0]                cwl_o,
    output logic [3:0]                bl_o,

    input  logic [NUM_ENTRIES-1:0]              wr_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_i,
    input  logic [NUM_ENTRIES-1:0]              wr_sch_age_exceed_i,
    input  logic [NUM_ENTRIES*4-1:0]            wr_sch_qos_i,
    input  logic [15:0]                         wr_sch_head_rel_i,
    input  logic                                wr_commit_ready_i,
    output logic                                wr_commit_valid_o,
    output logic [PTRW-1:0]                     wr_commit_slot_o,

    input  logic [NUM_ENTRIES-1:0]              rd_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_i,
    input  logic [NUM_ENTRIES-1:0]              rd_sch_age_exceed_i,
    input  logic [NUM_ENTRIES*4-1:0]            rd_sch_qos_i,
    input  logic [15:0]                         rd_sch_head_rel_i,
    input  logic                                rd_issue_ready_i,
    output logic                                rd_issue_valid_o,
    output logic [PTRW-1:0]                     rd_issue_slot_o,

    output logic                      cmd_valid_o,
    input  logic                      cmd_ready_i,
    output dram_op_e                  cmd_op_o,
    output logic [RKW-1:0]            cmd_rank_o,
    output logic [BKW-1:0]            cmd_bank_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,
    output logic                      cmd_mrr_o,

    input  logic                      trn_cmd_req_i,
    output logic                      trn_cmd_grant_o,
    input  dram_op_e                  trn_cmd_op_i,
    input  logic [BKW-1:0]            trn_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      trn_cmd_row_i,
    input  logic                      trn_cmd_mrr_i,
    input  logic                      cal_busy_i,

    output logic                      busy_o
);

    // ---- internal nets ----
    logic init_done;
    logic init_cmd_valid; dram_op_e init_cmd_op;
    logic [BKW-1:0] init_cmd_bank; logic [ROW_WIDTH-1:0] init_cmd_row;
    logic mr_seq_we; logic [4:0] mr_seq_index; logic [15:0] mr_seq_data;

    logic refresh_req, refresh_drain, refresh_grant;

    logic                  w_pp_ap_en;
    logic [NUM_BANKS-1:0]  w_pp_ap_close;
    logic                  w_pp_to_req;
    logic [BKW-1:0]        w_pp_to_bank;

    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  w_bank_open_row;

    logic            w_refpb_en;
    logic            w_refresh_kind;
    logic [BKW-1:0]  w_refresh_bank;
    assign w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR2);

    assign init_done_o = init_done;

    // ======================================================================
    // Rock-specific children.
    // ======================================================================
    init_sequencer #(
        .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH)
    ) u_init (
        .mc_clk             (aclk),
        .mc_rst_n           (aresetn),
        .memtype_i          (memtype_i),
        .t_init_wait_i      (t_init_wait_i),
        .t_dll_wait_i       (t_dll_wait_i),
        .t_mrd_wait_i       (t_mrd_wait_i),
        .t_rp_wait_i        (t_rp_wait_i),
        .t_rfc_wait_i       (t_rfc_wait_i),
        .mr0_i              (mr0_i),
        .mr1_i              (mr1_i),
        .mr2_i              (mr2_i),
        .mr3_i              (mr3_i),
        .init_restart_i     (init_restart_i),
        .dfi_init_start_o   (dfi_init_start_o),
        .dfi_init_complete_i(dfi_init_complete_i),
        .mr_seq_we_o        (mr_seq_we),
        .mr_seq_index_o     (mr_seq_index),
        .mr_seq_data_o      (mr_seq_data),
        .init_cmd_valid_o   (init_cmd_valid),
        .init_cmd_op_o      (init_cmd_op),
        .init_cmd_bank_o    (init_cmd_bank),
        .init_cmd_row_o     (init_cmd_row),
        .zqcl_req_o         (),
        .zqcl_grant_i       (1'b0),
        .init_busy_o        (),
        .init_done_o        (init_done)
    );

    mode_register #(
        .NUM_RANKS(NUM_RANKS)
    ) u_mode_reg (
        .mc_clk        (aclk),
        .mc_rst_n      (aresetn),
        .memtype_i     (memtype_i),
        .mr_we_i       (mr_seq_we),
        .mr_index_i    (mr_seq_index),
        .mr_data_i     (mr_seq_data),
        .mr_rank_i     ('0),
        .mr_req_o      (),
        .mr_grant_i    (1'b0),
        .mr_req_index_o(),
        .mr_req_data_o (),
        .mr_req_rank_o (),
        .cl_o          (cl_o),
        .cwl_o         (cwl_o),
        .bl_o          (bl_o),
        .al_o          (),
        .drv_strength_o(),
        .odt_o         ()
    );

    refresh_ctrl #(
        .NUM_BANKS(NUM_BANKS)
    ) u_refresh (
        .mc_clk          (aclk),
        .mc_rst_n        (aresetn),
        .t_refi_i        (t_refi_i),
        .trefi_pb_i      (ref_trefi_pb_i),
        .refresh_burst_i (refresh_burst_i),
        .refpb_mode_i    (w_refpb_en),
        .refi_reload_i   (refi_reload_i),
        .enable_i        (init_done),
        .postpone_limit_i(ref_postpone_i),
        .pullin_limit_i  (ref_pullin_i),
        .demand_i        (|rd_sch_valid_i || |wr_sch_valid_i),
        .refresh_req_o   (refresh_req),
        .refresh_grant_i (refresh_grant),
        .grant_was_pb_i        (cmd_op_o == OP_REFPB),
        .pending_refreshes_o   (),
        .refresh_drain_active_o(refresh_drain),
        .refresh_kind_o        (w_refresh_kind),
        .refresh_bank_o        (w_refresh_bank),
        .obs_refi_cnt_o        (),
        .obs_drain_remaining_o (),
        .obs_bank_rotor_o      (),
        .obs_grants_total_o    (),
        .obs_pullin_credit_o   ()
    );

    pumice_page_policy #(
        .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH)
    ) u_page_policy (
        .aclk              (aclk),
        .aresetn           (aresetn),
        .policy_mode_i     (page_mode_i),
        .tr_init_i         (page_tr_init_i),
        .cmd_valid_i       (cmd_valid_o && cmd_ready_i),
        .cmd_op_i          (cmd_op_o),
        .cmd_bank_i        (cmd_bank_o),
        .cmd_row_i         (cmd_row_o),
        .bank_row_active_i (w_bank_row_active[0]),
        .bank_open_row_i   (w_bank_open_row[0]),
        .ap_mode_en_o      (w_pp_ap_en),
        .ap_close_o        (w_pp_ap_close),
        .timeout_pre_req_o (w_pp_to_req),
        .timeout_pre_bank_o(w_pp_to_bank),
        .stat_page_hit_o   (stat_page_hit_o),
        .stat_row_hit_o    (stat_row_hit_o),
        .stat_page_miss_o  (stat_page_miss_o),
        .stat_page_empty_o (stat_page_empty_o),
        .stat_act_o        (stat_act_o),
        .stat_pre_o        (stat_pre_o),
        .stat_ref_o        (stat_ref_o),
        .demand_i          (|rd_sch_valid_i || |wr_sch_valid_i),
        .stat_ref_busy_o   (stat_ref_busy_o)
    );

    // ======================================================================
    // Common scheduler-layer core.
    // ======================================================================
    // Pumice maps its single-bit MRR training flag onto maint_extra[0].
    logic w_maint_grant;
    logic [0:0] w_maint_extra_in;
    logic [0:0] w_maint_extra_out;
    assign w_maint_extra_in[0] = trn_cmd_mrr_i;

    mc_scheduler_layer #(
        .NUM_RANKS   (NUM_RANKS),
        .NUM_BANKS   (NUM_BANKS),
        .NUM_BG      (1),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH),
        .AXI_ID_WIDTH(IW),
        .NUM_ENTRIES (NUM_ENTRIES),
        .AGE_WIDTH   (AGE_WIDTH),
        .CMD_FIFO_DEPTH(CMD_FIFO_DEPTH),
        .CMD_DELAY   (CMD_DELAY),
        .HAS_ZQ      (1'b0),
        .MAINT_EXTRA_WIDTH(1)
    ) u_core (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (page_policy_i),
        .sched_order_mode_i (sched_order_mode_i),
        .sched_row_sel_i    (sched_row_sel_i),
        .sched_col_sel_i    (sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i (sched_wr_high_wm_i),
        .sched_wr_batch_max_i(sched_wr_batch_max_i),
        .sched_wr_low_wm_i  (sched_wr_low_wm_i),
        .sched_prio_sub_i   (sched_prio_sub_i),
        .sched_qos_en_i     (sched_qos_en_i),
        .page_mode_i        (page_mode_i),
        .page_tr_init_i     (page_tr_init_i),
        .stall_bp_o         (stall_bp_o),
        .stall_refresh_o    (stall_refresh_o),
        .stall_turnaround_o (stall_turnaround_o),
        .stall_tccd_o       (stall_tccd_o),
        .stall_actlimit_o   (stall_actlimit_o),
        .stall_banktimer_o  (stall_banktimer_o),
        .stall_noreq_o      (stall_noreq_o),
        .stall_zq_o         (),
        .stat_page_hit_o    (),
        .stat_row_hit_o     (),
        .stat_page_miss_o   (),
        .stat_page_empty_o  (),
        .stat_act_o         (),
        .stat_pre_o         (),
        .stat_ref_o         (),
        .stat_ref_busy_o    (),
        .memtype_i          (memtype_i),
        .t_rcd_i            (t_rcd_i),
        .t_rp_i             (t_rp_i),
        .t_ras_i            (t_ras_i),
        .t_rc_i             (t_rc_i),
        .t_wr_i             (t_wr_i),
        .t_rtp_i            (t_rtp_i),
        .t_faw_i            (t_faw_i),
        .t_rrd_i            (t_rrd_i),
        .t_wtr_i            (t_wtr_i),
        .t_rtw_i            (t_rtw_i),
        .t_ccd_i            (t_ccd_i),
        .t_ccd_l_i          (8'd0),
        .t_ccd_s_i          (8'd0),
        .t_rrd_l_i          (8'd0),
        .t_rrd_s_i          (8'd0),
        .refresh_req_i      (refresh_req),
        .refresh_drain_i    (refresh_drain),
        .refresh_kind_i     (w_refresh_kind),
        .refresh_bank_i     (w_refresh_bank),
        .refresh_grant_o    (refresh_grant),
        .t_rfc_i            (t_rfc_i),
        .t_rfc_pb_i         (ref_trfc_pb_i),
        .zq_req_i           (1'b0),
        .zq_grant_o         (),
        .t_zqcs_i           (16'd0),
        .maint_req_i        (trn_cmd_req_i),
        .maint_grant_o      (w_maint_grant),
        .maint_op_i         (trn_cmd_op_i),
        .maint_bank_i       (trn_cmd_bank_i),
        .maint_row_i        (trn_cmd_row_i),
        .maint_extra_i      (w_maint_extra_in),
        .maint_busy_i       (cal_busy_i),
        .init_done_i        (init_done),
        .init_cmd_valid_i   (init_cmd_valid),
        .init_cmd_op_i      (init_cmd_op),
        .init_cmd_bank_i    (init_cmd_bank),
        .init_cmd_row_i     (init_cmd_row),
        .ap_mode_en_i       (w_pp_ap_en),
        .ap_close_i         (w_pp_ap_close),
        .timeout_pre_req_i  (w_pp_to_req),
        .timeout_pre_bank_i (w_pp_to_bank),
        .wr_sch_valid_i     (wr_sch_valid_i),
        .wr_sch_bank_i      (wr_sch_bank_i),
        .wr_sch_row_i       (wr_sch_row_i),
        .wr_sch_col_i       (wr_sch_col_i),
        .wr_sch_older_i     (wr_sch_older_i),
        .wr_sch_age_exceed_i(wr_sch_age_exceed_i),
        .wr_sch_qos_i       (wr_sch_qos_i),
        .wr_sch_head_rel_i  (wr_sch_head_rel_i),
        .wr_commit_ready_i  (wr_commit_ready_i),
        .wr_commit_valid_o  (wr_commit_valid_o),
        .wr_commit_slot_o   (wr_commit_slot_o),
        .rd_sch_valid_i     (rd_sch_valid_i),
        .rd_sch_bank_i      (rd_sch_bank_i),
        .rd_sch_row_i       (rd_sch_row_i),
        .rd_sch_col_i       (rd_sch_col_i),
        .rd_sch_older_i     (rd_sch_older_i),
        .rd_sch_age_exceed_i(rd_sch_age_exceed_i),
        .rd_sch_qos_i       (rd_sch_qos_i),
        .rd_sch_head_rel_i  (rd_sch_head_rel_i),
        .rd_issue_ready_i   (rd_issue_ready_i),
        .rd_issue_valid_o   (rd_issue_valid_o),
        .rd_issue_slot_o    (rd_issue_slot_o),
        .cmd_valid_o        (cmd_valid_o),
        .cmd_ready_i        (cmd_ready_i),
        .cmd_op_o           (cmd_op_o),
        .cmd_rank_o         (cmd_rank_o),
        .cmd_bank_o         (cmd_bank_o),
        .cmd_bg_o           (),
        .cmd_row_o          (cmd_row_o),
        .cmd_col_o          (cmd_col_o),
        .cmd_ap_o           (cmd_ap_o),
        .cmd_extra_o        (w_maint_extra_out),
        .bank_row_active_o  (w_bank_row_active),
        .bank_open_row_o    (w_bank_open_row),
        .busy_o             (busy_o)
    );

    assign trn_cmd_grant_o = w_maint_grant;
    assign cmd_mrr_o       = w_maint_extra_out[0];

    // ---- optional command-history scoreboard -------------------------------
    generate if (CMD_HISTORY_EN != 0) begin : g_cmd_history
        pumice_cmd_history_checker #(
            .NUM_RANKS(NUM_RANKS),
            .NUM_BANKS(NUM_BANKS),
            .DEPTH    (32),
            .T_RCD    (HIST_T_RCD),
            .T_RP     (HIST_T_RP),
            .T_RAS    (HIST_T_RAS),
            .T_RFC    (HIST_T_RFC),
            .T_WTR    (HIST_T_WTR),
            .T_RTW    (HIST_T_RTW),
            .T_RRD    (HIST_T_RRD),
            .T_FAW    (HIST_T_FAW)
        ) u_cmd_history (
            .clk        (aclk),
            .rst_n      (aresetn),
            .cmd_valid_i(cmd_valid_o && cmd_ready_i),
            .cmd_op_i   (cmd_op_o),
            .cmd_rank_i (cmd_rank_o),
            .cmd_bank_i (cmd_bank_o)
        );
    end endgenerate

endmodule : pumice_scheduler_layer
