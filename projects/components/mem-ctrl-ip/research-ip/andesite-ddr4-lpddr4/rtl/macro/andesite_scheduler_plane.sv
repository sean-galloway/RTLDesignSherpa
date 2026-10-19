// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_scheduler_plane
// Purpose: Thin andesite wrapper around the common mc_scheduler_plane core.
//          Instantiates the rock-specific init_sequencer, mode_register,
//          refresh_ctrl, zq_ctrl, and page_policy, and maps the andesite
//          training-command slot and DDR4 bank-group L/S timing onto the
//          common core's generic ports.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_scheduler_plane
    import andesite_pkg::*;
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
    parameter int NUM_BG      = 4,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int CMD_FIFO_DEPTH = 16,
    parameter int CMD_DELAY      = 6,
    parameter int N_LU  = NUM_BANKS,
    parameter int RKW   = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int NUM_CS = NUM_RANKS,
    parameter int CSW   = (NUM_CS > 1) ? $clog2(NUM_CS) : 1,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int BGW_EFF = (NUM_BG > 1) ? $clog2(NUM_BG) : 1,
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
    output logic [31:0]               stall_zq_o,
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
    input  logic [7:0]                t_ccd_l_i,
    input  logic [7:0]                t_ccd_s_i,
    input  logic [7:0]                t_rrd_l_i,
    input  logic [7:0]                t_rrd_s_i,
    input  logic [15:0]               t_refi_i,
    input  logic                      refi_reload_i,
    input  logic [15:0]               t_rfc_i,
    input  logic [1:0]                fgr_factor_i,
    input  logic [15:0]               t_rfc_2x_i,
    input  logic [15:0]               t_rfc_4x_i,
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
    input  logic [15:0]               t_cke_wait_i,
    input  logic [15:0]               t_mod_wait_i,
    input  logic [15:0]               t_zqinit_wait_i,
    output logic                      dram_reset_n_o,
    output logic                      cke_o,
    output logic                      wrlvl_en_o,

    input  logic                      zq_enable_i,
    input  logic [31:0]               zq_interval_i,
    input  logic [15:0]               t_zqcs_i,
    output logic                      zq_busy_o,
    output logic [15:0]               zq_total_o,
    output logic [31:0]               zq_interval_cnt_o,
    output logic                      zq_overdue_o,

    input  logic                      ref_elastic_en_i,
    input  logic [7:0]                ref_pullin_idle_streak_i,
    input  logic [6:0]                ref_postpone_demand_streak_i,
    input  logic                      ref_tcr_en_i,
    input  logic [1:0]                ref_trefi_derate_i,
    input  logic [1:0]                zq_placement_i,
    input  logic [12:0]               zq_overdue_max_i,
    input  logic [15:0]               t_zq_i,
    input  logic [5:0]                zq_mpc_opcode_i,
    output logic [15:0]               obs_ref_postpone_events_o,
    output logic [15:0]               obs_ref_pullin_events_o,

    input  logic                      trn_cmd_req_i,
    output logic                      trn_cmd_ack_o,
    input  dram_op_e                  trn_cmd_op_i,
    input  logic [2:0]                trn_cmd_bank_i,
    input  logic [17:0]               trn_cmd_addr_i,
    input  logic [5:0]                trn_cmd_mpc_i,

    input  logic [15:0]               mr0_i,
    input  logic [15:0]               mr1_i,
    input  logic [15:0]               mr2_i,
    input  logic [15:0]               mr3_i,
    input  logic [15:0]               mr4_i,
    input  logic [15:0]               mr5_i,
    input  logic [15:0]               mr6_i,
    input  logic                      init_restart_i,

    output logic                      init_done_o,
    output logic                      init_err_o,
    output logic                      zq_cal_start_o,
    output logic                      gear_down_entry_o,
    output logic                      ca_train_start_o,
    output logic                      parity_enable_o,

    output logic [2:0]                rtt_nom_o,
    output logic [2:0]                rtt_wr_o,
    output logic [2:0]                rtt_park_o,
    output logic                      rd_dbi_en_o,
    output logic                      wr_dbi_en_o,
    output logic [1:0]                mpr_page_o,
    output logic [1:0]                fgr_factor_o,
    output logic [1:0]                ca_parity_lat_o,
    output logic [2:0]                lpddr4_odt_o,

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
    output logic [BGW_EFF-1:0]        cmd_bg_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,

    output logic                      busy_o
);

    logic init_done;
    logic init_cmd_valid; dram_op_e init_cmd_op;
    logic init_cmd_valid_gated;
    logic [BKW-1:0] init_cmd_bank; logic [ROW_WIDTH-1:0] init_cmd_row;
    logic [17:0]      w_init_cmd_addr;
    logic             w_init_accept;
    logic             w_init_cmd_ack;
    logic             w_init_zq_start;
    logic [5:0]       mr_seq_wr_addr;
    logic             mr_seq_we; logic [15:0] mr_seq_data;

    logic refresh_req, refresh_drain, refresh_grant;
    logic [15:0] w_refresh_trfc;

    logic                  w_pp_ap_en;
    logic [NUM_BANKS-1:0]  w_pp_ap_close;
    logic                  w_pp_to_req;
    logic [BKW-1:0]        w_pp_to_bank;

    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  w_bank_open_row;

    logic w_refpb_en;
    logic w_refresh_kind;
    logic [BKW-1:0] w_refresh_bank;
    assign w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR3);

    logic w_zq_req, w_zq_grant;
    logic w_zq_run;
    assign w_zq_run = zq_enable_i && init_done
                    && ((memtype_i == MEMTYPE_DDR4) || (memtype_i == MEMTYPE_LPDDR4));

    logic [5:0] w_cmd_extra;
    logic       w_trn_cmd_grant;
    logic       w_cmd_accept;
    dram_op_e   w_cmd_accept_op;

    assign init_done_o    = init_done;
    assign zq_cal_start_o = w_init_zq_start;
    assign trn_cmd_ack_o  = w_trn_cmd_grant;

    // P1 init accept/ack gating. MRS/ZQCL are the only ops init issues on this
    // stream, so the arbiter accept pulse qualified by op class IS the honest
    // ack. The P1 FSM holds cmd_req until it clocks the ack; meanwhile the
    // arbiter RE-PICKS the presented request into its registered pick every
    // cycle, so a held request would push every command twice (the
    // macro-integration suite caught MRS twins one cycle apart). The pick
    // register makes the duplicate visible one cycle EARLY (the accept cycle
    // itself re-arms it), so the gate must be combinational on THIS cycle's
    // accept, not on a delayed copy: a_cmd_valid is the arbiter's registered
    // pick, so w_init_accept is loop-free. The in-flight accept is unaffected --
    // it rides the register, not the request. Legal init spacing (tMRD/tMOD >= 3
    // cycles) tolerates the one-cycle request drop.
    assign w_init_accept = w_cmd_accept && ((w_cmd_accept_op == OP_MRS) || (w_cmd_accept_op == OP_ZQCL));
    assign w_init_cmd_ack = w_init_accept;
    assign init_cmd_valid_gated = init_cmd_valid && !w_init_accept;
    assign init_cmd_row = w_init_cmd_addr[ROW_WIDTH-1:0];

    // ======================================================================
    // Rock-specific children.
    // ======================================================================
    andesite_init_sequencer #(
        .TINIT_WIDTH(16),
        .ADDR_WIDTH (18),
        .DATA_WIDTH (16)
    ) u_init (
        .clk                (aclk),
        .reset_n            (aresetn),
        .csr_memtype        (3'(memtype_i)),
        .csr_init_trigger   (init_restart_i),
        .csr_geardown_en    (1'b0),
        .csr_parity_en      (1'b0),
        .tinit1_csr         (t_init_wait_i),
        .tinit3_csr         (16'(t_rp_wait_i)),
        .tinit4_csr         (t_cke_wait_i),
        .tdllk_csr          (t_dll_wait_i),
        .tzqinit_csr        (t_zqinit_wait_i),
        .tmrd_csr           (16'(t_mrd_wait_i)),
        .tmod_csr           (t_mod_wait_i),
        .csr_mr0_image      (mr0_i),
        .csr_mr1_image      (mr1_i),
        .csr_mr2_image      (mr2_i),
        .csr_mr3_image      (mr3_i),
        .csr_mr4_image      (mr4_i),
        .csr_mr5_image      (mr5_i),
        .csr_mr6_image      (mr6_i),
        .cmd_ack            (w_init_cmd_ack),
        .parity_alert_i     (1'b0),
        .recovery_interval_i(16'd0),
        .csr_telem_clear_i  (1'b0),
        .retract_ack_i      (1'b0),
        .retract_req_o      (),
        .obs_recovery_state_o(),
        .obs_alerts_seen_o  (),
        .obs_cmds_dropped_o (),
        .obs_cmds_resent_o  (),
        .mr_image_out       (mr_seq_data),
        .mr_load            (mr_seq_we),
        .reset_n_out        (dram_reset_n_o),
        .cke_out            (cke_o),
        .cmd_req            (init_cmd_valid),
        .cmd_op             (init_cmd_op),
        .cmd_bank           (init_cmd_bank),
        .cmd_addr           (w_init_cmd_addr),
        .zq_cal_start       (w_init_zq_start),
        .gear_down_entry    (gear_down_entry_o),
        .parity_enable_out  (parity_enable_o),
        .ca_train_start     (ca_train_start_o),
        .init_done          (init_done),
        .init_err           (init_err_o)
    );

    assign mr_seq_wr_addr = {3'b000, init_cmd_bank};

    andesite_mode_register #(
        .DATA_WIDTH(16),
        .RANKS     (NUM_RANKS)
    ) u_mode_reg (
        .clk            (aclk),
        .rst_n          (aresetn),
        .memtype_i      (memtype_i),
        .rank_i         ('0),
        .wr_en_i        (mr_seq_we),
        .wr_addr_i      (mr_seq_wr_addr),
        .wr_data_i      (mr_seq_data),
        .rd_en_i        (1'b0),
        .rd_addr_i      ('0),
        .rd_data_o      (),
        .mr_sel_o       (),
        .mr_data_o      (),
        .mpr_page_o     (mpr_page_o),
        .fgr_factor_o   (fgr_factor_o),
        .rtt_nom_o      (rtt_nom_o),
        .rtt_wr_o       (rtt_wr_o),
        .rtt_park_o     (rtt_park_o),
        .rd_dbi_en_o    (rd_dbi_en_o),
        .wr_dbi_en_o    (wr_dbi_en_o),
        .ca_parity_lat_o(ca_parity_lat_o),
        .wrlvl_en_o     (wrlvl_en_o),
        .lpddr4_odt_o   (lpddr4_odt_o)
    );

    andesite_refresh_ctrl #(
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
        .elastic_en_i            (ref_elastic_en_i),
        .pullin_idle_streak_i    (ref_pullin_idle_streak_i),
        .postpone_demand_streak_i(ref_postpone_demand_streak_i),
        .tcr_en_i                (ref_tcr_en_i),
        .trefi_derate_i          (ref_trefi_derate_i),
        .fgr_factor_i            (fgr_factor_i),
        .t_rfc_1x_i              (t_rfc_i),
        .t_rfc_2x_i              (t_rfc_2x_i),
        .t_rfc_4x_i              (t_rfc_4x_i),
        .refresh_trfc_o          (w_refresh_trfc),
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
        .obs_pullin_credit_o   (),
        .obs_postpone_events_o (obs_ref_postpone_events_o),
        .obs_pullin_events_o   (obs_ref_pullin_events_o)
    );

    andesite_zq_ctrl u_zq (
        .mc_clk             (aclk),
        .mc_rst_n           (aresetn),
        .enable_i           (w_zq_run),
        .t_zqcs_interval_i  (zq_interval_i),
        .t_zqcs_i           (t_zqcs_i),
        .demand_i           (|rd_sch_valid_i || |wr_sch_valid_i),
        .placement_i        (zq_placement_i),
        .overdue_max_i      (zq_overdue_max_i),
        .zq_req_o           (w_zq_req),
        .zq_grant_i         (w_zq_grant),
        .memtype_i          (memtype_i),
        .t_zq_i             (t_zq_i),
        .mpc_opcode_i       (zq_mpc_opcode_i),
        .mpc_issuing_o      (),
        .mpc_op_o           (),
        .obs_busy_o         (zq_busy_o),
        .obs_zqcs_total_o   (zq_total_o),
        .obs_interval_cnt_o (zq_interval_cnt_o),
        .obs_overdue_o      (zq_overdue_o)
    );

    andesite_page_policy #(
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
    // Common scheduler-plane core.
    // ======================================================================
    mc_scheduler_plane #(
        .NUM_RANKS   (NUM_RANKS),
        .CMD_HISTORY_EN(CMD_HISTORY_EN),
        .HIST_T_RCD  (HIST_T_RCD),
        .HIST_T_RP   (HIST_T_RP),
        .HIST_T_RAS  (HIST_T_RAS),
        .HIST_T_RFC  (HIST_T_RFC),
        .HIST_T_WTR  (HIST_T_WTR),
        .HIST_T_RRD  (HIST_T_RRD),
        .HIST_T_FAW  (HIST_T_FAW),
        .HIST_T_RTW  (HIST_T_RTW),
        .NUM_BANKS   (NUM_BANKS),
        .NUM_BG      (NUM_BG),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH),
        .AXI_ID_WIDTH(IW),
        .NUM_ENTRIES (NUM_ENTRIES),
        .AGE_WIDTH   (AGE_WIDTH),
        .CMD_FIFO_DEPTH(CMD_FIFO_DEPTH),
        .CMD_DELAY   (CMD_DELAY),
        .HAS_ZQ      (1'b1),
        .MAINT_EXTRA_WIDTH(6)
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
        .stall_zq_o         (stall_zq_o),
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
        .t_ccd_l_i          (t_ccd_l_i),
        .t_ccd_s_i          (t_ccd_s_i),
        .t_rrd_l_i          (t_rrd_l_i),
        .t_rrd_s_i          (t_rrd_s_i),
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
        .dfi_init_start_o   (),
        .dfi_init_complete_i(1'b0),
        .init_done_o        (),
        .cl_o               (),
        .cwl_o              (),
        .bl_o               (),
        .t_refi_i           (t_refi_i),
        .refi_reload_i      (refi_reload_i),
        .refresh_burst_i    (refresh_burst_i),
        .ref_postpone_i     (ref_postpone_i),
        .ref_pullin_i       (ref_pullin_i),
        .ref_mode_i         (ref_mode_i),
        .ref_trefi_pb_i     (ref_trefi_pb_i),
        .refresh_req_i      (refresh_req),
        .refresh_drain_i    (refresh_drain),
        .refresh_kind_i     (w_refresh_kind),
        .refresh_bank_i     (w_refresh_bank),
        .refresh_grant_o    (refresh_grant),
        .t_rfc_i            (w_refresh_trfc),
        .ref_trfc_pb_i      (ref_trfc_pb_i),
        .zq_req_i           (w_zq_req),
        .zq_grant_o         (w_zq_grant),
        .t_zqcs_i           (t_zqcs_i),
        .maint_req_i        (trn_cmd_req_i),
        .maint_grant_o      (w_trn_cmd_grant),
        // TRAINING (MRS/MPC): all banks must be idle (JESD79-4 MRS /
        // JESD209-4 MPC). Same two-step shape as refresh/ZQ: the common core
        // closes banks first, then issues + grants. Idles rather than falls
        // through so host traffic cannot reopen rows.
        .maint_op_i         (trn_cmd_op_i),
        .maint_bank_i       (trn_cmd_bank_i[BKW-1:0]),
        .maint_row_i        (trn_cmd_addr_i[ROW_WIDTH-1:0]),
        .maint_col_i        (trn_cmd_addr_i[COL_WIDTH-1:0]),
        .maint_extra_i      (trn_cmd_mpc_i),
        .maint_busy_i       (1'b0),
        .init_done_i        (init_done),
        .init_cmd_valid_i   (init_cmd_valid_gated),
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
        .wr_bh_valid_i      ('0),
        .wr_bh_slot_i       ('0),
        .wr_bh_row_i        ('0),
        .wr_bh_col_i        ('0),
        .wr_bh_id_i         ('0),
        .wr_bh_last_i       ('0),
        .wr_bh_empty_i      ('0),
        .wr_bh_act_i        ('0),
        .wr_bh_age_i        ('0),
        .rd_bh_valid_i      ('0),
        .rd_bh_slot_i       ('0),
        .rd_bh_row_i        ('0),
        .rd_bh_col_i        ('0),
        .rd_bh_id_i         ('0),
        .rd_bh_empty_i      ('0),
        .rd_bh_act_i        ('0),
        .rd_bh_age_i        ('0),
        .wr_bh2_valid_i     ('0),
        .wr_bh2_slot_i      ('0),
        .wr_bh2_row_i       ('0),
        .wr_bh2_col_i       ('0),
        .wr_bh2_id_i        ('0),
        .wr_bh2_last_i      ('0),
        .wr_bh2_act_i       ('0),
        .wr_bh2_age_i       ('0),
        .rd_bh2_valid_i     ('0),
        .rd_bh2_slot_i      ('0),
        .rd_bh2_row_i       ('0),
        .rd_bh2_col_i       ('0),
        .rd_bh2_id_i        ('0),
        .rd_bh2_act_i       ('0),
        .rd_bh2_age_i       ('0),
        .rd_issue_ready_i   (rd_issue_ready_i),
        .rd_issue_valid_o   (rd_issue_valid_o),
        .rd_issue_slot_o    (rd_issue_slot_o),
        .sched_decr_o       (),
        .rd_ret_busy_i      (1'b0),
        .cmd_valid_o        (cmd_valid_o),
        .cmd_ready_i        (cmd_ready_i),
        .cmd_op_o           (cmd_op_o),
        .cmd_rank_o         (cmd_rank_o),
        .cmd_bank_o         (cmd_bank_o),
        .cmd_bg_o           (cmd_bg_o),
        .cmd_row_o          (cmd_row_o),
        .cmd_col_o          (cmd_col_o),
        .cmd_ap_o           (cmd_ap_o),
        .cmd_extra_o        (w_cmd_extra),
        .bank_row_active_o  (w_bank_row_active),
        .bank_open_row_o    (w_bank_open_row),
        .busy_o             (busy_o),
        .cmd_accept_o       (w_cmd_accept),
        .cmd_accept_op_o    (w_cmd_accept_op)
    );

    // The page-policy telemetry is produced by the wrapper's own page_policy
    // (not the tied-off outputs of the common core). The common core's
    // telemetry outputs are intentionally unused here.

    // ---- optional command-history scoreboard --------------------------------
    generate if (CMD_HISTORY_EN != 0) begin : g_cmd_history
        andesite_cmd_history_checker #(
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
            .cmd_bank_i (cmd_bank_o),
            .cmd_bg_i   (cmd_bg_o)
        );
    end endgenerate

    wire _unused = &{1'b0, w_cmd_extra};

endmodule : andesite_scheduler_plane
