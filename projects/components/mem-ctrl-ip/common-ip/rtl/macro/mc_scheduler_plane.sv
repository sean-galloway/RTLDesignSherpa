// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_scheduler_plane
// Purpose: Common scheduler-plane macro for the mem-ctrl family. Wires the
//          common command arbiter to the per-bank safe timers, global
//          (bus/rank) timers, an output command FIFO, and the v2 generation's
//          rock-specific children (init_sequencer, mode_register, refresh_ctrl,
//          page_policy, and optional cmd_history_checker).  A product configures
//          which children compose via the HAS_* parameters; the default v2 set
//          matches the pumice reference wiring.
//
//          - NUM_BG > 1 enables DDR4 bank-group L/S timing and carries cmd_bg_o.
//          - HAS_ZQ == 1 exposes the ZQ calibration request/grant/t_zqcs port.
//          - HAS_CMD_HISTORY arms the scheduler-side JEDEC sequencing scoreboard.
//
// Documentation: projects/components/mem-ctrl-ip/common-ip/docs/mc_scheduler_knobs.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_scheduler_plane
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
    parameter int NUM_BG      = 1,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int CMD_FIFO_DEPTH = 16,
    parameter int CMD_DELAY      = 6,
    parameter bit HAS_ZQ      = 1'b0,
    parameter int MAINT_EXTRA_WIDTH = 1,
    parameter bit CLOSE_ON_DRAIN = 1'b1,
    parameter bit BANK_IN_ORDER  = 1'b0,
    // SCHED_CORE select: BANK_FIFO = the per-bank in-order product core
    // (mc_bank_sched, the family design); 0 = the FRFCFS research core
    // (mc_cmd_arbiter). See common-ip/docs/mc_scheduler_plane_v2.md.
    parameter bit BANK_FIFO      = 1'b0,
    // v2 children composition
    parameter bit HAS_INIT_SEQUENCER = 1'b1,
    parameter bit HAS_MODE_REGISTER  = 1'b1,
    parameter bit HAS_REFRESH_CTRL   = 1'b1,
    parameter bit HAS_PAGE_POLICY    = 1'b1,
    parameter bit HAS_CMD_HISTORY    = 1'b0,
    // refresh feature reduction (passed to mc_xddr2_refresh_ctrl)
    parameter bit REF_HAS_POSTPONE    = 1'b1,
    parameter bit REF_HAS_PULLIN      = 1'b1,
    parameter bit REF_HAS_REFPB       = 1'b1,
    parameter bit REF_HAS_DRAIN_BURST = 1'b1,

    parameter int N_LU  = NUM_BANKS,
    parameter int RKW   = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int NUM_CS = NUM_RANKS,
    parameter int CSW   = (NUM_CS > 1) ? $clog2(NUM_CS) : 1,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int IW    = AXI_ID_WIDTH,
    parameter int BGW_EFF = (NUM_BG > 1) ? $clog2(NUM_BG) : 1
) (
    input  logic                      aclk,
    input  logic                      aresetn,

    // ---- config ----
    input  page_policy_e              page_policy_i,

    // ---- runtime page-policy CSR fields + telemetry ----
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

    // page-policy pass-through (used when HAS_PAGE_POLICY=0)
    input  logic                      ap_mode_en_i,
    input  logic [NUM_BANKS-1:0]      ap_close_i,
    input  logic                      timeout_pre_req_i,
    input  logic [BKW-1:0]            timeout_pre_bank_i,

    // stall-cause attribution from the arbiter
    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stall_zq_o,

    // page-policy telemetry (from the page_policy child)
    output logic [31:0]               stat_page_hit_o,
    output logic [31:0]               stat_row_hit_o [NUM_BANKS],
    output logic [31:0]               stat_page_miss_o,
    output logic [31:0]               stat_page_empty_o,
    output logic [31:0]               stat_act_o,
    output logic [31:0]               stat_pre_o,
    output logic [31:0]               stat_ref_o,
    output logic [31:0]               stat_ref_busy_o,

    // ---- runtime timing CSRs ----
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
    // L/S pair CSRs (tied off in wrappers when NUM_BG == 1)
    input  logic [7:0]                t_ccd_l_i,
    input  logic [7:0]                t_ccd_s_i,
    input  logic [7:0]                t_rrd_l_i,
    input  logic [7:0]                t_rrd_s_i,

    // ---- init sequencer timing / MR CSRs ----
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

    // init-sequencer pass-through (used when HAS_INIT_SEQUENCER=0)
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    output logic                      dfi_init_start_o,
    input  logic                      dfi_init_complete_i,
    output logic                      init_done_o,

    output logic [3:0]                cl_o,
    output logic [3:0]                cwl_o,
    output logic [3:0]                bl_o,

    // ---- refresh CSRs ----
    input  logic [15:0]               t_refi_i,
    input  logic                      refi_reload_i,
    input  logic [15:0]               t_rfc_i,
    input  logic [3:0]                refresh_burst_i,
    input  logic [3:0]                ref_postpone_i,
    input  logic [3:0]                ref_pullin_i,
    input  logic [1:0]                ref_mode_i,
    input  logic [15:0]               ref_trefi_pb_i,
    input  logic [7:0]                ref_trfc_pb_i,

    // refresh pass-through (used when HAS_REFRESH_CTRL=0)
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    input  logic                      refresh_kind_i,
    input  logic [BKW-1:0]            refresh_bank_i,
    output logic                      refresh_grant_o,

    // ---- ZQ calibration (from wrapper's zq source; present when HAS_ZQ=1) ----
    input  logic                      zq_req_i,
    output logic                      zq_grant_o,
    input  logic [15:0]               t_zqcs_i,

    // ---- generic maintenance-class commands (from training plane) ----
    input  logic                      maint_req_i,
    output logic                      maint_grant_o,
    input  dram_op_e                  maint_op_i,
    input  logic [BKW-1:0]            maint_bank_i,
    input  logic [ROW_WIDTH-1:0]      maint_row_i,
    input  logic [COL_WIDTH-1:0]      maint_col_i,
    input  logic [MAINT_EXTRA_WIDTH-1:0] maint_extra_i,
    input  logic                      maint_busy_i,

    // ---- CAM per-entry vectors (external) ----
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

    // ---- BANK_FIFO storage head views (from mc_xddr2_entry_store; tied off
    // when the FRFCFS core is selected) ------------------------------------
    input  logic [NUM_BANKS-1:0]                wr_bh_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0]           wr_bh_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      wr_bh_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0]      wr_bh_col_i,
    input  logic [NUM_BANKS*IW-1:0]             wr_bh_id_i,
    input  logic [NUM_BANKS-1:0]                wr_bh_last_i,
    input  logic [NUM_BANKS-1:0]                wr_bh_empty_i,
    input  logic [NUM_BANKS-1:0]                rd_bh_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0]           rd_bh_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      rd_bh_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0]      rd_bh_col_i,
    input  logic [NUM_BANKS*IW-1:0]             rd_bh_id_i,
    input  logic [NUM_BANKS-1:0]                rd_bh_empty_i,
    input  logic [NUM_BANKS-1:0]                wr_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0]           wr_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      wr_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0]      wr_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]             wr_bh2_id_i,
    input  logic [NUM_BANKS-1:0]                wr_bh2_last_i,
    input  logic [NUM_BANKS-1:0]                rd_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0]           rd_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      rd_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0]      rd_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]             rd_bh2_id_i,
    input  logic                                rd_issue_ready_i,
    output logic                                rd_issue_valid_o,
    output logic [PTRW-1:0]                     rd_issue_slot_o,

    // ---- read-return busy from DFI plane (BANK_FIFO core only) ----
    input  logic                                rd_ret_busy_i,

    // ---- output command stream (to DFI plane) ----
    output logic                      cmd_valid_o,
    input  logic                      cmd_ready_i,
    output dram_op_e                  cmd_op_o,
    output logic [RKW-1:0]            cmd_rank_o,
    output logic [BKW-1:0]            cmd_bank_o,
    output logic [BGW_EFF-1:0]        cmd_bg_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,
    output logic [MAINT_EXTRA_WIDTH-1:0] cmd_extra_o,

    // registered bank-state image (for rock page_policy / history checkers)
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_o,

    output logic                      busy_o,

    // Pre-FIFO command accept (arbiter-side).
    output logic                      cmd_accept_o,
    output dram_op_e                  cmd_accept_op_o
);

    // ---- internal nets ----
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_act_ready_la;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_rdwr_ready_la;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_pre_ready_la;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_act_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_pre_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  w_bank_open_row;

    logic [NUM_RANKS-1:0] w_tfaw_ok, w_trrd_ok;
    logic w_twtr_ok, w_trtw_ok, w_tccd_ok;
    logic w_tccd_l_ok, w_tccd_s_ok, w_trrd_l_ok, w_trrd_s_ok;

    logic evt_act, evt_rd, evt_wr, evt_pre, evt_ap;
    logic [RKW-1:0] evt_rank; logic [BKW-1:0] evt_bank; logic [ROW_WIDTH-1:0] evt_row;

    // arbiter -> cmd FIFO
    logic          a_cmd_valid, a_cmd_ready;
    dram_op_e      a_cmd_op;
    logic [RKW-1:0] a_cmd_rank; logic [BKW-1:0] a_cmd_bank;
    logic [BGW_EFF-1:0] a_cmd_bg;
    logic [ROW_WIDTH-1:0] a_cmd_row; logic [COL_WIDTH-1:0] a_cmd_col; logic a_cmd_ap;
    logic [MAINT_EXTRA_WIDTH-1:0] a_cmd_extra;

    // ======================================================================
    // v2 children: init / mode-register / refresh / page-policy
    // ======================================================================
    logic                       init_done;
    logic                       init_cmd_valid; dram_op_e init_cmd_op;
    logic [BKW-1:0]             init_cmd_bank; logic [ROW_WIDTH-1:0] init_cmd_row;
    logic                       mr_seq_we; logic [4:0] mr_seq_index; logic [15:0] mr_seq_data;

    logic                       refresh_req, refresh_drain, refresh_grant;
    logic                       w_refresh_kind;
    logic [BKW-1:0]             w_refresh_bank;
    assign refresh_grant_o = refresh_grant;

    logic                       w_pp_ap_en;
    logic [NUM_BANKS-1:0]       w_pp_ap_close;
    logic                       w_pp_to_req;
    logic [BKW-1:0]             w_pp_to_bank;

    logic                       w_refpb_en;
    assign w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR2);

    generate
        if (HAS_INIT_SEQUENCER) begin : g_init
            mc_xddr2_init_sequencer #(
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
                // Legacy internal-init path: tie the LPDDR2 MR OP data to the
                // JEDEC defaults the old hardcoded localparams carried
                // (8'h23/8'h01/8'h02). The xDDR2-generation products run
                // HAS_INIT_SEQUENCER=0 and take CSR-backed values through
                // mc_init_plane instead.
                .lp_mr1_op_i        (8'h23),
                .lp_mr2_op_i        (8'h01),
                .lp_mr3_op_i        (8'h02),
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
                .init_done_o        (init_done),
                .init_state_o       ()
            );
        end else begin : g_no_init
            assign dfi_init_start_o = 1'b0;
            assign init_done        = init_done_i;
            assign init_cmd_valid   = init_cmd_valid_i;
            assign init_cmd_op      = init_cmd_op_i;
            assign init_cmd_bank    = init_cmd_bank_i;
            assign init_cmd_row     = init_cmd_row_i;
            assign mr_seq_we        = 1'b0;
            assign mr_seq_index     = 5'd0;
            assign mr_seq_data      = 16'd0;
            wire _unused_init = &{1'b0, dfi_init_complete_i, t_init_wait_i, t_dll_wait_i,
                                  t_mrd_wait_i, t_rp_wait_i, t_rfc_wait_i,
                                  mr0_i, mr1_i, mr2_i, mr3_i, init_restart_i};
        end
    endgenerate

    generate
        if (HAS_MODE_REGISTER) begin : g_mode_reg
            mc_xddr2_mode_register #(
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
        end else begin : g_no_mode_reg
            assign cl_o  = 4'd0;
            assign cwl_o = 4'd0;
            assign bl_o  = 4'd0;
        end
    endgenerate

    generate
        if (HAS_REFRESH_CTRL) begin : g_refresh
            mc_xddr2_refresh_ctrl #(
                .NUM_BANKS        (NUM_BANKS),
                .HAS_POSTPONE     (REF_HAS_POSTPONE),
                .HAS_PULLIN       (REF_HAS_PULLIN),
                .HAS_REFPB        (REF_HAS_REFPB),
                .HAS_DRAIN_BURST  (REF_HAS_DRAIN_BURST)
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
                .grant_was_pb_i  (cmd_op_o == OP_REFPB),
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
        end else begin : g_no_refresh
            assign refresh_req    = refresh_req_i;
            assign refresh_drain  = refresh_drain_i;
            assign w_refresh_kind = refresh_kind_i;
            assign w_refresh_bank = refresh_bank_i;
            wire _unused_ref = &{1'b0, t_refi_i, refi_reload_i, refresh_burst_i,
                                 ref_postpone_i, ref_pullin_i, ref_mode_i,
                                 ref_trefi_pb_i, ref_trfc_pb_i};
        end
    endgenerate

    generate
        if (HAS_PAGE_POLICY) begin : g_page_policy
            mc_page_policy #(
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
        end else begin : g_no_page_policy
            assign w_pp_ap_en     = ap_mode_en_i;
            assign w_pp_ap_close  = ap_close_i;
            assign w_pp_to_req    = timeout_pre_req_i;
            assign w_pp_to_bank   = timeout_pre_bank_i;
            assign stat_page_hit_o   = '0;
            assign stat_row_hit_o    = '{default: '0};
            assign stat_page_miss_o  = '0;
            assign stat_page_empty_o = '0;
            assign stat_act_o        = '0;
            assign stat_pre_o        = '0;
            assign stat_ref_o        = '0;
            assign stat_ref_busy_o   = '0;
            wire _unused_pp = &{1'b0, page_mode_i, page_tr_init_i};
        end
    endgenerate

    assign init_done_o = init_done;

    // ======================================================================
    // Common scheduler-plane core.
    // ======================================================================
    // Pumice maps its single-bit MRR training flag onto maint_extra[0];
    // wider MAINT_EXTRA_WIDTH (andesite v4) passes through full width.
    localparam int MEW = (MAINT_EXTRA_WIDTH > 0) ? MAINT_EXTRA_WIDTH : 1;
    logic w_maint_grant;
    logic [MEW-1:0] w_maint_extra_in;
    logic [MEW-1:0] w_maint_extra_out;
    assign w_maint_extra_in = (MAINT_EXTRA_WIDTH > 0) ? MEW'(maint_extra_i) : '0;

    // ======================================================================
    // mc_bank_timers — per-bank safe timers (open-page).
    // ======================================================================
    mc_bank_timers #(
        .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH),
        .BANK_LA  (4)
    ) u_bank_timers (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .t_rcd_i          (t_rcd_i),
        .t_rp_i           (t_rp_i),
        .t_ras_i          (t_ras_i),
        .t_rc_i           (t_rc_i),
        .t_wr_i           (t_wr_i),
        .t_rtp_i          (t_rtp_i),
        .evt_act_i        (evt_act),
        .evt_rd_i         (evt_rd),
        .evt_wr_i         (evt_wr),
        .evt_pre_i        (evt_pre),
        .evt_ap_i         (evt_ap),
        .evt_rank_i       (evt_rank),
        .evt_bank_i       (evt_bank),
        .evt_row_i        (evt_row),
        .bank_act_ready_la_o (w_bank_act_ready_la),
        .bank_rdwr_ready_la_o(w_bank_rdwr_ready_la),
        .bank_pre_ready_la_o (w_bank_pre_ready_la),
        .bank_act_ready_o (w_bank_act_ready),
        .bank_rdwr_ready_o(w_bank_rdwr_ready),
        .bank_pre_ready_o (w_bank_pre_ready),
        .bank_row_active_o(w_bank_row_active),
        .bank_open_row_o  (w_bank_open_row),
        .bank_state_o     (),
        .obs_act_cnt_nz_o (),
        .obs_preblk_nz_o  (),
        .obs_ras_nz_o     (),
        .obs_ap_pending_o ()
    );

    // ======================================================================
    // mc_global_timers — tFAW/tRRD (per-rank), tWTR/tRTW/tCCD (global),
    // plus optional L/S pair windows (per-(rank,group) ACT, per-group column).
    // ======================================================================
    localparam bit HAS_LS_PAIRS = (NUM_BG > 1);
    logic [BGW_EFF-1:0] w_evt_bg;
    assign w_evt_bg = HAS_LS_PAIRS ? evt_bank[BKW-1 -: BGW_EFF] : '0;

    mc_global_timers #(
        .NUM_RANKS  (NUM_RANKS),
        .NUM_BANKS  (NUM_BANKS),
        .NUM_BG     (NUM_BG),
        .BGW        (BGW_EFF),
        .HAS_LS_PAIRS(HAS_LS_PAIRS)
    ) u_global_timers (
        .mc_clk          (aclk),
        .mc_rst_n        (aresetn),
        .t_faw_i         (t_faw_i),
        .t_rrd_i         (t_rrd_i),
        .t_wtr_global_i  (t_wtr_i),
        .t_rtw_i         (t_rtw_i),
        .t_ccd_i         (t_ccd_i),
        .t_ccd_l_i       (t_ccd_l_i),
        .t_ccd_s_i       (t_ccd_s_i),
        .t_rrd_l_i       (t_rrd_l_i),
        .t_rrd_s_i       (t_rrd_s_i),
        .evt_act_i       (evt_act),
        .evt_act_rank_i  (evt_rank),
        .evt_act_bg_i    (w_evt_bg),
        .evt_rd_i        (evt_rd),
        .evt_wr_i        (evt_wr),
        .evt_col_bg_i    (w_evt_bg),
        .cand_rank_i     ('0),
        .cand_bg_i       (a_cmd_bg),
        .tfaw_window_ok_o(w_tfaw_ok),
        .trrd_window_ok_o(w_trrd_ok),
        .twtr_global_ok_o(w_twtr_ok),
        .trtw_window_ok_o(w_trtw_ok),
        .tccd_window_ok_o(w_tccd_ok),
        .tccd_l_window_ok_o(w_tccd_l_ok),
        .tccd_s_window_ok_o(w_tccd_s_ok),
        .trrd_l_window_ok_o(w_trrd_l_ok),
        .trrd_s_window_ok_o(w_trrd_s_ok),
        .obs_faw_nz_o    (),
        .obs_trrd_nz_o   (),
        .obs_twtr_nz_o   (),
        .obs_trtw_nz_o   (),
        .obs_tccd_nz_o   ()
    );

    // ======================================================================
    // Pick core: BANK_FIFO = per-bank in-order product core (family design);
    // else the FRFCFS research core. Both drive the plane outputs directly
    // (exactly one branch elaborates).
    // ======================================================================
    // rd_ret_busy_i originates in the DFI plane's dfi_clk domain; synchronize
    // to aclk before gating the per-bank scheduler's refresh grant.
    logic r_rd_ret_busy_sync0, r_rd_ret_busy_sync1;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_ret_busy_sync0 <= 1'b0;
            r_rd_ret_busy_sync1 <= 1'b0;
        end else begin
            r_rd_ret_busy_sync0 <= rd_ret_busy_i;
            r_rd_ret_busy_sync1 <= r_rd_ret_busy_sync0;
        end
    )

    generate if (BANK_FIFO) begin : g_bank_sched
        mc_bank_sched #(
            .NUM_RANKS   (NUM_RANKS),
            .NUM_BANKS   (NUM_BANKS),
            .ROW_WIDTH   (ROW_WIDTH),
            .COL_WIDTH   (COL_WIDTH),
            .AXI_ID_WIDTH(IW),
            .NUM_ENTRIES (NUM_ENTRIES),
            .HAS_ZQ      (HAS_ZQ),
            .CLOSE_ON_DRAIN(CLOSE_ON_DRAIN),
            .MAINT_EXTRA_WIDTH(MAINT_EXTRA_WIDTH)
        ) u_bank_sched (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .page_policy_i      (page_policy_i),
            .wr_bh_valid_i      (wr_bh_valid_i),
            .wr_bh_slot_i       (wr_bh_slot_i),
            .wr_bh_row_i        (wr_bh_row_i),
            .wr_bh_col_i        (wr_bh_col_i),
            .wr_bh_id_i         (wr_bh_id_i),
            .wr_bh_last_i       (wr_bh_last_i),
            .wr_bh_empty_i      (wr_bh_empty_i),
            .rd_bh_valid_i      (rd_bh_valid_i),
            .rd_bh_slot_i       (rd_bh_slot_i),
            .rd_bh_row_i        (rd_bh_row_i),
            .rd_bh_col_i        (rd_bh_col_i),
            .rd_bh_id_i         (rd_bh_id_i),
            .rd_bh_empty_i      (rd_bh_empty_i),
            .wr_bh2_valid_i     (wr_bh2_valid_i),
            .wr_bh2_slot_i      (wr_bh2_slot_i),
            .wr_bh2_row_i       (wr_bh2_row_i),
            .wr_bh2_col_i       (wr_bh2_col_i),
            .wr_bh2_id_i        (wr_bh2_id_i),
            .wr_bh2_last_i      (wr_bh2_last_i),
            .rd_bh2_valid_i     (rd_bh2_valid_i),
            .rd_bh2_slot_i      (rd_bh2_slot_i),
            .rd_bh2_row_i       (rd_bh2_row_i),
            .rd_bh2_col_i       (rd_bh2_col_i),
            .rd_bh2_id_i        (rd_bh2_id_i),
            .wr_commit_ready_i  (wr_commit_ready_i),
            .wr_commit_valid_o  (wr_commit_valid_o),
            .wr_commit_slot_o   (wr_commit_slot_o),
            .rd_issue_ready_i   (rd_issue_ready_i),
            .rd_issue_valid_o   (rd_issue_valid_o),
            .rd_issue_slot_o    (rd_issue_slot_o),
            .rd_ret_busy_i      (r_rd_ret_busy_sync1),
            .init_done_i        (init_done),
            .init_cmd_valid_i   (init_cmd_valid),
            .init_cmd_op_i      (init_cmd_op),
            .init_cmd_bank_i    (init_cmd_bank),
            .init_cmd_row_i     (init_cmd_row),
            .refresh_req_i      (refresh_req),
            .refresh_drain_i    (refresh_drain),
            .refresh_kind_i     (w_refresh_kind),
            .refresh_bank_i     (w_refresh_bank),
            .refresh_grant_o    (refresh_grant),
            .t_rfc_i            (t_rfc_i),
            .t_rfc_pb_i         (ref_trfc_pb_i),
            .zq_req_i           (zq_req_i),
            .zq_grant_o         (zq_grant_o),
            .t_zqcs_i           (t_zqcs_i),
            .maint_req_i        (maint_req_i),
            .maint_grant_o      (w_maint_grant),
            .maint_op_i         (maint_op_i),
            .maint_bank_i       (maint_bank_i),
            .maint_row_i        (maint_row_i),
            .maint_col_i        (maint_col_i),
            .maint_extra_i      (maint_extra_i),
            .maint_busy_i       (maint_busy_i),
            .bank_act_ready_i   (w_bank_act_ready),
            .bank_rdwr_ready_i  (w_bank_rdwr_ready),
            .bank_pre_ready_i   (w_bank_pre_ready),
            .bank_act_ready_la_i (w_bank_act_ready_la),
            .bank_rdwr_ready_la_i(w_bank_rdwr_ready_la),
            .bank_pre_ready_la_i (w_bank_pre_ready_la),
            .bank_row_active_i  (w_bank_row_active),
            .bank_open_row_i    (w_bank_open_row),
            .tfaw_ok_i          (w_tfaw_ok),
            .trrd_ok_i          (w_trrd_ok),
            .twtr_ok_i          (w_twtr_ok),
            .trtw_ok_i          (w_trtw_ok),
            .tccd_ok_i          (w_tccd_ok),
            .evt_act_o          (evt_act),
            .evt_rd_o           (evt_rd),
            .evt_wr_o           (evt_wr),
            .evt_pre_o          (evt_pre),
            .evt_ap_o           (evt_ap),
            .evt_rank_o         (evt_rank),
            .evt_bank_o         (evt_bank),
            .evt_row_o          (evt_row),
            .cmd_valid_o        (a_cmd_valid),
            .cmd_ready_i        (a_cmd_ready),
            .cmd_op_o           (a_cmd_op),
            .cmd_rank_o         (a_cmd_rank),
            .cmd_bank_o         (a_cmd_bank),
            .cmd_row_o          (a_cmd_row),
            .cmd_col_o          (a_cmd_col),
            .cmd_ap_o           (a_cmd_ap),
            .cmd_extra_o        (a_cmd_extra),
            .stall_bp_o         (stall_bp_o),
            .stall_refresh_o    (stall_refresh_o),
            .stall_turnaround_o (stall_turnaround_o),
            .stall_tccd_o       (stall_tccd_o),
            .stall_actlimit_o   (stall_actlimit_o),
            .stall_banktimer_o  (stall_banktimer_o),
            .stall_noreq_o      (stall_noreq_o),
            .stall_zq_o         (stall_zq_o)
        );
        assign a_cmd_bg = '0;
    end else begin : g_arbiter
    // ======================================================================
    // mc_cmd_arbiter — the FRFCFS research pick core.
    // ======================================================================
    mc_cmd_arbiter #(
        .NUM_RANKS   (NUM_RANKS),
        .NUM_BANKS   (NUM_BANKS),
        .NUM_BG      (NUM_BG),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH),
        .AXI_ID_WIDTH(IW),
        .NUM_ENTRIES (NUM_ENTRIES),
        .AGE_WIDTH   (AGE_WIDTH),
        .HAS_ZQ      (HAS_ZQ),
        .MAINT_EXTRA_WIDTH(MAINT_EXTRA_WIDTH),
        .CLOSE_ON_DRAIN(CLOSE_ON_DRAIN),
        .BANK_IN_ORDER (BANK_IN_ORDER)
    ) u_arbiter (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (page_policy_i),
        .ap_mode_en_i       (w_pp_ap_en),
        .ap_close_i         (w_pp_ap_close),
        .timeout_pre_req_i  (w_pp_to_req),
        .timeout_pre_bank_i (w_pp_to_bank),
        .init_done_i        (init_done),
        .init_cmd_valid_i   (init_cmd_valid),
        .init_cmd_op_i      (init_cmd_op),
        .init_cmd_bank_i    (init_cmd_bank),
        .init_cmd_row_i     (init_cmd_row),
        .refresh_req_i      (refresh_req),
        .refresh_drain_i    (refresh_drain),
        .refresh_grant_o    (refresh_grant),
        .refresh_kind_i     (w_refresh_kind),
        .refresh_bank_i     (w_refresh_bank),
        .t_rfc_i            (t_rfc_i),
        .t_rfc_pb_i         (ref_trfc_pb_i),
        .zq_req_i           (zq_req_i),
        .zq_grant_o         (zq_grant_o),
        .t_zqcs_i           (t_zqcs_i),
        .maint_req_i        (maint_req_i),
        .maint_grant_o      (w_maint_grant),
        .maint_op_i         (maint_op_i),
        .maint_bank_i       (maint_bank_i),
        .maint_row_i        (maint_row_i),
        .maint_col_i        (maint_col_i),
        .maint_extra_i      (maint_extra_i),
        .maint_busy_i       (maint_busy_i),
        .bank_act_ready_i   (w_bank_act_ready),
        .bank_rdwr_ready_i  (w_bank_rdwr_ready),
        .bank_pre_ready_i   (w_bank_pre_ready),
        .bank_act_ready_la_i (w_bank_act_ready_la),
        .bank_rdwr_ready_la_i(w_bank_rdwr_ready_la),
        .bank_pre_ready_la_i (w_bank_pre_ready_la),
        .bank_row_active_i  (w_bank_row_active),
        .bank_open_row_i    (w_bank_open_row),
        .tfaw_ok_i          (w_tfaw_ok),
        .trrd_ok_i          (w_trrd_ok),
        .twtr_ok_i          (w_twtr_ok),
        .trtw_ok_i          (w_trtw_ok),
        .tccd_ok_i          (w_tccd_ok),
        .tccd_l_ok_i        (w_tccd_l_ok),
        .trrd_l_ok_i        (w_trrd_l_ok),
        .pick_group_o       (a_cmd_bg),
        .t_ccd_i            (t_ccd_i),
        .wr_sch_valid_i     (wr_sch_valid_i),
        .wr_sch_bank_i      (wr_sch_bank_i),
        .wr_sch_row_i       (wr_sch_row_i),
        .wr_sch_col_i       (wr_sch_col_i),
        .wr_sch_older_i     (wr_sch_older_i),
        .sched_order_mode_i (sched_order_mode_i),
        .sched_row_sel_i    (sched_row_sel_i),
        .sched_col_sel_i    (sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i (sched_wr_high_wm_i),
        .sched_wr_batch_max_i (sched_wr_batch_max_i),
        .sched_wr_low_wm_i  (sched_wr_low_wm_i),
        .sched_prio_sub_i   (sched_prio_sub_i),
        .sched_qos_en_i     (sched_qos_en_i),
        .rd_sch_qos_i       (rd_sch_qos_i),
        .wr_sch_qos_i       (wr_sch_qos_i),
        .wr_sch_age_exceed_i(wr_sch_age_exceed_i),
        .wr_sch_head_rel_i  (wr_sch_head_rel_i),
        .rd_sch_age_exceed_i(rd_sch_age_exceed_i),
        .rd_sch_head_rel_i  (rd_sch_head_rel_i),
        .wr_commit_ready_i  (wr_commit_ready_i),
        .wr_commit_valid_o  (wr_commit_valid_o),
        .wr_commit_slot_o   (wr_commit_slot_o),
        .rd_sch_valid_i     (rd_sch_valid_i),
        .rd_sch_bank_i      (rd_sch_bank_i),
        .rd_sch_row_i       (rd_sch_row_i),
        .rd_sch_col_i       (rd_sch_col_i),
        .rd_sch_older_i     (rd_sch_older_i),
        .rd_issue_ready_i   (rd_issue_ready_i),
        .rd_issue_valid_o   (rd_issue_valid_o),
        .rd_issue_slot_o    (rd_issue_slot_o),
        .evt_act_o          (evt_act),
        .evt_rd_o           (evt_rd),
        .evt_wr_o           (evt_wr),
        .evt_pre_o          (evt_pre),
        .evt_ap_o           (evt_ap),
        .evt_rank_o         (evt_rank),
        .evt_bank_o         (evt_bank),
        .evt_row_o          (evt_row),
        .cmd_valid_o        (a_cmd_valid),
        .cmd_ready_i        (a_cmd_ready),
        .cmd_op_o           (a_cmd_op),
        .cmd_rank_o         (a_cmd_rank),
        .cmd_bank_o         (a_cmd_bank),
        .cmd_row_o          (a_cmd_row),
        .cmd_col_o          (a_cmd_col),
        .cmd_ap_o           (a_cmd_ap),
        .cmd_extra_o        (a_cmd_extra),
        .stall_bp_o         (stall_bp_o),
        .stall_refresh_o    (stall_refresh_o),
        .stall_turnaround_o (stall_turnaround_o),
        .stall_tccd_o       (stall_tccd_o),
        .stall_actlimit_o   (stall_actlimit_o),
        .stall_banktimer_o  (stall_banktimer_o),
        .stall_noreq_o      (stall_noreq_o),
        .stall_zq_o         (stall_zq_o)
    );
    end endgenerate

    assign maint_grant_o = w_maint_grant;
    generate
        if (MAINT_EXTRA_WIDTH > 0) begin : g_extra_out
            assign cmd_extra_o = w_maint_extra_out;
        end else begin : g_no_extra
            assign cmd_extra_o = '0;
        end
    endgenerate

    // ======================================================================
    // Output command FIFO (scheduler -> DFI). Packs {ap,col,row,bg,bank,rank,extra,op}.
    // ======================================================================
    localparam int CMD_W = $bits(dram_op_e) + RKW + BKW + BGW_EFF + ROW_WIDTH + COL_WIDTH + 1 + MAINT_EXTRA_WIDTH;
    logic [CMD_W-1:0] w_cmd_wr_data, w_cmd_rd_data;
    assign w_cmd_wr_data = {a_cmd_ap, a_cmd_col, a_cmd_row, a_cmd_bg, a_cmd_bank, a_cmd_rank, a_cmd_extra, a_cmd_op};

    logic w_cmd_rd_valid, w_cmd_pop;
    dram_op_e w_rd_op;
    gaxi_fifo_sync #(.DATA_WIDTH(CMD_W), .DEPTH(CMD_FIFO_DEPTH)) u_cmd_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (a_cmd_valid),
        .wr_ready   (a_cmd_ready),
        .wr_data    (w_cmd_wr_data),
        .rd_ready   (w_cmd_pop),
        .count      (),
        .rd_valid   (w_cmd_rd_valid),
        .rd_data    (w_cmd_rd_data)
    );

    // ---- fixed-delay release (CMD_DELAY) ------------------------------------
    localparam int TOKW = $clog2(CMD_FIFO_DEPTH + 1);
    logic            w_cmd_push, w_tok_mature;
    logic [TOKW-1:0] r_tok_cnt;
    assign w_cmd_push = a_cmd_valid && a_cmd_ready;
    generate if (CMD_DELAY > 0) begin : g_cmd_delay
        logic [CMD_DELAY-1:0] r_tok_shift;
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) r_tok_shift <= '0;
            else if (CMD_DELAY > 1)     r_tok_shift <= {r_tok_shift[CMD_DELAY-2:0], w_cmd_push};
            else                        r_tok_shift <= CMD_DELAY'(w_cmd_push);
        )
        assign w_tok_mature = r_tok_shift[CMD_DELAY-1];
    end else begin : g_cmd_nodelay
        assign w_tok_mature = w_cmd_push;
    end endgenerate

    assign cmd_valid_o = w_cmd_rd_valid && ((r_tok_cnt != '0) || w_tok_mature);
    assign w_cmd_pop   = cmd_valid_o && cmd_ready_i;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_tok_cnt <= '0;
        else r_tok_cnt <= r_tok_cnt + (w_tok_mature ? TOKW'(1) : TOKW'(0))
                                    - (w_cmd_pop    ? TOKW'(1) : TOKW'(0));
    )

    assign {cmd_ap_o, cmd_col_o, cmd_row_o, cmd_bg_o, cmd_bank_o, cmd_rank_o, w_maint_extra_out, w_rd_op} = w_cmd_rd_data;
    assign cmd_op_o    = w_rd_op;

    assign bank_row_active_o = w_bank_row_active;
    assign bank_open_row_o   = w_bank_open_row;

    assign busy_o = !init_done || refresh_req || w_cmd_rd_valid
                 || (|w_bank_row_active[0]);

    assign cmd_accept_o    = a_cmd_valid && a_cmd_ready;
    assign cmd_accept_op_o = a_cmd_op;

    // ---- optional command-history scoreboard -------------------------------
    generate if (HAS_CMD_HISTORY && (CMD_HISTORY_EN != 0)) begin : g_cmd_history
        mc_cmd_history_checker #(
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

endmodule : mc_scheduler_plane
