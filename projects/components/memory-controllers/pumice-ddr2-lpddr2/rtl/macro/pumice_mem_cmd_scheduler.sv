// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_mem_cmd_scheduler
// Purpose: The pumice command-scheduling layer. Wires the command arbiter to
//          the per-bank safe timers, global (bus/rank) timers, refresh
//          controller, init sequencer + mode-register shadow, and an output
//          command FIFO. Emits a single abstract DRAM command stream
//          {op,rank,bank,row,col,ap} for the DFI layer to pack onto phases.
//
//          PHY/nphases-agnostic; single-issue; single controller clock (aclk).
//          The CAM sched-lookup / oldest / commit / issue ports are EXTERNAL
//          (the CAMs live in pumice_axi4_ifc).
//
// Documentation: rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_mem_cmd_scheduler
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    // Optional issued-command-history scoreboard (audit-only; see the generate
    // at the end). HIST_* are the JEDEC same-bank windows in MC cycles (0 = a
    // check disabled); HIST_T_RFC should match the t_rfc_i the TB programs.
    parameter int CMD_HISTORY_EN = 0,   // int (not bit): -G overrides are 32-bit
    parameter int HIST_T_RCD  = 0,
    parameter int HIST_T_RP   = 0,
    parameter int HIST_T_RAS  = 0,
    parameter int HIST_T_RFC  = 8,
    parameter int HIST_T_WTR  = 0,   // global WR->RD turnaround window
    parameter int HIST_T_RTW  = 0,   // global RD->WR turnaround window
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int CMD_FIFO_DEPTH = 8,
    parameter int N_LU  = NUM_BANKS,
    parameter int RKW   = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int IW    = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,

    // ---- config ----
    input  page_policy_e              page_policy_i,

    // ---- runtime page-policy CSR fields + telemetry (PUMICE-006 Axis 2) ----
    input  logic [1:0]                sched_order_mode_i, // SCHED_POLICY.order_mode
    input  logic [1:0]                sched_row_sel_i,    // SCHED_POLICY.row_sel
    input  logic [1:0]                sched_col_sel_i,    // SCHED_POLICY.col_sel
    input  logic [1:0]                sched_access_pref_i,// SCHED_POLICY.access_pref
    input  logic [7:0]                sched_wr_high_wm_i, // SCHED_WR_WM.wr_high_wm
    input  logic [7:0]                sched_wr_low_wm_i,  // SCHED_WR_WM.wr_low_wm
    input  logic [1:0]                sched_prio_sub_i,   // SCHED_POLICY.prio_sub
    input  logic                      sched_qos_en_i,     // SCHED_POLICY.qos_en
    input  logic [2:0]                page_mode_i,        // PAGE_POLICY_CFG.policy_mode
    input  logic                      page_scope_i,
    input  logic [7:0]                page_tr_init_i,
    input  logic [7:0]                page_tr_min_i,
    input  logic [7:0]                page_tr_max_i,
    input  logic [7:0]                page_tr_step_i,
    input  logic [3:0]                page_mc_high_i,
    input  logic [3:0]                page_mc_low_i,
    input  logic [3:0]                page_mc_init_i,
    input  logic [15:0]               page_check_ivl_i,
    input  logic [3:0]                page_ctr_thresh_i,
    input  logic [3:0]                page_ctr_init_i,
    input  logic [7:0]                page_rbl_thresh_i,
    input  logic [1:0]                page_rbl_ways_i,
    input  logic [3:0]                page_rbl_sets_i,
    input  logic [15:0]               page_rbl_ivl_i,
    output logic [31:0]               stat_page_hit_o,
    output logic [31:0]               stat_page_miss_o,
    output logic [31:0]               stat_page_empty_o,
    output logic [31:0]               stat_act_o,
    output logic [31:0]               stat_pre_o,
    output logic [31:0]               stat_ref_o,
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
    input  logic [15:0]               t_rfc_i,          // mission-mode REF recovery (arbiter)
    input  logic [3:0]                refresh_burst_i,
    input  logic [3:0]                ref_postpone_i,   // REF_CTRL.postpone_limit
    input  logic [3:0]                ref_pullin_i,     // REF_CTRL.pullin_limit
    input  logic [1:0]                ref_mode_i,       // REF_CTRL.mode (2=REFpb)
    input  logic [15:0]               ref_trefi_pb_i,   // REF_TIMING_PB.trefi_pb
    input  logic [7:0]                ref_trfc_pb_i,    // REF_TIMING_PB.trfc_pb
    // init timing
    input  logic [15:0]               t_init_wait_i,
    input  logic [15:0]               t_dll_wait_i,
    input  logic [7:0]                t_mrd_wait_i,
    input  logic [7:0]                t_rp_wait_i,
    input  logic [7:0]                t_rfc_wait_i,
    // DDR2 mode-register values (CSR-backed MR0..MR3.VAL) for the init MRS chain
    input  logic [15:0]               mr0_i,
    input  logic [15:0]               mr1_i,
    input  logic [15:0]               mr2_i,
    input  logic [15:0]               mr3_i,
    input  logic                      init_restart_i,   // CTRL.init_force_restart

    // ---- DFI init handshake (to/from the PHY via the DFI layer) ----
    output logic                      dfi_init_start_o,
    input  logic                      dfi_init_complete_i,
    output logic                      init_done_o,

    // ---- mode-register shadow (to DFI layer) ----
    output logic [3:0]                cl_o,
    output logic [3:0]                cwl_o,
    output logic [3:0]                bl_o,

    // ---- CAM per-entry vectors (external: pumice_axi4_ifc) ----
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

    // ---- output command stream (to DFI layer) ----
    output logic                      cmd_valid_o,
    input  logic                      cmd_ready_i,
    output dram_op_e                  cmd_op_o,
    output logic [RKW-1:0]            cmd_rank_o,
    output logic [BKW-1:0]            cmd_bank_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,

    output logic                      busy_o
);

    // ---- internal nets ----
    logic init_done;
    logic init_cmd_valid; dram_op_e init_cmd_op;
    logic [BKW-1:0] init_cmd_bank; logic [ROW_WIDTH-1:0] init_cmd_row;
    logic mr_seq_we; logic [4:0] mr_seq_index; logic [15:0] mr_seq_data;

    logic refresh_req, refresh_drain, refresh_grant;

    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_act_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_pre_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 w_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  w_bank_open_row;

    logic [NUM_RANKS-1:0] w_tfaw_ok, w_trrd_ok;
    logic w_twtr_ok, w_trtw_ok, w_tccd_ok;

    logic evt_act, evt_rd, evt_wr, evt_pre, evt_ap;
    logic [RKW-1:0] evt_rank; logic [BKW-1:0] evt_bank; logic [ROW_WIDTH-1:0] evt_row;

    // arbiter -> cmd FIFO
    logic          a_cmd_valid, a_cmd_ready;
    dram_op_e      a_cmd_op;
    logic [RKW-1:0] a_cmd_rank; logic [BKW-1:0] a_cmd_bank;
    logic [ROW_WIDTH-1:0] a_cmd_row; logic [COL_WIDTH-1:0] a_cmd_col; logic a_cmd_ap;

    assign init_done_o = init_done;

    // ======================================================================
    // init_sequencer — JEDEC MRS init; gates traffic until done.
    // ======================================================================
    init_sequencer #(
        .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH)
    ) u_init (
        .mc_clk(aclk), .mc_rst_n(aresetn),
        .memtype_i(memtype_i),
        .t_init_wait_i(t_init_wait_i), .t_dll_wait_i(t_dll_wait_i),
        .t_mrd_wait_i(t_mrd_wait_i), .t_rp_wait_i(t_rp_wait_i), .t_rfc_wait_i(t_rfc_wait_i),
        .mr0_i(mr0_i), .mr1_i(mr1_i), .mr2_i(mr2_i), .mr3_i(mr3_i),
        .init_restart_i(init_restart_i),
        .dfi_init_start_o(dfi_init_start_o), .dfi_init_complete_i(dfi_init_complete_i),
        .mr_seq_we_o(mr_seq_we), .mr_seq_index_o(mr_seq_index), .mr_seq_data_o(mr_seq_data),
        .init_cmd_valid_o(init_cmd_valid), .init_cmd_op_o(init_cmd_op),
        .init_cmd_bank_o(init_cmd_bank), .init_cmd_row_o(init_cmd_row),
        .zqcl_req_o(), .zqcl_grant_i(1'b0),
        .init_busy_o(), .init_done_o(init_done)
    );

    // ======================================================================
    // mode_register — shadow updated by init MRS; supplies CL/CWL/BL.
    // ======================================================================
    mode_register #(
        .NUM_RANKS(NUM_RANKS)
    ) u_mode_reg (
        .mc_clk(aclk), .mc_rst_n(aresetn),
        .memtype_i(memtype_i),
        .mr_we_i(mr_seq_we), .mr_index_i(mr_seq_index), .mr_data_i(mr_seq_data),
        .mr_rank_i('0),
        .mr_req_o(), .mr_grant_i(1'b0), .mr_req_index_o(), .mr_req_data_o(), .mr_req_rank_o(),
        .cl_o(cl_o), .cwl_o(cwl_o), .bl_o(bl_o),
        .al_o(), .drv_strength_o(), .odt_o()
    );

    // ======================================================================
    // refresh_ctrl — tREFI + 8-deep postpone; enabled after init.
    // ======================================================================
    // REFpb is LPDDR2-only (DDR2 has no per-bank refresh command); an
    // unsupported mode select degrades to REFab rather than emitting an
    // illegal command.
    logic            w_refpb_en;
    logic            w_refresh_kind;
    logic [BKW-1:0]  w_refresh_bank;
    assign w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR2);

    refresh_ctrl #(
        .NUM_BANKS(NUM_BANKS)
    ) u_refresh (
        .mc_clk(aclk), .mc_rst_n(aresetn),
        .t_refi_i(t_refi_i), .trefi_pb_i(ref_trefi_pb_i),
        .refresh_burst_i(refresh_burst_i),
        .refpb_mode_i(w_refpb_en), .enable_i(init_done),
        .postpone_limit_i(ref_postpone_i), .pullin_limit_i(ref_pullin_i),
        .demand_i(|rd_sch_valid_i || |wr_sch_valid_i),
        .refresh_req_o(refresh_req), .refresh_grant_i(refresh_grant),
        // refresh_grant fires at the arbiter's FIFO-PUSH, so the granted op is
        // the ARBITER-side a_cmd_op — cmd_op_o is the FIFO HEAD (an older
        // command) and sampling it stalls the rotor mirror erratically.
        .grant_was_pb_i(a_cmd_op == OP_REFPB),
        .pending_refreshes_o(),
        .refresh_drain_active_o(refresh_drain),
        .refresh_kind_o(w_refresh_kind), .refresh_bank_o(w_refresh_bank),
        .obs_refi_cnt_o(), .obs_drain_remaining_o(), .obs_bank_rotor_o(),
        .obs_grants_total_o(), .obs_pullin_credit_o()
    );

    // ======================================================================
    // pumice_bank_timers — per-bank safe timers (open-page).
    // ======================================================================
    pumice_bank_timers #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH)
    ) u_bank_timers (
        .aclk(aclk), .aresetn(aresetn),
        .t_rcd_i(t_rcd_i), .t_rp_i(t_rp_i), .t_ras_i(t_ras_i), .t_rc_i(t_rc_i),
        .t_wr_i(t_wr_i), .t_rtp_i(t_rtp_i),
        .evt_act_i(evt_act), .evt_rd_i(evt_rd), .evt_wr_i(evt_wr), .evt_pre_i(evt_pre),
        .evt_ap_i(evt_ap), .evt_rank_i(evt_rank), .evt_bank_i(evt_bank), .evt_row_i(evt_row),
        .bank_act_ready_o(w_bank_act_ready), .bank_rdwr_ready_o(w_bank_rdwr_ready),
        .bank_pre_ready_o(w_bank_pre_ready), .bank_row_active_o(w_bank_row_active),
        .bank_open_row_o(w_bank_open_row), .bank_state_o(),
        .obs_act_cnt_nz_o(), .obs_preblk_nz_o(), .obs_ras_nz_o(), .obs_ap_pending_o()
    );

    // ======================================================================
    // global_timers — tFAW/tRRD (per-rank), tWTR/tRTW/tCCD (global).
    // ======================================================================
    global_timers #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS)
    ) u_global_timers (
        .mc_clk(aclk), .mc_rst_n(aresetn),
        .t_faw_i(t_faw_i), .t_rrd_i(t_rrd_i), .t_wtr_global_i(t_wtr_i),
        .t_rtw_i(t_rtw_i), .t_ccd_i(t_ccd_i),
        .evt_act_i(evt_act), .evt_act_rank_i(evt_rank), .evt_rd_i(evt_rd), .evt_wr_i(evt_wr),
        .tfaw_window_ok_o(w_tfaw_ok), .trrd_window_ok_o(w_trrd_ok),
        .twtr_global_ok_o(w_twtr_ok), .trtw_window_ok_o(w_trtw_ok), .tccd_window_ok_o(w_tccd_ok),
        .obs_faw_nz_o(), .obs_trrd_nz_o(), .obs_twtr_nz_o(), .obs_trtw_nz_o(), .obs_tccd_nz_o()
    );

    // ======================================================================
    // pumice_cmd_arbiter — the pick core.
    // ======================================================================
    // pumice_page_policy — runtime Axis-2 engine + telemetry. Watches the
    // arbiter's issued stream (valid && ready, identical tap to the
    // cmd-history checker) and the registered bank-state buses.
    logic                  w_pp_ap_en;
    logic [NUM_BANKS-1:0]  w_pp_ap_close;
    logic                  w_pp_to_req;
    logic [BKW-1:0]        w_pp_to_bank;

    pumice_page_policy #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH)
    ) u_page_policy (
        .aclk(aclk), .aresetn(aresetn),
        .policy_mode_i(page_mode_i), .policy_scope_i(page_scope_i),
        .tr_init_i(page_tr_init_i), .tr_min_i(page_tr_min_i),
        .tr_max_i(page_tr_max_i), .tr_step_i(page_tr_step_i),
        .mc_high_thr_i(page_mc_high_i), .mc_low_thr_i(page_mc_low_i),
        .mc_init_i(page_mc_init_i), .check_interval_i(page_check_ivl_i),
        .ctr_thresh_i(page_ctr_thresh_i), .ctr_init_i(page_ctr_init_i),
        .rbl_miss_thresh_i(page_rbl_thresh_i), .rbl_ways_i(page_rbl_ways_i),
        .rbl_sets_i(page_rbl_sets_i), .rbl_reset_ivl_i(page_rbl_ivl_i),
        .cmd_valid_i(cmd_valid_o && cmd_ready_i),
        .cmd_op_i(cmd_op_o), .cmd_bank_i(cmd_bank_o), .cmd_row_i(cmd_row_o),
        .bank_row_active_i(w_bank_row_active[0]),
        .bank_open_row_i(w_bank_open_row[0]),
        .ap_mode_en_o(w_pp_ap_en), .ap_close_o(w_pp_ap_close),
        .timeout_pre_req_o(w_pp_to_req), .timeout_pre_bank_o(w_pp_to_bank),
        .stat_page_hit_o(stat_page_hit_o), .stat_page_miss_o(stat_page_miss_o),
        .stat_page_empty_o(stat_page_empty_o), .stat_act_o(stat_act_o),
        .stat_pre_o(stat_pre_o), .stat_ref_o(stat_ref_o)
    );

    pumice_cmd_arbiter #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH),
        .COL_WIDTH(COL_WIDTH), .AXI_ID_WIDTH(IW), .NUM_ENTRIES(NUM_ENTRIES),
        .AGE_WIDTH(AGE_WIDTH)
    ) u_arbiter (
        .aclk(aclk), .aresetn(aresetn), .page_policy_i(page_policy_i),
        .ap_mode_en_i(w_pp_ap_en), .ap_close_i(w_pp_ap_close),
        .timeout_pre_req_i(w_pp_to_req), .timeout_pre_bank_i(w_pp_to_bank),
        .init_done_i(init_done), .init_cmd_valid_i(init_cmd_valid),
        .init_cmd_op_i(init_cmd_op), .init_cmd_bank_i(init_cmd_bank), .init_cmd_row_i(init_cmd_row),
        .refresh_req_i(refresh_req), .refresh_drain_i(refresh_drain), .refresh_grant_o(refresh_grant),
        .refresh_kind_i(w_refresh_kind), .refresh_bank_i(w_refresh_bank),
        .t_rfc_i(t_rfc_i), .t_rfc_pb_i(ref_trfc_pb_i),
        .bank_act_ready_i(w_bank_act_ready), .bank_rdwr_ready_i(w_bank_rdwr_ready),
        .bank_pre_ready_i(w_bank_pre_ready), .bank_row_active_i(w_bank_row_active),
        .bank_open_row_i(w_bank_open_row),
        .tfaw_ok_i(w_tfaw_ok), .trrd_ok_i(w_trrd_ok), .twtr_ok_i(w_twtr_ok),
        .trtw_ok_i(w_trtw_ok), .tccd_ok_i(w_tccd_ok),
        .wr_sch_valid_i(wr_sch_valid_i), .wr_sch_bank_i(wr_sch_bank_i), .wr_sch_row_i(wr_sch_row_i),
        .wr_sch_col_i(wr_sch_col_i), .wr_sch_older_i(wr_sch_older_i),
        .sched_order_mode_i(sched_order_mode_i),
        .sched_row_sel_i(sched_row_sel_i), .sched_col_sel_i(sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i(sched_wr_high_wm_i), .sched_wr_low_wm_i(sched_wr_low_wm_i),
        .sched_prio_sub_i(sched_prio_sub_i), .sched_qos_en_i(sched_qos_en_i),
        .rd_sch_qos_i(rd_sch_qos_i), .wr_sch_qos_i(wr_sch_qos_i),
        .wr_sch_age_exceed_i(wr_sch_age_exceed_i), .wr_sch_head_rel_i(wr_sch_head_rel_i),
        .rd_sch_age_exceed_i(rd_sch_age_exceed_i), .rd_sch_head_rel_i(rd_sch_head_rel_i),
        .wr_commit_ready_i(wr_commit_ready_i),
        .wr_commit_valid_o(wr_commit_valid_o), .wr_commit_slot_o(wr_commit_slot_o),
        .rd_sch_valid_i(rd_sch_valid_i), .rd_sch_bank_i(rd_sch_bank_i), .rd_sch_row_i(rd_sch_row_i),
        .rd_sch_col_i(rd_sch_col_i), .rd_sch_older_i(rd_sch_older_i),
        .rd_issue_ready_i(rd_issue_ready_i),
        .rd_issue_valid_o(rd_issue_valid_o), .rd_issue_slot_o(rd_issue_slot_o),
        .evt_act_o(evt_act), .evt_rd_o(evt_rd), .evt_wr_o(evt_wr), .evt_pre_o(evt_pre),
        .evt_ap_o(evt_ap), .evt_rank_o(evt_rank), .evt_bank_o(evt_bank), .evt_row_o(evt_row),
        .cmd_valid_o(a_cmd_valid), .cmd_ready_i(a_cmd_ready), .cmd_op_o(a_cmd_op),
        .cmd_rank_o(a_cmd_rank), .cmd_bank_o(a_cmd_bank), .cmd_row_o(a_cmd_row),
        .cmd_col_o(a_cmd_col), .cmd_ap_o(a_cmd_ap)
    );

    // ======================================================================
    // Output command FIFO (scheduler -> DFI). Packs {op,rank,bank,row,col,ap}.
    // ======================================================================
    localparam int CMD_W = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1;
    logic [CMD_W-1:0] w_cmd_wr_data, w_cmd_rd_data;
    assign w_cmd_wr_data = {a_cmd_ap, a_cmd_col, a_cmd_row, a_cmd_bank, a_cmd_rank,
                            a_cmd_op};

    logic w_cmd_rd_valid;
    dram_op_e w_rd_op;
    gaxi_fifo_sync #(.DATA_WIDTH(CMD_W), .DEPTH(CMD_FIFO_DEPTH)) u_cmd_fifo (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(a_cmd_valid), .wr_ready(a_cmd_ready), .wr_data(w_cmd_wr_data),
        .rd_ready(cmd_ready_i), .count(), .rd_valid(w_cmd_rd_valid), .rd_data(w_cmd_rd_data)
    );

    assign {cmd_ap_o, cmd_col_o, cmd_row_o, cmd_bank_o, cmd_rank_o, w_rd_op} = w_cmd_rd_data;
    assign cmd_op_o    = w_rd_op;
    assign cmd_valid_o = w_cmd_rd_valid;

    assign busy_o = !init_done || refresh_req || w_cmd_rd_valid
                 || (|w_bank_row_active[0]);

    // ---- optional command-history scoreboard (CMD_HISTORY_EN) ---------------
    // Fine-grained per-(rank,bank) shift-register record of the ISSUED stream
    // (valid && ready, i.e. DFI issue order), auditing the JEDEC same-bank
    // sequencing the coarse registered readiness can miss (REFab-with-row-open,
    // positional tRCD/tRP/tRAS/tRFC). Generate-gated, default OFF: zero cost in
    // the release build, always COMPILED (no ifdef rot). DV enables it with
    // -GCMD_HISTORY_EN=1; the assertions are simulation-only ($fatal), and the
    // history regs are synthesizable if an ILA build ever wants the trace.
    generate if (CMD_HISTORY_EN != 0) begin : g_cmd_history
        pumice_cmd_history_checker #(
            .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .DEPTH(32),
            .T_RCD(HIST_T_RCD), .T_RP(HIST_T_RP),
            .T_RAS(HIST_T_RAS), .T_RFC(HIST_T_RFC),
            .T_WTR(HIST_T_WTR), .T_RTW(HIST_T_RTW)
        ) u_cmd_history (
            .clk        (aclk),
            .rst_n      (aresetn),
            .cmd_valid_i(cmd_valid_o && cmd_ready_i),
            .cmd_op_i   (cmd_op_o),
            .cmd_rank_i (cmd_rank_o),
            .cmd_bank_i (cmd_bank_o)
        );
    end endgenerate

endmodule : pumice_mem_cmd_scheduler
