// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_scheduler_layer
// Purpose: The command-scheduling layer — the scoria-carried scheduler with
//          the andesite bank-group-aware L/S admission delta (ANDESITE L/S
//          DELTA). See andesite_mas ch02_blocks/05_scheduler.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_scheduler_layer per andesite HAS ch02 (MODIFIED); the
// andesite delta is marked ANDESITE L/S DELTA. This header is free-form
// provenance.
//
// Author: sean galloway
// Created: 2026-10-04 (carried, andesite delta applied)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_scheduler_layer
    import andesite_pkg::*;
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
    parameter int HIST_T_RRD  = 0,   // global ACT->ACT rate limit (ISSUE-019)
    parameter int HIST_T_FAW  = 0,   // global 4-ACT window (ISSUE-019)
    parameter int HIST_T_RTW  = 0,   // global RD->WR turnaround window
    parameter int NUM_BANKS   = 8,
    // ANDESITE L/S DELTA (P3 review I-1): bank-group count, passed to the
    // arbiter and used for the event/pick group wires below (1 = LPDDR4
    // degeneration, no memtype branch).
    parameter int NUM_BG      = 4,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int CMD_FIFO_DEPTH = 16,
    // Fixed release delay of the command stream, aclk cycles (0 = none). Every
    // command leaves the cmd FIFO exactly CMD_DELAY cycles after it entered
    // (absent DFI back-pressure), so the spacing the arbiter enforced is kept
    // while a WR's data -- committed with the command, drained at a fixed
    // latency -- reaches the DFI no later than the command does.
    parameter int CMD_DELAY      = 6,
    parameter int N_LU  = NUM_BANKS,
    parameter int RKW   = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    // Chip selects track ranks on this family: one CS_n per rank. Kept as its
    // own parameter because the DFI v3.1 leveling handshake is per-CS, not
    // per-rank, and the two need not stay equal on a future part.
    parameter int NUM_CS = NUM_RANKS,
    parameter int CSW   = (NUM_CS > 1) ? $clog2(NUM_CS) : 1,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int IW    = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,

    // ---- config ----
    input  page_policy_e              page_policy_i,

    // ---- runtime page-policy CSR fields + telemetry (TASK-001 Axis 2) ----
    input  logic [1:0]                sched_order_mode_i, // SCHED_POLICY.order_mode
    input  logic [1:0]                sched_row_sel_i,    // SCHED_POLICY.row_sel
    input  logic [1:0]                sched_col_sel_i,    // SCHED_POLICY.col_sel
    input  logic [1:0]                sched_access_pref_i,// SCHED_POLICY.access_pref
    input  logic [7:0]                sched_wr_high_wm_i, // SCHED_WR_WM.wr_high_wm
    input  logic [7:0]                sched_wr_batch_max_i, // SCHED_WR_WM.wr_batch_max
    input  logic [7:0]                sched_wr_low_wm_i,  // SCHED_WR_WM.wr_low_wm
    input  logic [1:0]                sched_prio_sub_i,   // SCHED_POLICY.prio_sub
    input  logic                      sched_qos_en_i,     // SCHED_POLICY.qos_en
    input  logic [2:0]                page_mode_i,        // PAGE_POLICY_CFG.policy_mode
    input  logic [7:0]                page_tr_init_i,
    // stall-cause attribution from the arbiter (TASK-006)
    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stall_zq_o,
    output logic [31:0]               stat_page_hit_o,
    output logic [31:0]               stat_row_hit_o [NUM_BANKS],  // per-bank row hits (BUG-020)
    output logic [31:0]               stat_page_miss_o,
    output logic [31:0]               stat_page_empty_o,
    output logic [31:0]               stat_act_o,
    output logic [31:0]               stat_pre_o,
    output logic [31:0]               stat_ref_o,
    // TASK-012: refreshes that fired with work pending (see page_policy)
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
    // ANDESITE L/S DELTA: the long/short pair CSRs (tCCD_L/S, tRRD_L/S).
    input  logic [7:0]                t_ccd_l_i,
    input  logic [7:0]                t_ccd_s_i,
    input  logic [7:0]                t_rrd_l_i,
    input  logic [7:0]                t_rrd_s_i,
    input  logic [15:0]               t_refi_i,
    // DV/bring-up knob: pulse to reload the tREFI countdown immediately
    // with the current t_refi_i (it otherwise reloads only on expiry).
    // Tie to 0 in production -- no effect unless pulsed.
    input  logic                      refi_reload_i,
    input  logic [15:0]               t_rfc_i,          // mission-mode REF recovery (the 1x density CSR)
    // ANDESITE FGR DELTA: DDR4 fine-granularity refresh CSRs. t_rfc_i stays
    // the 1x density value; refresh_ctrl selects tRFC(fgr) and returns it on
    // refresh_trfc_o, which drives the arbiter's recovery input.
    input  logic [1:0]                fgr_factor_i,     // 0=1x, 1=2x, 2=4x; illegal clamps to 1x
    input  logic [15:0]               t_rfc_2x_i,       // tRFC at 2x density
    input  logic [15:0]               t_rfc_4x_i,       // tRFC at 4x density
    input  logic [3:0]                refresh_burst_i,
    input  logic [3:0]                ref_postpone_i,   // REF_CTRL.postpone_limit
    input  logic [3:0]                ref_pullin_i,     // REF_CTRL.pullin_limit
    input  logic [1:0]                ref_mode_i,       // REF_CTRL.mode (2=REFpb)
    input  logic [15:0]               ref_trefi_pb_i,   // REF_TIMING_PB.trefi_pb
    input  logic [7:0]                ref_trfc_pb_i,    // REF_TIMING_PB.trfc_pb
    // init timing (P1 init_sequencer CSRs; the 8-bit runtime CSRs zero-extend)
    input  logic [15:0]               t_init_wait_i,    // tINIT1: RESET# low time
    input  logic [15:0]               t_dll_wait_i,     // tDLLK
    input  logic [7:0]                t_mrd_wait_i,     // tMRD (MRS->MRS gap)
    input  logic [7:0]                t_rp_wait_i,      // tINIT3 (RESET# release->CKE)
    input  logic [15:0]               t_cke_wait_i,     // tINIT4 (CKE->first MRS)
    input  logic [15:0]               t_mod_wait_i,     // tMOD (last MRS->ZQCL)
    input  logic [15:0]               t_zqinit_wait_i,  // tZQinit
    output logic                      dram_reset_n_o,   // RESET# -- a PIN
    output logic                      cke_o,            // CKE -- a PIN (P1 init sequencer)
    output logic                      wrlvl_en_o,       // MR1[7]

    // ----- ZQ calibration (DDR3): andesite_zq_ctrl -----
    input  logic                      zq_enable_i,      // ZQ_CFG.zq_enable
    input  logic [31:0]               zq_interval_i,    // ZQ_INTERVAL; 0 = off
    input  logic [15:0]               t_zqcs_i,         // ZQ_CFG.t_zqcs
    output logic                      zq_busy_o,
    output logic [15:0]               zq_total_o,
    output logic [31:0]               zq_interval_cnt_o,
    output logic                      zq_overdue_o,

    // ----- Mode A/B/C CSR fields (TASK-001) ----
    input  logic                      ref_elastic_en_i,            // REF_CTRL.elastic_en
    input  logic [7:0]                ref_pullin_idle_streak_i,    // REF_CTRL.pullin_idle_streak
    input  logic [6:0]                ref_postpone_demand_streak_i,// REF_CTRL.postpone_demand_streak
    input  logic                      ref_tcr_en_i,                // REF_CTRL.tcr_en
    input  logic [1:0]                ref_trefi_derate_i,          // REF_CTRL.trefi_derate
    input  logic [1:0]                zq_placement_i,              // ZQ_CFG.placement
    input  logic [12:0]               zq_overdue_max_i,            // ZQ_CFG.overdue_max
    // ANDESITE MPC DELTA (T5): LPDDR4 calibration CSRs for andesite_zq_ctrl
    input  logic [15:0]               t_zq_i,                      // tZQ latency (LPDDR4)
    input  logic [5:0]                zq_mpc_opcode_i,             // MPC opcode image; encodings TBC
    output logic [15:0]               obs_ref_postpone_events_o,   // REF_STATS_POSTPONE
    output logic [15:0]               obs_ref_pullin_events_o,     // REF_STATS_PULLIN

    // ----- maintenance-class training commands (from andesite_training_layer)
    input  logic                      trn_cmd_req_i,
    output logic                      trn_cmd_ack_o,
    input  dram_op_e                  trn_cmd_op_i,
    input  logic [2:0]                trn_cmd_bank_i,
    input  logic [17:0]               trn_cmd_addr_i,
    input  logic [5:0]                trn_cmd_mpc_i,
    // DDR4 mode-register CSR images for the init MRS chain
    // (P1 write order MR3, MR6, MR5, MR4, MR2, MR1, MR0)
    input  logic [15:0]               mr0_i,
    input  logic [15:0]               mr1_i,
    input  logic [15:0]               mr2_i,
    input  logic [15:0]               mr3_i,
    input  logic [15:0]               mr4_i,
    input  logic [15:0]               mr5_i,
    input  logic [15:0]               mr6_i,
    input  logic                      init_restart_i,   // CTRL.init_force_restart

    // ---- init status. The P1 sequencer is self-timed (tINIT* CSRs); there
    // is no DFI init handshake at the macro -- the DFI layer generates
    // dfi_init_start from init_busy when it is born. ----
    output logic                      init_done_o,
    output logic                      init_err_o,       // unsupported memtype / watchdog
    output logic                      zq_cal_start_o,   // init-ZQCL status strobe
    output logic                      gear_down_entry_o,
    output logic                      ca_train_start_o,
    output logic                      parity_enable_o,

    // ---- P1 mode-register policy outputs: the observability contract the
    // DFI / training / ODT consumers read. The scoria CL/CWL/BL shadow
    // outputs retire here (the P1 register never had them). ----
    output logic [2:0]                rtt_nom_o,
    output logic [2:0]                rtt_wr_o,
    output logic [2:0]                rtt_park_o,
    output logic                      rd_dbi_en_o,
    output logic                      wr_dbi_en_o,
    output logic [1:0]                mpr_page_o,
    output logic [1:0]                fgr_factor_o,
    output logic [1:0]                ca_parity_lat_o,
    output logic [2:0]                lpddr4_odt_o,

    // ---- CAM per-entry vectors (external: andesite_axi4_layer) ----
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
    output logic [((NUM_BG > 1) ? $clog2(NUM_BG) : 1)-1:0] cmd_bg_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,

    output logic                      busy_o
);

    // ---- internal nets ----
    logic init_done;
    logic init_cmd_valid; dram_op_e init_cmd_op;
    logic init_cmd_valid_gated;          // req held one beat past accept -> gate
    logic [BKW-1:0] init_cmd_bank; logic [ROW_WIDTH-1:0] init_cmd_row;
    logic [17:0]      w_init_cmd_addr;   // P1 full-width init command address
    logic             w_init_accept;     // an init-class command won this cycle
    logic             w_init_cmd_ack;    // accept pulse back to the P1 sequencer
    logic             w_init_zq_start;   // P1 init-ZQCL status strobe
    logic mr_seq_we; logic [15:0] mr_seq_data;

    logic refresh_req, refresh_drain, refresh_grant;
    logic [15:0] w_refresh_trfc;   // ANDESITE FGR DELTA: tRFC(fgr) to the arbiter

    // advisory lookahead twins: what the pick pipeline decides on. The LIVE
    // w_bank_*_ready above stay wired to the arbiter too -- they are what its
    // final stage enforces against.
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

    logic evt_act, evt_rd, evt_wr, evt_pre, evt_ap;
    logic [RKW-1:0] evt_rank; logic [BKW-1:0] evt_bank; logic [ROW_WIDTH-1:0] evt_row;
    // Declared ahead of the assignments below that consume them (the repo's
    // declared-before-use gate rejects forward references; verilator and
    // cocotb tolerate them, which is how they rode along from scoria).
    logic [((NUM_BG > 1) ? $clog2(NUM_BG) : 1)-1:0] w_pick_group;
    logic w_trn_cmd_grant;

    // arbiter -> cmd FIFO
    logic          a_cmd_valid, a_cmd_ready;
    dram_op_e      a_cmd_op;
    logic [RKW-1:0] a_cmd_rank; logic [BKW-1:0] a_cmd_bank;
    logic [((NUM_BG > 1) ? $clog2(NUM_BG) : 1)-1:0] a_cmd_bg;
    logic [ROW_WIDTH-1:0] a_cmd_row; logic [COL_WIDTH-1:0] a_cmd_col; logic a_cmd_ap;
    // The issued command's bank group: the arbiter's registered-pick group
    // (bank[BKW-1 -: BGW], the JEDEC DDR4 mapping), aligned with a_cmd_*.
    assign a_cmd_bg = w_pick_group;

    assign init_done_o    = init_done;
    assign zq_cal_start_o = w_init_zq_start;
    assign trn_cmd_ack_o  = w_trn_cmd_grant;

    // P1 init accept/ack. MRS/ZQCL are the only ops init (or anything on the
    // demand path) issues on this stream, so the arbiter accept pulse
    // qualified by op class IS the honest ack. Coupling note: a future
    // demand-path MRS/ZQCL source would spuriously ack init -- the honest fix
    // then is an arbiter source qualifier, not a wider guess here.
    assign w_init_accept = a_cmd_valid && a_cmd_ready
                        && ((a_cmd_op == OP_MRS) || (a_cmd_op == OP_ZQCL));
    assign w_init_cmd_ack = w_init_accept;
    // The P1 FSM holds cmd_req until it clocks the ack; meanwhile the arbiter
    // RE-PICKS the presented request into its registered pick every cycle, so
    // a held request would push every command twice (the macro-integration
    // suite caught MRS twins one cycle apart). The pick register makes the
    // duplicate visible one cycle EARLY (the accept cycle itself re-arms it),
    // so the gate must be combinational on THIS cycle's accept, not on a
    // delayed copy: a_cmd_valid is the arbiter's registered pick, so
    // w_init_accept is loop-free. The in-flight accept is unaffected -- it
    // rides the register, not the request. Legal init spacing (tMRD/tMOD >= 3
    // cycles) tolerates the one-cycle request drop.
    assign init_cmd_valid_gated = init_cmd_valid && !w_init_accept;
    // The P1 address is 18-bit; the carried stream nets are ROW_WIDTH. MRS
    // (16'h0010+idx) and ZQCL (18'h000400) payloads fit the low 15 bits.
    assign init_cmd_row   = w_init_cmd_addr[ROW_WIDTH-1:0];

    // ======================================================================
    // andesite_init_sequencer — P1 DDR4 init (JEDEC 79-4 sequence), gates
    // traffic until done. Rewired to the P1 pin names: the carried scoria
    // DDR3 connections were the 49 PINNOTFOUND the integration pass owns.
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
        .tinit3_csr         (16'(t_rp_wait_i)),  // RESET# release -> CKE (DDR3 named it tRP)
        .tinit4_csr         (t_cke_wait_i),      // CKE -> first MRS (P1 splits this out)
        .tdllk_csr          (t_dll_wait_i),
        .tzqinit_csr        (t_zqinit_wait_i),
        .tmrd_csr           (16'(t_mrd_wait_i)), // MRS -> MRS gap
        .tmod_csr           (t_mod_wait_i),      // last MRS -> ZQCL
        .csr_mr0_image      (mr0_i),
        .csr_mr1_image      (mr1_i),
        .csr_mr2_image      (mr2_i),
        .csr_mr3_image      (mr3_i),
        .csr_mr4_image      (mr4_i),
        .csr_mr5_image      (mr5_i),
        .csr_mr6_image      (mr6_i),
        .cmd_ack            (w_init_cmd_ack),
        // TASK-006 recovery FSM pins: parked -- grounded so no spurious alert
        // can fire; the alert source + scheduler retract channel are the
        // recorded TASK-006 wiring follow-on.
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

    // ======================================================================
    // andesite_mode_register — P1 shadow. The init FSM's mr_load/mr_image_out
    // write the MR the init just issued (the MR index rides cmd_bank, per the
    // P1 FSM's MR_ORDER). The policy outputs (RTT/DBI/MPR/parity-latency/
    // LPDDR4-ODT/wrlvl) are the observability contract the DFI, training and
    // ODT consumers read. The carried CL/CWL/BL shadow outputs retire with
    // the scoria DDR3 register -- the P1 register never had them (latency
    // values live in the MR images themselves).
    // ======================================================================
    andesite_mode_register #(
        .DATA_WIDTH(16),
        .RANKS     (NUM_RANKS)
    ) u_mode_reg (
        .clk            (aclk),
        .rst_n          (aresetn),
        .memtype_i      (memtype_i),
        .rank_i         ('0),                       // single-rank design point
        .wr_en_i        (mr_seq_we),
        .wr_addr_i      ({3'b000, init_cmd_bank}),  // MR index rides cmd_bank
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

    // ======================================================================
    // andesite_refresh_ctrl — tREFI + 8-deep postpone; enabled after init.
    // ======================================================================
    // REFpb is LPDDR2-only (DDR2 has no per-bank refresh command); an
    // unsupported mode select degrades to REFab rather than emitting an
    // illegal command.
    logic            w_refpb_en;
    logic            w_refresh_kind;
    logic [BKW-1:0]  w_refresh_bank;
    assign w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR3);

    andesite_refresh_ctrl #(
        .NUM_BANKS(NUM_BANKS)
    ) u_refresh (
        .mc_clk          (aclk),
        .mc_rst_n        (aresetn),
        .t_refi_i        (t_refi_i),
        .trefi_pb_i      (ref_trefi_pb_i),
        .refresh_burst_i (refresh_burst_i),
        .refpb_mode_i    (w_refpb_en),
        .refi_reload_i (refi_reload_i),
        .enable_i        (init_done),
        .postpone_limit_i(ref_postpone_i),
        .pullin_limit_i  (ref_pullin_i),
        .demand_i        (|rd_sch_valid_i || |wr_sch_valid_i),
        // Mode A/B/C CSR fields (TASK-001)
        .elastic_en_i            (ref_elastic_en_i),
        .pullin_idle_streak_i    (ref_pullin_idle_streak_i),
        .postpone_demand_streak_i(ref_postpone_demand_streak_i),
        .tcr_en_i                (ref_tcr_en_i),
        .trefi_derate_i          (ref_trefi_derate_i),
        // ANDESITE FGR DELTA: factor + per-density tRFC CSRs; the selected
        // recovery window feeds the arbiter's t_rfc_i below.
        .fgr_factor_i            (fgr_factor_i),
        .t_rfc_1x_i              (t_rfc_i),
        .t_rfc_2x_i              (t_rfc_2x_i),
        .t_rfc_4x_i              (t_rfc_4x_i),
        .refresh_trfc_o          (w_refresh_trfc),
        .refresh_req_o   (refresh_req),
        .refresh_grant_i (refresh_grant),
        // refresh_grant fires at the arbiter's FIFO-PUSH, so the granted op is
        // the ARBITER-side a_cmd_op — cmd_op_o is the FIFO HEAD (an older
        // command) and sampling it stalls the rotor mirror erratically.
        .grant_was_pb_i        (a_cmd_op == OP_REFPB),
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

    // ======================================================================
    // andesite_zq_ctrl — periodic ZQCS. DDR3 only; parked on LPDDR3.
    // ======================================================================
    // Maintenance traffic on the same request/grant contract as refresh, and
    // BELOW it in the arbiter's cone. Gated on init_done for the same reason
    // refresh is: a ZQCS before the init ZQCL would be issued into a device
    // that has not finished initialising.
    //
    // LPDDR3 has ZQ calibration too (JESD209-3C MRW-based ZQCal), but it is
    // an MR write, not a bus command -- a different mechanism entirely, so
    // this block is held off rather than pointed at it. Deliberately not
    // implemented; the LPDDR3 path has no ZQ maintenance yet.
    logic w_zq_req, w_zq_grant;
    logic w_zq_run;
    // ANDESITE DELTA: scoria gated ZQ on MEMTYPE_DDR3 (its only exercised
    // family); andesite exercises DDR4 and LPDDR4, both of which carry ZQ
    // calibration (DDR4 ZQCS/ZQCL, LPDDR4 MPC).
    assign w_zq_run = zq_enable_i && init_done
                    && ((memtype_i == MEMTYPE_DDR4) || (memtype_i == MEMTYPE_LPDDR4));

    andesite_zq_ctrl u_zq (
        .mc_clk             (aclk),
        .mc_rst_n           (aresetn),
        .enable_i           (w_zq_run),
        .t_zqcs_interval_i  (zq_interval_i),
        .t_zqcs_i           (t_zqcs_i),
        .demand_i           (|rd_sch_valid_i || |wr_sch_valid_i),
        // Mode C CSR fields (TASK-001)
        .placement_i        (zq_placement_i),
        .overdue_max_i      (zq_overdue_max_i),
        .zq_req_o           (w_zq_req),
        .zq_grant_i         (w_zq_grant),
        // ANDESITE MPC DELTA: LPDDR4 calibration path (T5)
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

    // ======================================================================
    // andesite_bank_timers — per-bank safe timers (open-page).
    // ======================================================================
    // BANK_LA = the pick pipeline's select-to-fire depth: the advisory image
    // is sampled into r_bank_*_ready and the command fires four register
    // stages later (r_bank_*_ready -> STAGE-1a -> pre-pick -> output), all of
    // which advance together on w_out_ready. Back-pressure only ever DELAYS
    // the fire, which is the safe direction -- more decrement has happened, so
    // a lookahead that assumed 4 is still conservative at 5+. Only firing
    // EARLIER than the assumed depth would be wrong, and nothing can.
    // Over-estimating costs a dropped pick at the final gate, never a
    // violation; the reject rate lands in stall_banktimer_o.
    andesite_bank_timers #(
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

    // ANDESITE L/S DELTA: group wires + timer readiness loop. group(bank)
    // matches the arbiter's formula exactly; the design point is single-rank
    // (RK0), so the timers' per-candidate rank select is constant zero.
    localparam int BGW_EFF_M = (NUM_BG > 1) ? $clog2(NUM_BG) : 1;
    logic [BGW_EFF_M-1:0] w_evt_bg;
    logic                 w_tccd_l_ok, w_trrd_l_ok, w_tccd_s_ok, w_trrd_s_ok;
    assign w_evt_bg = (NUM_BG > 1) ? evt_bank[BKW-1 -: BGW_EFF_M] : '0;

    // ======================================================================
    // andesite_global_timers — tFAW/tRRD (per-rank), tWTR/tRTW/tCCD (global),
    // plus the L/S pair windows (per-(rank,group) ACT, per-group column).
    // ======================================================================
    andesite_global_timers #(
        .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS)
    ) u_global_timers (
        .mc_clk          (aclk),
        .mc_rst_n        (aresetn),
        .t_faw_i         (t_faw_i),
        .t_rrd_i         (t_rrd_i),
        .t_wtr_global_i  (t_wtr_i),
        .t_rtw_i         (t_rtw_i),
        .t_ccd_i         (t_ccd_i),
        // ANDESITE L/S DELTA
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
        .cand_bg_i       (w_pick_group),
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
    // andesite_cmd_arbiter — the pick core.
    // ======================================================================
    // andesite_page_policy — runtime Axis-2 engine + telemetry. Watches the
    // arbiter's issued stream (valid && ready, identical tap to the
    // cmd-history checker) and the registered bank-state buses.
    logic                  w_pp_ap_en;
    logic [NUM_BANKS-1:0]  w_pp_ap_close;
    logic                  w_pp_to_req;
    logic [BKW-1:0]        w_pp_to_bank;

    andesite_page_policy #(
        .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH)
    ) u_page_policy (
        .aclk              (aclk),
        .aresetn           (aresetn),
        .policy_mode_i     (page_mode_i),
        .tr_init_i         (page_tr_init_i),
        // Taps the ARBITER's accept (pre-FIFO), not the FIFO output: the
        // predictors correlate each command with the LIVE bank image, and the
        // cmd FIFO now releases CMD_DELAY cycles later -- a command seen that
        // late no longer matches the row it acted on (adapt_access learned
        // nothing: 12 vs 11 PREs, 2026-09-09).
        .cmd_valid_i       (a_cmd_valid && a_cmd_ready),
        .cmd_op_i          (a_cmd_op),
        .cmd_bank_i        (a_cmd_bank),
        .cmd_row_i         (a_cmd_row),
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

    andesite_cmd_arbiter #(
        .NUM_RANKS   (NUM_RANKS),
        .NUM_BANKS   (NUM_BANKS),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH),
        .AXI_ID_WIDTH(IW),
        .NUM_ENTRIES (NUM_ENTRIES),
        .AGE_WIDTH   (AGE_WIDTH),
        .NUM_BG      (NUM_BG)
    ) u_arbiter (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (page_policy_i),
        .ap_mode_en_i       (w_pp_ap_en),
        .ap_close_i         (w_pp_ap_close),
        .timeout_pre_req_i  (w_pp_to_req),
        .timeout_pre_bank_i (w_pp_to_bank),
        .init_done_i        (init_done),
        .init_cmd_valid_i   (init_cmd_valid_gated),
        .init_cmd_op_i      (init_cmd_op),
        .init_cmd_bank_i    (init_cmd_bank),
        .init_cmd_row_i     (init_cmd_row),
        .refresh_req_i      (refresh_req),
        .refresh_drain_i    (refresh_drain),
        .refresh_grant_o    (refresh_grant),
        .refresh_kind_i     (w_refresh_kind),
        .refresh_bank_i     (w_refresh_bank),
        .t_rfc_i            (w_refresh_trfc),
        .t_rfc_pb_i         (ref_trfc_pb_i),
        .zq_req_i           (w_zq_req),
        .zq_grant_o         (w_zq_grant),
        .t_zqcs_i           (t_zqcs_i),
        .trn_cmd_req_i      (trn_cmd_req_i),
        .trn_cmd_op_i       (trn_cmd_op_i),
        .trn_cmd_bank_i     (trn_cmd_bank_i),
        .trn_cmd_addr_i     (trn_cmd_addr_i),
        .trn_cmd_grant_o    (w_trn_cmd_grant),
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
        .pick_group_o       (w_pick_group),
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
        .stall_bp_o        (stall_bp_o),
        .stall_refresh_o        (stall_refresh_o),
        .stall_turnaround_o        (stall_turnaround_o),
        .stall_tccd_o        (stall_tccd_o),
        .stall_actlimit_o        (stall_actlimit_o),
        .stall_banktimer_o        (stall_banktimer_o),
        .stall_noreq_o        (stall_noreq_o),
        .stall_zq_o           (stall_zq_o)
    );

    // ======================================================================
    // Output command FIFO (scheduler -> DFI). Packs {ap,col,row,bg,bank,rank,op}.
    // ======================================================================
    localparam int CMD_W = $bits(dram_op_e) + RKW + BKW + BGW_EFF_M + ROW_WIDTH + COL_WIDTH + 1;
    logic [CMD_W-1:0] w_cmd_wr_data, w_cmd_rd_data;
    assign w_cmd_wr_data = {a_cmd_ap, a_cmd_col, a_cmd_row, a_cmd_bg, a_cmd_bank, a_cmd_rank,
                            a_cmd_op};

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
    // A token enters a CMD_DELAY-stage shift register with every push; the FIFO
    // head may leave only once a token has matured. Matured-but-unpopped tokens
    // are counted, so under DFI back-pressure nothing is lost -- the stream then
    // degrades to back-to-back release, which the DFI write-staged gate is
    // designed never to cause (its held counters prove it).
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

    assign {cmd_ap_o, cmd_col_o, cmd_row_o, cmd_bg_o, cmd_bank_o, cmd_rank_o, w_rd_op} = w_cmd_rd_data;
    assign cmd_op_o    = w_rd_op;

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
            // P2 L/S growth: the issued command's bank group, same formula
            // as the arbiter's group select.
            .cmd_bg_i   (w_evt_bg)
        );
    end endgenerate

endmodule : andesite_scheduler_layer
