// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_cmd_arbiter
// Purpose: Common command arbiter for the mem-ctrl family scheduler layer.
//          Parameterized superset of the pumice/scoria/andesite schedulers.
//          Each cycle it picks ONE abstract DRAM command and pushes it into the
//          scheduler->DFI command interface. PHY/nphases-agnostic; single-issue.
//          JEDEC timing is enforced via the per-bank (mc_bank_timers) and global
//          (mc_global_timers) readiness inputs.
//
//          - NUM_BG > 1 enables DDR4 bank-group long/short (L/S) admission.
//          - HAS_ZQ == 1 enables the DDR3/DDR4 ZQ calibration branch and the
//            tZQCS fire-stage block (scoria BUG-002 / andesite).
//          - The per-rock training/maintenance requesters collapse to a single
//            generic maintenance slot {req,grant,op,bank,row,extra} plus a
//            maint_busy_i demand-block. ZQCS keeps its own external contract.
//
//          The fire-stage policy is the union of the three rocks:
//            - pumice w_out_hold is kept for ACTs blocked only by tFAW/tRRD.
//            - !w_zq_busy is added to every demand-class w_out_safe.
//            - tfaw_ok_i/trrd_ok_i are re-checked at the fire stage.
//            - L/S group windows are re-checked when NUM_BG > 1.
//
// Documentation: projects/components/mem-ctrl-ip/common-ip/docs/mc_scheduler_knobs.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_cmd_arbiter
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int NUM_RANKS   = 1,
    parameter int NUM_BANKS   = 8,
    parameter int NUM_BG      = 1,   // bank groups; 1 = no L/S pair windows
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter bit HAS_ZQ      = 1'b0, // include ZQ calibration branch + tZQCS block
    parameter int MAINT_EXTRA_WIDTH = 1, // width of maint_extra_i; pumice maps trn_cmd_mrr, andesite maps mpc[5:0]
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int IW   = AXI_ID_WIDTH,
    parameter int BGW_EFF = (NUM_BG > 1) ? $clog2(NUM_BG) : 1
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  page_policy_e              page_policy_i,

    // ---- SCHED_POLICY order mode (TASK-001 Axis 1) ----
    input  logic [1:0]                sched_order_mode_i,
    input  logic [1:0]                sched_row_sel_i,
    input  logic [1:0]                sched_col_sel_i,
    input  logic [1:0]                sched_access_pref_i,
    input  logic [7:0]                sched_wr_high_wm_i,
    input  logic [7:0]                sched_wr_batch_max_i,
    input  logic [7:0]                sched_wr_low_wm_i,
    input  logic [1:0]                sched_prio_sub_i,
    input  logic                      sched_qos_en_i,
    input  logic [NUM_ENTRIES*4-1:0]  rd_sch_qos_i,
    input  logic [NUM_ENTRIES*4-1:0]  wr_sch_qos_i,
    input  logic [NUM_ENTRIES-1:0]    rd_sch_age_exceed_i,
    input  logic [NUM_ENTRIES-1:0]    wr_sch_age_exceed_i,
    input  logic [AGE_WIDTH-1:0]      rd_sch_head_rel_i,
    input  logic [AGE_WIDTH-1:0]      wr_sch_head_rel_i,

    // ---- runtime page-policy engine ----
    input  logic                      ap_mode_en_i,
    input  logic [NUM_BANKS-1:0]      ap_close_i,
    input  logic                      timeout_pre_req_i,
    input  logic [BKW-1:0]            timeout_pre_bank_i,

    // ---- init passthrough (from rock-specific init_sequencer) ----
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    // ---- refresh (from rock-specific refresh_ctrl) ----
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    input  logic                      refresh_kind_i,   // 0=REFab, 1=REFpb
    input  logic [BKW-1:0]            refresh_bank_i,   // rotor mirror
    output logic                      refresh_grant_o,
    input  logic [15:0]               t_rfc_i,
    input  logic [7:0]                t_rfc_pb_i,       // REFpb recovery; 0 = t_rfc_i

    // ---- ZQ calibration (rock-side source; present when HAS_ZQ=1) ----
    input  logic                      zq_req_i,
    output logic                      zq_grant_o,
    input  logic [15:0]               t_zqcs_i,

    // ---- generic maintenance-class training commands (rock-side source) ----
    input  logic                      maint_req_i,
    output logic                      maint_grant_o,
    input  dram_op_e                  maint_op_i,
    input  logic [BKW-1:0]            maint_bank_i,
    input  logic [ROW_WIDTH-1:0]      maint_row_i,
    input  logic [COL_WIDTH-1:0]      maint_col_i,
    input  logic [MAINT_EXTRA_WIDTH-1:0] maint_extra_i,
    input  logic                      maint_busy_i,     // demand-class block (pumice cal_busy_i semantics)

    // ---- per-bank readiness (from mc_bank_timers) ----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_i,

    // ---- global readiness (from mc_global_timers) ----
    input  logic [NUM_RANKS-1:0]      tfaw_ok_i,
    input  logic [NUM_RANKS-1:0]      trrd_ok_i,
    input  logic                      twtr_ok_i,
    input  logic                      trtw_ok_i,
    input  logic                      tccd_ok_i,
    // L/S pair readiness when NUM_BG > 1 (tied off / constant-1 otherwise)
    input  logic                      tccd_l_ok_i,
    input  logic                      trrd_l_ok_i,
    output logic [BGW_EFF-1:0]        pick_group_o,
    // tCCD in MC cycles, for the FORWARD column-spacing gate
    input  logic [7:0]                t_ccd_i,

    // ---- wr CAM per-entry vectors (registered) + commit ----
    input  logic [NUM_ENTRIES-1:0]              wr_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_i,
    input  logic                                wr_commit_ready_i,
    output logic                                wr_commit_valid_o,
    output logic [PTRW-1:0]                     wr_commit_slot_o,

    // ---- rd CAM per-entry vectors (registered) + issue ----
    input  logic [NUM_ENTRIES-1:0]              rd_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_i,
    input  logic                                rd_issue_ready_i,
    output logic                                rd_issue_valid_o,
    output logic [PTRW-1:0]                     rd_issue_slot_o,

    // ---- event strobes to bank + global timers ----
    output logic                      evt_act_o,
    output logic                      evt_rd_o,
    output logic                      evt_wr_o,
    output logic                      evt_pre_o,
    output logic                      evt_ap_o,
    output logic [RKW-1:0]            evt_rank_o,
    output logic [BKW-1:0]            evt_bank_o,
    output logic [ROW_WIDTH-1:0]      evt_row_o,

    // ---- command push (scheduler -> DFI command FIFO) ----
    output logic                      cmd_valid_o,
    input  logic                      cmd_ready_i,
    output dram_op_e                  cmd_op_o,
    output logic [RKW-1:0]            cmd_rank_o,
    output logic [BKW-1:0]            cmd_bank_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o,
    output logic [MAINT_EXTRA_WIDTH-1:0] cmd_extra_o,

    // ---- stall-cause attribution (TASK-006) ----
    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stall_zq_o
);

    localparam int RK0 = 0;   // v1 single-rank pick

    // Column auto-precharge bit from the page policy.
    logic w_ap;
    assign w_ap = (page_policy_i == PAGE_POLICY_CLOSE);

    function automatic logic f_ap (input logic [BKW-1:0] b);
        return ap_mode_en_i ? ap_close_i[b] : w_ap;
    endfunction

    // Per-bank ACT/PRE re-issue GUARD.
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;

    // ---- output pipeline: the registered arbiter DECISION ------------------
    logic                 r_pick_valid;
    dram_op_e             r_op;
    logic [BKW-1:0]       r_bank;
    logic [ROW_WIDTH-1:0] r_row;
    logic [COL_WIDTH-1:0] r_col_out;
    logic                 r_ap_out;
    logic                 r_do_act, r_do_rd, r_do_wr, r_do_pre, r_grant;
    logic                 r_zq_grant;
    logic                 r_maint_grant;
    logic                 r_wr_commit, r_rd_issue;
    logic [PTRW-1:0]      r_commit_slot, r_issue_slot;
    logic [MAINT_EXTRA_WIDTH-1:0] r_cmd_extra;

    // Pre-pick registers
    logic            rd_col_f, wr_col_f, rd_act_f, wr_act_f, rd_pre_f, wr_pre_f;
    logic [PTRW-1:0] rd_col_s, wr_col_s, rd_act_s, wr_act_s, rd_pre_s, wr_pre_s;
    logic            rd_col_ap, wr_col_ap;

    // Pre-MUXED pick operands
    logic [BKW-1:0]       rd_col_bank, wr_col_bank, rd_act_bank, wr_act_bank;
    logic [BKW-1:0]       rd_pre_bank, wr_pre_bank;
    logic [COL_WIDTH-1:0] rd_col_col,  wr_col_col;
    logic [ROW_WIDTH-1:0] rd_act_row,  wr_act_row;

    // arg_sel COMBINATIONAL result (STAGE 1b)
    logic            w_sel_rd_col_f, w_sel_wr_col_f, w_sel_rd_act_f;
    logic            w_sel_wr_act_f, w_sel_rd_pre_f, w_sel_wr_pre_f;
    logic [PTRW-1:0] w_sel_rd_col_s, w_sel_wr_col_s, w_sel_rd_act_s;
    logic [PTRW-1:0] w_sel_wr_act_s, w_sel_rd_pre_s, w_sel_wr_pre_s;

    // Output-stage accept
    logic w_out_ready, w_fire_out;

    // ---- FINAL-STAGE TIMING ENFORCEMENT -------------------------------------
    // Union of pumice BUG-021 hold, scoria BUG-001/BUG-002 re-checks, and
    // andesite L/S re-checks. Real timing is enforced HERE.
    logic [15:0] r_zqcs_cnt;
    logic        w_zq_busy;
    assign w_zq_busy = (r_zqcs_cnt != 16'd0);

    // L/S admission declarations (active when NUM_BG > 1)
    logic [BGW_EFF-1:0] w_pick_group, r_last_col_bg, r_last_act_bg;
    logic               w_tccd_ls_ok, w_trrd_ls_ok;

    logic w_out_safe, w_out_reject, w_out_hold;
    always_comb begin
        w_out_safe = 1'b1;
        if      (r_do_act)            w_out_safe = !maint_busy_i
                                                  && bank_act_ready_i [RK0][r_bank]
                                                  && tfaw_ok_i[RK0] && trrd_ok_i[RK0]
                                                  && w_trrd_ls_ok
                                                  && !w_zq_busy;
        else if (r_do_rd || r_do_wr)  w_out_safe = !maint_busy_i && bank_rdwr_ready_i[RK0][r_bank]
                                                  && w_tccd_ls_ok
                                                  && !w_zq_busy;
        else if (r_do_pre)            w_out_safe = !maint_busy_i && bank_pre_ready_i [RK0][r_bank]
                                                  && !w_zq_busy;
    end
    // HOLD an ACT whose only obstacle is the rank-global windows:
    assign w_out_hold   = r_pick_valid && !maint_busy_i && r_do_act
                          && bank_act_ready_i[RK0][r_bank]
                          && !(tfaw_ok_i[RK0] && trrd_ok_i[RK0])
                          && !w_zq_busy;
    assign w_out_reject = r_pick_valid && !w_out_safe && !w_out_hold;
    assign w_out_ready  = !r_pick_valid || (cmd_ready_i && !w_out_hold) || w_out_reject;
    assign w_fire_out   = r_pick_valid && cmd_ready_i && w_out_safe;

    // Pre-pick forward-guard
    logic w_prepick_col, w_prepick_preact;
    assign w_prepick_col    = w_sel_rd_col_f || w_sel_wr_col_f
                            || rd_col_f || wr_col_f;
    assign w_prepick_preact = w_sel_rd_act_f || w_sel_wr_act_f
                            || w_sel_rd_pre_f || w_sel_wr_pre_f
                            || rd_act_f || wr_act_f || rd_pre_f || wr_pre_f;

    // Forward-masks covering the extra output-register cycle
    logic w_inflight_col, w_inflight_preact;
    assign w_inflight_col    = r_pick_valid && (r_do_rd || r_do_wr);
    assign w_inflight_preact = r_pick_valid && (r_do_act || r_do_pre);

    // =====================================================================
    // IN-FLIGHT SHADOW -- what has this arbiter already committed that the
    // bank timers have not been told about yet?
    // =====================================================================
    logic [NUM_BANKS-1:0] w_if_preact_sel, w_if_preact_pre, w_if_preact_out;
    logic [NUM_BANKS-1:0] w_if_col_sel,    w_if_col_pre,    w_if_col_out;
    always_comb begin
        w_if_preact_sel = '0;
        if (w_sel_rd_act_f)
            w_if_preact_sel |= (NUM_BANKS'(1) << f_bank(rd_sch_bank_i, w_sel_rd_act_s));
        if (w_sel_wr_act_f)
            w_if_preact_sel |= (NUM_BANKS'(1) << f_bank(wr_sch_bank_i, w_sel_wr_act_s));
        if (w_sel_rd_pre_f)
            w_if_preact_sel |= (NUM_BANKS'(1) << f_bank(rd_sch_bank_i, w_sel_rd_pre_s));
        if (w_sel_wr_pre_f)
            w_if_preact_sel |= (NUM_BANKS'(1) << f_bank(wr_sch_bank_i, w_sel_wr_pre_s));

        w_if_preact_pre = '0;
        if (rd_act_f) w_if_preact_pre |= (NUM_BANKS'(1) << rd_act_bank);
        if (wr_act_f) w_if_preact_pre |= (NUM_BANKS'(1) << wr_act_bank);
        if (rd_pre_f) w_if_preact_pre |= (NUM_BANKS'(1) << rd_pre_bank);
        if (wr_pre_f) w_if_preact_pre |= (NUM_BANKS'(1) << wr_pre_bank);

        w_if_preact_out = w_inflight_preact ? (NUM_BANKS'(1) << r_bank) : '0;

        w_if_col_sel = '0;
        if (w_sel_rd_col_f)
            w_if_col_sel |= (NUM_BANKS'(1) << f_bank(rd_sch_bank_i, w_sel_rd_col_s));
        if (w_sel_wr_col_f)
            w_if_col_sel |= (NUM_BANKS'(1) << f_bank(wr_sch_bank_i, w_sel_wr_col_s));

        w_if_col_pre = '0;
        if (rd_col_f) w_if_col_pre |= (NUM_BANKS'(1) << rd_col_bank);
        if (wr_col_f) w_if_col_pre |= (NUM_BANKS'(1) << wr_col_bank);

        w_if_col_out = w_inflight_col ? (NUM_BANKS'(1) << r_bank) : '0;
    end

    logic [NUM_BANKS-1:0] w_prepick_guard;
    assign w_prepick_guard = w_if_preact_sel | w_if_preact_pre;

    logic [NUM_BANKS-1:0] w_col_inflight_guard;
    assign w_col_inflight_guard = w_if_col_sel | w_if_col_pre;

    // Per-entry double-issue mask
    logic [NUM_ENTRIES-1:0] w_rd_col_inflight_ent, w_wr_col_inflight_ent;
    always_comb begin
        w_rd_col_inflight_ent = '0;
        w_wr_col_inflight_ent = '0;
        if (w_sel_rd_col_f) w_rd_col_inflight_ent[w_sel_rd_col_s] = 1'b1;
        if (w_sel_wr_col_f) w_wr_col_inflight_ent[w_sel_wr_col_s] = 1'b1;
        if (rd_col_f)       w_rd_col_inflight_ent[rd_col_s]       = 1'b1;
        if (wr_col_f)       w_wr_col_inflight_ent[wr_col_s]       = 1'b1;
        if (r_pick_valid && r_do_rd) w_rd_col_inflight_ent[r_issue_slot]  = 1'b1;
        if (r_pick_valid && r_do_wr) w_wr_col_inflight_ent[r_commit_slot] = 1'b1;
    end

    logic w_act_classify_gate;
    assign w_act_classify_gate = (sched_access_pref_i == 2'd2)
                               ? (tfaw_ok_i[RK0] && trrd_ok_i[RK0]) : 1'b1;

    logic [NUM_BANKS-1:0] w_col_inflight_bank;
    assign w_col_inflight_bank = w_col_inflight_guard
                               | (w_inflight_col ? (NUM_BANKS'(1) << r_bank) : '0);

    // ---- FORWARD tCCD (column spacing at classify time) --------------------
    logic [7:0] r_tccd_fwd;
    logic       w_col_sel_now, w_tccd_fwd_ok;
    assign w_col_sel_now = w_sel_rd_col_f || w_sel_wr_col_f;
    assign w_tccd_fwd_ok = (r_tccd_fwd <= 8'd1) && !(w_col_sel_now && (t_ccd_i > 8'd1));
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_tccd_fwd <= '0;
        else if (w_col_sel_now)          r_tccd_fwd <= (t_ccd_i > 8'd1) ? (t_ccd_i - 8'd1) : 8'd0;
        else if (r_tccd_fwd != 8'd0)     r_tccd_fwd <= r_tccd_fwd - 8'd1;
    )
    logic [NUM_BANKS-1:0] r_ap_closing, w_ap_fire_bank;
    assign w_ap_fire_bank = (w_fire_out && (r_do_rd || r_do_wr) && r_ap_out)
                          ? (NUM_BANKS'(1) << r_bank) : '0;

    logic [NUM_BANKS-1:0] w_guarded;
    assign w_guarded = r_guard0 | r_guard1 | w_prepick_guard | w_col_inflight_guard
                     | w_if_preact_out | w_if_col_out;

    // in-flight ACT/PRE bank guard for the COLUMN masks
    logic [NUM_BANKS-1:0] w_preact_bank_guard;
    assign w_preact_bank_guard = w_prepick_guard | w_if_preact_out;

    // ---- direction-turnaround guard ----------------------------------------
    logic r_wrfire0, r_wrfire1, r_rdfire0, r_rdfire1;
    logic w_rd_turn_block, w_wr_turn_block;
    assign w_rd_turn_block = r_wrfire0 || r_wrfire1;
    assign w_wr_turn_block = r_rdfire0 || r_rdfire1;

    // ---- auto-precharge column guard ---------------------------------------
    logic [NUM_BANKS-1:0] r_apguard0, r_apguard1;
    logic [NUM_BANKS-1:0] w_ap_col_guard;
    assign w_ap_col_guard = r_apguard0 | r_apguard1;

    // PRE-only column guard
    logic [NUM_BANKS-1:0] r_preguard0, r_preguard1, r_preguard2;
    logic [NUM_BANKS-1:0] w_pre_col_guard;
    assign w_pre_col_guard = r_preguard0 | r_preguard1 | r_preguard2;

    // ---- REF recovery (tRFC) -----------------------------------------------
    logic [15:0] r_rfc_cnt;
    logic        w_rfc_busy;
    assign w_rfc_busy = (r_rfc_cnt != 16'd0);

    // ---- pipeline: register the bank-timer fan-in at the arbiter input ------
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bank_act_ready, r_bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bank_pre_ready,  r_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] r_bank_open_row;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bank_act_ready <= '0; r_bank_rdwr_ready <= '0;
            r_bank_pre_ready <= '0; r_bank_row_active <= '0; r_bank_open_row <= '0;
        end else begin
            r_bank_act_ready  <= bank_act_ready_la_i;
            r_bank_rdwr_ready <= bank_rdwr_ready_la_i;
            r_bank_pre_ready  <= bank_pre_ready_la_i;
            r_bank_row_active <= bank_row_active_i;
            r_bank_open_row   <= bank_open_row_i;
        end
    )

    // ---- per-entry field extractors --------------------------------------
    function automatic logic [BKW-1:0]       f_bank(input logic [NUM_ENTRIES*BKW-1:0] v, input logic [PTRW-1:0] e);
        return v[e*BKW +: BKW];
    endfunction
    function automatic logic [ROW_WIDTH-1:0] f_row (input logic [NUM_ENTRIES*ROW_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*ROW_WIDTH +: ROW_WIDTH];
    endfunction
    function automatic logic [COL_WIDTH-1:0] f_col (input logic [NUM_ENTRIES*COL_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*COL_WIDTH +: COL_WIDTH];
    endfunction

    // ---- unified rd/wr prospect pool (2N entries) ----------------------------
    localparam int POOL = 2*NUM_ENTRIES;
    localparam int PTXW = PTRW + 1;
    logic [POOL-1:0]           pool_valid;
    logic [POOL*BKW-1:0]       pool_bank;
    logic [POOL*ROW_WIDTH-1:0] pool_row;
    logic [POOL*COL_WIDTH-1:0] pool_col;
    assign pool_valid = {wr_sch_valid_i, rd_sch_valid_i};
    assign pool_bank  = {wr_sch_bank_i,  rd_sch_bank_i};
    assign pool_row   = {wr_sch_row_i,   rd_sch_row_i};
    assign pool_col   = {wr_sch_col_i,   rd_sch_col_i};
    function automatic logic [BKW-1:0]       f_pool_bank(input logic [PTXW-1:0] e);
        return pool_bank[e*BKW +: BKW];
    endfunction
    function automatic logic [ROW_WIDTH-1:0] f_pool_row (input logic [PTXW-1:0] e);
        return pool_row[e*ROW_WIDTH +: ROW_WIDTH];
    endfunction
    function automatic logic [COL_WIDTH-1:0] f_pool_col (input logic [PTXW-1:0] e);
        return pool_col[e*COL_WIDTH +: COL_WIDTH];
    endfunction

    // ---- classify each pool entry into column / activate / precharge --------
    logic [POOL-1:0]        pool_col_m, pool_act_m, pool_pre_m;
    logic [NUM_ENTRIES-1:0] rd_col_m, rd_act_m, rd_pre_m;
    logic [NUM_ENTRIES-1:0] wr_col_m, wr_act_m, wr_pre_m;
    assign rd_col_m = pool_col_m[NUM_ENTRIES-1:0];
    assign rd_act_m = pool_act_m[NUM_ENTRIES-1:0];
    assign rd_pre_m = pool_pre_m[NUM_ENTRIES-1:0];
    assign wr_col_m = pool_col_m[POOL-1:NUM_ENTRIES];
    assign wr_act_m = pool_act_m[POOL-1:NUM_ENTRIES];
    assign wr_pre_m = pool_pre_m[POOL-1:NUM_ENTRIES];
    logic [NUM_BANKS-1:0] w_ref_col_block;
    always_comb begin
        pool_col_m = '0; pool_act_m = '0; pool_pre_m = '0;
        for (int e = 0; e < POOL; e++) begin
            automatic logic           pdir = (e >= NUM_ENTRIES);
            automatic int             pslot = pdir ? (e - NUM_ENTRIES) : e;
            automatic logic [BKW-1:0] pbank = f_pool_bank(PTXW'(e));
            automatic logic           phit = r_bank_row_active[RK0][pbank]
                                             && (f_pool_row(PTXW'(e)) == r_bank_open_row[RK0][pbank]);
            if (pool_valid[e]) begin
                pool_col_m[e] = phit && r_bank_rdwr_ready[RK0][pbank] && w_tccd_fwd_ok
                              && (pdir ? trtw_ok_i : twtr_ok_i)
                              && (pdir ? wr_commit_ready_i : rd_issue_ready_i)
                              && !(f_ap(pbank) && w_col_inflight_bank[pbank]) && !r_ap_closing[pbank]
                              && !(pdir ? w_wr_col_inflight_ent[pslot] : w_rd_col_inflight_ent[pslot])
                              && !w_ref_col_block[pbank]
                              && (pdir ? !w_wr_turn_block : !w_rd_turn_block)
                              && !w_ap_col_guard[pbank] && !w_pre_col_guard[pbank]
                              && !w_preact_bank_guard[pbank]
                              && w_tccd_ls_ok;
                pool_act_m[e] = !r_bank_row_active[RK0][pbank] && !w_guarded[pbank]
                              && r_bank_act_ready[RK0][pbank] && w_act_classify_gate
                              && !w_rfc_busy;
                pool_pre_m[e] = r_bank_row_active[RK0][pbank] && !w_guarded[pbank] && !phit
                              && r_bank_pre_ready[RK0][pbank];
            end
        end
    end

    // ---- refresh-pending column block ------------------------------------
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_ref_col_block[b] = (refresh_req_i || refresh_drain_i)
                               && (!refresh_kind_i || (BKW'(b) == refresh_bank_i));
    end

    // ---- oldest-in-mask via the age-order matrix ---------------------------
    function automatic logic [PTRW:0] arg_oldest(
        input logic [NUM_ENTRIES-1:0]              mask,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  older
    );
        logic                   found;
        logic [PTRW-1:0]        slot;
        logic [NUM_ENTRIES-1:0] is_old;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic [NUM_ENTRIES-1:0] orow = older[i*NUM_ENTRIES +: NUM_ENTRIES];
            automatic logic ge_all = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && mask[j] && !orow[j]) ge_all = 1'b0;
            is_old[i] = mask[i] && ge_all;
        end
        found = |is_old;
        slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (is_old[i]) slot = PTRW'(i);
        return {found, slot};
    endfunction

    // ---- ORDER_MODE overlay -----------------------------------------------
    localparam logic [1:0] ORDER_IN_ORDER = 2'd1;
    localparam logic [1:0] ORDER_AGE_THR  = 2'd3;

`ifdef PUMICE_ENHANCED
    localparam bit SUPPORT_GLOBAL_ORDER = 1'b1;
`else
    localparam bit SUPPORT_GLOBAL_ORDER = 1'b0;
`endif

    logic [NUM_ENTRIES-1:0] w_rd_head, w_wr_head;
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic older_rd = 1'b0;
            automatic logic older_wr = 1'b0;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if ((j != i) && rd_sch_valid_i[j]
                    && rd_sch_older_i[j*NUM_ENTRIES + i]) older_rd = 1'b1;
                if ((j != i) && wr_sch_valid_i[j]
                    && wr_sch_older_i[j*NUM_ENTRIES + i]) older_wr = 1'b1;
            end
            w_rd_head[i] = rd_sch_valid_i[i] && !older_rd;
            w_wr_head[i] = wr_sch_valid_i[i] && !older_wr;
        end
    end

    logic w_rd_head_wins;
    assign w_rd_head_wins = !(|wr_sch_valid_i)
                          || ((|rd_sch_valid_i)
                              && (rd_sch_head_rel_i >= wr_sch_head_rel_i));

    logic w_boost_any;
    assign w_boost_any = (|rd_sch_age_exceed_i) || (|wr_sch_age_exceed_i);

    logic [NUM_ENTRIES-1:0] rd_col_me, rd_act_me, rd_pre_me;
    logic [NUM_ENTRIES-1:0] wr_col_me, wr_act_me, wr_pre_me;
    always_comb begin
        rd_col_me = rd_col_m; rd_act_me = rd_act_m; rd_pre_me = rd_pre_m;
        wr_col_me = wr_col_m; wr_act_me = wr_act_m; wr_pre_me = wr_pre_m;
        if (sched_order_mode_i == ORDER_IN_ORDER) begin
            rd_col_me &= w_rd_head; rd_act_me &= w_rd_head; rd_pre_me &= w_rd_head;
            wr_col_me &= w_wr_head; wr_act_me &= w_wr_head; wr_pre_me &= w_wr_head;
            if (SUPPORT_GLOBAL_ORDER) begin
                if (w_rd_head_wins) begin
                    wr_col_me = '0; wr_act_me = '0; wr_pre_me = '0;
                end else begin
                    rd_col_me = '0; rd_act_me = '0; rd_pre_me = '0;
                end
            end
        end else if (sched_order_mode_i == ORDER_AGE_THR && w_boost_any) begin
            rd_col_me &= rd_sch_age_exceed_i; rd_act_me &= rd_sch_age_exceed_i;
            rd_pre_me &= rd_sch_age_exceed_i;
            wr_col_me &= wr_sch_age_exceed_i; wr_act_me &= wr_sch_age_exceed_i;
            wr_pre_me &= wr_sch_age_exceed_i;
        end
    end

    // ---- per-entry pending population --------------------------------------
    localparam int POPW = $clog2(NUM_ENTRIES + 1);
    logic [POPW-1:0] rd_pop [NUM_ENTRIES];
    logic [POPW-1:0] wr_pop [NUM_ENTRIES];
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            rd_pop[i] = '0;
            wr_pop[i] = '0;
        end
        for (int e = 0; e < POOL; e++) begin
            automatic logic           pdir = (e >= NUM_ENTRIES);
            automatic int             pslot = pdir ? (e - NUM_ENTRIES) : e;
            automatic logic [BKW-1:0] ppbk = f_pool_bank(PTXW'(e));
            automatic logic [ROW_WIDTH-1:0] pprw = f_pool_row(PTXW'(e));
            for (int j = 0; j < POOL; j++) begin
                if (pool_valid[j] && ((j >= NUM_ENTRIES) == pdir)
                    && (f_pool_bank(PTXW'(j)) == ppbk)
                    && (f_pool_row (PTXW'(j)) == pprw)) begin
                    if (pdir) wr_pop[pslot] = wr_pop[pslot] + POPW'(1);
                    else      rd_pop[pslot] = rd_pop[pslot] + POPW'(1);
                end
            end
        end
    end

    // ---- oldest-with-population-policy pick --------------------------------
    function automatic logic [PTRW:0] arg_sel(
        input logic [1:0]                          sel,
        input logic [NUM_ENTRIES-1:0]              mask,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  older,
        input logic [POPW-1:0]                     pops [NUM_ENTRIES]
    );
        logic                   found;
        logic [PTRW-1:0]        slot;
        logic [NUM_ENTRIES-1:0] is_best;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic [NUM_ENTRIES-1:0] orow = older[i*NUM_ENTRIES +: NUM_ENTRIES];
            automatic logic best = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if ((j != i) && mask[j]) begin
                    automatic logic j_pop_wins =
                        (sel == 2'd1) ? (pops[j] > pops[i]) :
                        (sel == 2'd2) ? (pops[j] < pops[i]) : 1'b0;
                    automatic logic pop_tie =
                        (sel == 2'd0) || (pops[j] == pops[i]);
                    if (j_pop_wins || (pop_tie && !orow[j])) best = 1'b0;
                end
            end
            is_best[i] = mask[i] && best;
        end
        found = |is_best;
        slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (is_best[i]) slot = PTRW'(i);
        return {found, slot};
    endfunction

    // ---- ACCESS_PREF / QoS -------------------------------------------------
    typedef enum logic [1:0] {CL_NONE, CL_COL, CL_ACT, CL_PRE} pick_class_e;

    function automatic logic [NUM_ENTRIES-1:0] qos_top(
        input logic [NUM_ENTRIES-1:0]     mask,
        input logic [NUM_ENTRIES*4-1:0]   qosv
    );
        logic [3:0] best;
        logic [NUM_ENTRIES-1:0] out;
        best = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (mask[i] && (qosv[i*4 +: 4] > best)) best = qosv[i*4 +: 4];
        for (int i = 0; i < NUM_ENTRIES; i++)
            out[i] = mask[i] && (qosv[i*4 +: 4] == best);
        return out;
    endfunction

    logic [NUM_ENTRIES-1:0] rd_col_q, rd_act_q, rd_pre_q;
    logic [NUM_ENTRIES-1:0] wr_col_q, wr_act_q, wr_pre_q;
    always_comb begin
        rd_col_q = sched_qos_en_i ? qos_top(rd_col_me, rd_sch_qos_i) : rd_col_me;
        rd_act_q = sched_qos_en_i ? qos_top(rd_act_me, rd_sch_qos_i) : rd_act_me;
        rd_pre_q = sched_qos_en_i ? qos_top(rd_pre_me, rd_sch_qos_i) : rd_pre_me;
        wr_col_q = sched_qos_en_i ? qos_top(wr_col_me, wr_sch_qos_i) : wr_col_me;
        wr_act_q = sched_qos_en_i ? qos_top(wr_act_me, wr_sch_qos_i) : wr_act_me;
        wr_pre_q = sched_qos_en_i ? qos_top(wr_pre_me, wr_sch_qos_i) : wr_pre_me;
    end

    // ---- STAGE 1a ----------------------------------------------------------
    logic [NUM_ENTRIES-1:0]             r_rd_col_q, r_rd_act_q, r_rd_pre_q;
    logic [NUM_ENTRIES-1:0]             r_wr_col_q, r_wr_act_q, r_wr_pre_q;
    logic [NUM_ENTRIES*NUM_ENTRIES-1:0] r_rd_older, r_wr_older;
    logic [POPW-1:0]                    r_rd_pop [NUM_ENTRIES];
    logic [POPW-1:0]                    r_wr_pop [NUM_ENTRIES];
    logic [1:0]                         r_col_sel, r_row_sel;
    logic [NUM_BANKS-1:0]               r_ap_snap;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_col_q <= '0; r_rd_act_q <= '0; r_rd_pre_q <= '0;
            r_wr_col_q <= '0; r_wr_act_q <= '0; r_wr_pre_q <= '0;
            r_rd_older <= '0; r_wr_older <= '0;
            r_col_sel  <= '0; r_row_sel  <= '0;
            r_ap_snap  <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_rd_pop[i] <= '0; r_wr_pop[i] <= '0;
            end
        end else if (w_out_ready) begin
            r_rd_col_q <= rd_col_q; r_rd_act_q <= rd_act_q; r_rd_pre_q <= rd_pre_q;
            r_wr_col_q <= wr_col_q; r_wr_act_q <= wr_act_q; r_wr_pre_q <= wr_pre_q;
            r_rd_older <= rd_sch_older_i; r_wr_older <= wr_sch_older_i;
            r_col_sel  <= sched_col_sel_i; r_row_sel <= sched_row_sel_i;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_rd_pop[i] <= rd_pop[i]; r_wr_pop[i] <= wr_pop[i];
            end
            for (int b = 0; b < NUM_BANKS; b++) r_ap_snap[b] <= f_ap(BKW'(b));
        end
    )

    // ---- STAGE 1b ----------------------------------------------------------
    logic w_act_gate_live;
    assign w_act_gate_live = !w_rfc_busy && tfaw_ok_i[RK0] && trrd_ok_i[RK0] && w_trrd_ls_ok;

    logic w_rd_turn_live, w_wr_turn_live;
    assign w_rd_turn_live = twtr_ok_i && !w_rd_turn_block
                         && !(w_fire_out && r_do_wr);
    assign w_wr_turn_live = trtw_ok_i && !w_wr_turn_block
                         && !(w_fire_out && r_do_rd);
    always_comb begin
        {w_sel_rd_col_f, w_sel_rd_col_s} =
            arg_sel(r_col_sel, r_rd_col_q & rd_sch_valid_i, r_rd_older, r_rd_pop);
        {w_sel_wr_col_f, w_sel_wr_col_s} =
            arg_sel(r_col_sel, r_wr_col_q & wr_sch_valid_i, r_wr_older, r_wr_pop);
        {w_sel_rd_act_f, w_sel_rd_act_s} =
            arg_sel(r_row_sel, r_rd_act_q & rd_sch_valid_i, r_rd_older, r_rd_pop);
        {w_sel_wr_act_f, w_sel_wr_act_s} =
            arg_sel(r_row_sel, r_wr_act_q & wr_sch_valid_i, r_wr_older, r_wr_pop);
        {w_sel_rd_pre_f, w_sel_rd_pre_s} = arg_oldest(r_rd_pre_q & rd_sch_valid_i, r_rd_older);
        {w_sel_wr_pre_f, w_sel_wr_pre_s} = arg_oldest(r_wr_pre_q & wr_sch_valid_i, r_wr_older);
        if (!w_act_gate_live) begin
            w_sel_rd_act_f = 1'b0;
            w_sel_wr_act_f = 1'b0;
        end
    end

    // ---- registered pre-pick -----------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_col_f <= 1'b0; wr_col_f <= 1'b0; rd_act_f <= 1'b0;
            wr_act_f <= 1'b0; rd_pre_f <= 1'b0; wr_pre_f <= 1'b0;
            rd_col_ap <= 1'b0; wr_col_ap <= 1'b0;
        end else if (w_out_ready) begin
            rd_col_f <= w_sel_rd_col_f; rd_col_s <= w_sel_rd_col_s;
            wr_col_f <= w_sel_wr_col_f; wr_col_s <= w_sel_wr_col_s;
            rd_col_ap <= r_ap_snap[f_bank(rd_sch_bank_i, w_sel_rd_col_s)];
            wr_col_ap <= r_ap_snap[f_bank(wr_sch_bank_i, w_sel_wr_col_s)];
            rd_act_f <= w_sel_rd_act_f; rd_act_s <= w_sel_rd_act_s;
            wr_act_f <= w_sel_wr_act_f; wr_act_s <= w_sel_wr_act_s;
            rd_pre_f <= w_sel_rd_pre_f; rd_pre_s <= w_sel_rd_pre_s;
            wr_pre_f <= w_sel_wr_pre_f; wr_pre_s <= w_sel_wr_pre_s;
            rd_col_bank <= f_bank(rd_sch_bank_i, w_sel_rd_col_s);
            rd_col_col  <= f_col (rd_sch_col_i,  w_sel_rd_col_s);
            wr_col_bank <= f_bank(wr_sch_bank_i, w_sel_wr_col_s);
            wr_col_col  <= f_col (wr_sch_col_i,  w_sel_wr_col_s);
            rd_act_bank <= f_bank(rd_sch_bank_i, w_sel_rd_act_s);
            rd_act_row  <= f_row (rd_sch_row_i,  w_sel_rd_act_s);
            wr_act_bank <= f_bank(wr_sch_bank_i, w_sel_wr_act_s);
            wr_act_row  <= f_row (wr_sch_row_i,  w_sel_wr_act_s);
            rd_pre_bank <= f_bank(rd_sch_bank_i, w_sel_rd_pre_s);
            wr_pre_bank <= f_bank(wr_sch_bank_i, w_sel_wr_pre_s);
        end
    )

    // ---- write-batching drain state ----------------------------------------
    localparam int OCCW = $clog2(NUM_ENTRIES + 1);
    logic [OCCW-1:0] w_wr_occ;
    always_comb begin
        w_wr_occ = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (wr_sch_valid_i[i]) w_wr_occ = w_wr_occ + OCCW'(1);
    end

    logic r_dir_rr;

    localparam int WR_BATCH_W = 8;
    logic                    r_wr_drain;
    logic [WR_BATCH_W-1:0]   r_wr_batch_cnt;
    logic                    r_rd_owed;
    logic w_wr_col_fire, w_rd_col_fire, w_batch_done;
    assign w_wr_col_fire = w_fire_out && r_do_wr;
    assign w_rd_col_fire = w_fire_out && r_do_rd;
    assign w_batch_done  = r_wr_drain && w_wr_col_fire
                         && (sched_wr_batch_max_i != 8'd0)
                         && (r_wr_batch_cnt >= (sched_wr_batch_max_i - 8'd1));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_drain     <= 1'b0;
            r_wr_batch_cnt <= '0;
            r_rd_owed      <= 1'b0;
        end else begin
            if (w_rd_col_fire) r_rd_owed <= 1'b0;

            if (sched_wr_high_wm_i == 8'd0) begin
                r_wr_drain     <= 1'b0;
                r_wr_batch_cnt <= '0;
                r_rd_owed      <= 1'b0;
            end else if (w_batch_done) begin
                r_wr_drain     <= 1'b0;
                r_wr_batch_cnt <= '0;
                r_rd_owed      <= 1'b1;
            end else if (8'(w_wr_occ) <= sched_wr_low_wm_i) begin
                r_wr_drain     <= 1'b0;
                r_wr_batch_cnt <= '0;
            end else if (8'(w_wr_occ) >= sched_wr_high_wm_i && !r_rd_owed) begin
                r_wr_drain     <= 1'b1;
                if (w_wr_col_fire) r_wr_batch_cnt <= r_wr_batch_cnt + 1'b1;
            end else if (r_wr_drain && w_wr_col_fire) begin
                r_wr_batch_cnt <= r_wr_batch_cnt + 1'b1;
            end
        end
    )

    // ---- stall-cause attribution (TASK-006) --------------------------------
    logic w_any_pending, w_stalled;
    assign w_any_pending = (|rd_sch_valid_i) || (|wr_sch_valid_i);
    assign w_stalled     = !w_fire_out;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            stall_bp_o         <= 32'h0;
            stall_refresh_o    <= 32'h0;
            stall_turnaround_o <= 32'h0;
            stall_tccd_o       <= 32'h0;
            stall_actlimit_o   <= 32'h0;
            stall_banktimer_o  <= 32'h0;
            stall_noreq_o      <= 32'h0;
            stall_zq_o         <= 32'h0;
        end else if (w_stalled) begin
            if (w_out_reject)
                stall_banktimer_o  <= stall_banktimer_o + 32'h1;
            else if (w_out_hold)
                stall_actlimit_o   <= stall_actlimit_o + 32'h1;
            else if (r_pick_valid)
                stall_bp_o         <= stall_bp_o + 32'h1;
            else if (HAS_ZQ && (w_zq_busy || zq_req_i))
                stall_zq_o         <= stall_zq_o + 32'h1;
            else if (refresh_req_i || refresh_drain_i)
                stall_refresh_o    <= stall_refresh_o + 32'h1;
            else if (!w_any_pending)
                stall_noreq_o      <= stall_noreq_o + 32'h1;
            else if (!twtr_ok_i || !trtw_ok_i)
                stall_turnaround_o <= stall_turnaround_o + 32'h1;
            else if (!tccd_ok_i)
                stall_tccd_o       <= stall_tccd_o + 32'h1;
            else if (!tfaw_ok_i[RK0] || !trrd_ok_i[RK0])
                stall_actlimit_o   <= stall_actlimit_o + 32'h1;
            else
                stall_banktimer_o  <= stall_banktimer_o + 32'h1;
        end
    )

    // Per-class "write goes first" decision
    logic w_col_wrf, w_act_wrf, w_pre_wrf;
    always_comb begin
        automatic logic rr = (sched_prio_sub_i == 2'd1) && r_dir_rr;
        w_col_wrf = r_wr_drain || rr
                  || ((sched_prio_sub_i == 2'd3)
                      && wr_sch_age_exceed_i[wr_col_s]
                      && !rd_sch_age_exceed_i[rd_col_s]);
        w_act_wrf = r_wr_drain || rr
                  || ((sched_prio_sub_i == 2'd3)
                      && wr_sch_age_exceed_i[wr_act_s]
                      && !rd_sch_age_exceed_i[rd_act_s]);
        w_pre_wrf = r_wr_drain || rr
                  || ((sched_prio_sub_i == 2'd3)
                      && wr_sch_age_exceed_i[wr_pre_s]
                      && !rd_sch_age_exceed_i[rd_pre_s]);
    end

    logic w_c_col, w_c_act, w_c_pre;
    pick_class_e w_pick_class;
    always_comb begin
        w_c_col = rd_col_f || wr_col_f;
        w_c_act = (rd_act_f || wr_act_f) && w_act_gate_live;
        w_c_pre = rd_pre_f || wr_pre_f;
        unique case (sched_access_pref_i)
            2'd2:    w_pick_class = w_c_act ? CL_ACT
                                  : w_c_col ? CL_COL
                                  : w_c_pre ? CL_PRE : CL_NONE;
            2'd3:    w_pick_class = w_c_pre ? CL_PRE
                                  : w_c_col ? CL_COL
                                  : w_c_act ? CL_ACT : CL_NONE;
            default: w_pick_class = w_c_col ? CL_COL
                                  : w_c_act ? CL_ACT
                                  : w_c_pre ? CL_PRE : CL_NONE;
        endcase
    end

    // ---- refresh: pick the lowest active bank that can precharge ------------
    logic            w_any_active, w_rfsh_pre_found, w_ref_safe;
    logic [BKW-1:0]  w_rfsh_pre_bank;
    always_comb begin
        w_any_active     = |r_bank_row_active[RK0];
        w_rfsh_pre_found = 1'b0;
        w_rfsh_pre_bank  = '0;
        for (int j = NUM_BANKS-1; j >= 0; j--)
            if (r_bank_row_active[RK0][j] && r_bank_pre_ready[RK0][j] && !w_guarded[j]) begin
                w_rfsh_pre_found = 1'b1;
                w_rfsh_pre_bank  = BKW'(j);
            end
    end
    assign w_ref_safe = !w_any_active && !w_inflight_preact
                      && (r_guard0 == '0) && (r_guard1 == '0)
                      && !w_rfc_busy && !r_grant && !r_maint_grant;

    logic w_refpb_safe;
    assign w_refpb_safe = !r_bank_row_active[RK0][refresh_bank_i]
                        && !w_inflight_preact
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant && !r_maint_grant;

    // Generic maintenance grant safety: all banks idle, no row-affecting command
    // in flight or inside its guard window, and no REF/ZQ recovery. !r_grant /
    // !r_maint_grant / !r_zq_grant stop a held request from re-picking while the
    // granted command sits in the output register.
    logic w_maint_safe;
    assign w_maint_safe = !w_any_active && !w_inflight_preact
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !w_zq_busy && !r_grant && !r_maint_grant
                        && !(HAS_ZQ && r_zq_grant);

    // ZQCS safety (when HAS_ZQ)
    logic w_zq_safe;
    assign w_zq_safe = !w_any_active && !w_inflight_preact
                     && (r_guard0 == '0) && (r_guard1 == '0)
                     && !w_rfc_busy && !w_zq_busy && !r_grant && !r_maint_grant;

    // ========================================================================
    // Priority pick (combinational)
    // ========================================================================
    dram_op_e        w_op;
    logic [BKW-1:0]  w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;
    logic            w_ap_out;
    logic            w_valid;
    logic            w_do_act, w_do_rd, w_do_wr, w_do_pre, w_grant;
    logic            w_zq_grant;
    logic            w_maint_grant;
    logic            w_wr_commit, w_rd_issue;
    logic [PTRW-1:0] w_commit_slot, w_issue_slot;

    always_comb begin
        w_op = OP_NOP; w_bank = '0; w_row = '0; w_col = '0; w_ap_out = 1'b0;
        w_valid = 1'b0;
        w_do_act = 1'b0; w_do_rd = 1'b0; w_do_wr = 1'b0; w_do_pre = 1'b0;
        w_grant = 1'b0; w_zq_grant = 1'b0; w_maint_grant = 1'b0;
        w_wr_commit = 1'b0; w_rd_issue = 1'b0;
        w_commit_slot = '0; w_issue_slot = '0;

        if (!init_done_i) begin
            if (init_cmd_valid_i) begin
                w_valid = 1'b1; w_op = init_cmd_op_i;
                w_bank = init_cmd_bank_i; w_row = init_cmd_row_i;
            end
        end else if (HAS_ZQ && w_zq_busy) begin
            // tZQCS window: DRAM calibrating, no command may issue.
            w_valid = 1'b0;
        end else if (refresh_req_i || refresh_drain_i) begin
            if (refresh_kind_i) begin
                if (r_bank_row_active[RK0][refresh_bank_i]) begin
                    if (r_bank_pre_ready[RK0][refresh_bank_i]
                        && !w_guarded[refresh_bank_i]) begin
                        w_valid = 1'b1; w_op = OP_PRE; w_bank = refresh_bank_i;
                        w_do_pre = 1'b1;
                    end
                end else if (w_refpb_safe) begin
                    w_valid = 1'b1; w_op = OP_REFPB; w_bank = refresh_bank_i;
                    w_grant = 1'b1;
                end
            end else if (w_any_active) begin
                if (w_rfsh_pre_found) begin
                    w_valid = 1'b1; w_op = OP_PRE; w_bank = w_rfsh_pre_bank;
                    w_do_pre = 1'b1;
                end
            end else if (w_ref_safe) begin
                w_valid = 1'b1; w_op = OP_REF; w_grant = 1'b1;
            end
        end else if (HAS_ZQ && zq_req_i) begin
            if (w_any_active) begin
                if (w_rfsh_pre_found) begin
                    w_valid = 1'b1; w_op = OP_PRE; w_bank = w_rfsh_pre_bank;
                    w_do_pre = 1'b1;
                end
            end else if (w_zq_safe) begin
                w_valid = 1'b1; w_op = OP_ZQCS; w_zq_grant = 1'b1;
            end
        end else if (maint_req_i && w_maint_safe) begin
            w_valid = 1'b1; w_op = maint_op_i;
            w_bank = maint_bank_i; w_row = maint_row_i; w_col = maint_col_i;
            w_maint_grant = 1'b1;
        end else if (w_pick_class == CL_COL && rd_col_f && rd_issue_ready_i
                     && w_rd_turn_live
                     && !(w_col_wrf && wr_col_f && wr_commit_ready_i
                          && w_wr_turn_live)) begin
            w_bank = rd_col_bank; w_col = rd_col_col;
            w_valid = 1'b1; w_op = rd_col_ap ? OP_RDA : OP_RD;
            w_ap_out = rd_col_ap; w_do_rd = 1'b1; w_rd_issue = 1'b1; w_issue_slot = rd_col_s;
        end else if (w_pick_class == CL_COL && wr_col_f && wr_commit_ready_i
                     && w_wr_turn_live) begin
            w_bank = wr_col_bank; w_col = wr_col_col;
            w_valid = 1'b1; w_op = wr_col_ap ? OP_WRA : OP_WR;
            w_ap_out = wr_col_ap; w_do_wr = 1'b1; w_wr_commit = 1'b1; w_commit_slot = wr_col_s;
        end else if (w_pick_class == CL_ACT && rd_act_f && w_act_gate_live
                     && !(w_act_wrf && wr_act_f)) begin
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = rd_act_bank; w_row = rd_act_row;
            w_do_act = 1'b1;
        end else if (w_pick_class == CL_ACT && wr_act_f && w_act_gate_live) begin
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = wr_act_bank; w_row = wr_act_row;
            w_do_act = 1'b1;
        end else if (w_pick_class == CL_PRE && rd_pre_f
                     && !(w_pre_wrf && wr_pre_f)) begin
            w_valid = 1'b1; w_op = OP_PRE; w_bank = rd_pre_bank;
            w_do_pre = 1'b1;
        end else if (w_pick_class == CL_PRE && wr_pre_f) begin
            w_valid = 1'b1; w_op = OP_PRE; w_bank = wr_pre_bank;
            w_do_pre = 1'b1;
        end else if (timeout_pre_req_i
                     && r_bank_row_active[RK0][timeout_pre_bank_i]
                     && r_bank_pre_ready[RK0][timeout_pre_bank_i]
                     && !w_guarded[timeout_pre_bank_i]) begin
            w_valid = 1'b1; w_op = OP_PRE; w_bank = timeout_pre_bank_i;
            w_do_pre = 1'b1;
        end
    end

    // ---- output register ----------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dir_rr <= 1'b0;
        else if (w_fire_out && (r_do_rd || r_do_wr || r_do_act || r_do_pre))
            r_dir_rr <= ~r_dir_rr;
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pick_valid <= 1'b0;
            r_do_act <= 1'b0; r_do_rd <= 1'b0; r_do_wr <= 1'b0; r_do_pre <= 1'b0;
            r_grant  <= 1'b0; r_maint_grant <= 1'b0; r_zq_grant <= 1'b0; r_wr_commit <= 1'b0; r_rd_issue <= 1'b0;
            r_cmd_extra <= '0;
        end else if (w_out_ready) begin
            r_pick_valid  <= w_valid;
            r_op          <= w_op;
            r_bank        <= w_bank;
            r_row         <= w_row;
            r_col_out     <= w_col;
            r_ap_out      <= w_ap_out;
            r_do_act      <= w_do_act;
            r_do_rd       <= w_do_rd;
            r_do_wr       <= w_do_wr;
            r_do_pre      <= w_do_pre;
            r_grant       <= w_grant;
            r_maint_grant <= w_maint_grant;
            r_zq_grant    <= w_zq_grant;
            r_cmd_extra   <= w_maint_grant ? maint_extra_i : '0;
            r_wr_commit   <= w_wr_commit;
            r_commit_slot <= w_commit_slot;
            r_rd_issue    <= w_rd_issue;
            r_issue_slot  <= w_issue_slot;
        end
    )

    // ---- command push outputs ----------------------------------------------
    assign cmd_valid_o = r_pick_valid && w_out_safe;
    assign cmd_op_o    = r_op;
    assign cmd_rank_o  = RKW'(RK0);
    assign cmd_bank_o  = r_bank;
    assign cmd_row_o   = r_row;
    assign cmd_col_o   = r_col_out;
    assign cmd_ap_o    = r_ap_out;
    assign cmd_extra_o = r_cmd_extra;

    // ---- event strobes -----------------------------------------------------
    assign evt_act_o = w_fire_out && r_do_act;
    assign evt_rd_o  = w_fire_out && r_do_rd;
    assign evt_wr_o  = w_fire_out && r_do_wr;
    assign evt_pre_o = w_fire_out && r_do_pre;
    assign evt_ap_o  = r_ap_out;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = r_bank;
    assign evt_row_o  = r_row;

    // ---- CAM commit / issue / refresh grant / maintenance grant ------------
    assign wr_commit_valid_o = w_fire_out && r_wr_commit;
    assign wr_commit_slot_o  = r_commit_slot;
    assign rd_issue_valid_o  = w_fire_out && r_rd_issue;
    assign rd_issue_slot_o   = r_issue_slot;
    assign refresh_grant_o   = w_fire_out && r_grant;
    assign zq_grant_o        = HAS_ZQ ? (w_fire_out && r_zq_grant) : 1'b0;
    assign maint_grant_o     = w_fire_out && r_maint_grant;

    // ---- guard update -------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0 <= '0;
            r_guard1 <= '0;
            r_ap_closing <= '0;
            r_wrfire0 <= 1'b0; r_wrfire1 <= 1'b0;
            r_rdfire0 <= 1'b0; r_rdfire1 <= 1'b0;
            r_apguard0 <= '0;  r_apguard1 <= '0;
            r_preguard0 <= '0; r_preguard1 <= '0; r_preguard2 <= '0;
        end else begin
            r_guard1 <= r_guard0;
            r_guard0 <= '0;
            r_ap_closing <= w_ap_fire_bank | (r_ap_closing & r_bank_row_active[RK0]);
            if (w_fire_out && (r_do_act || r_do_pre || r_do_rd || r_do_wr))
                r_guard0 <= (NUM_BANKS'(1) << r_bank);
            r_preguard2 <= r_preguard1;
            r_preguard1 <= r_preguard0;
            r_preguard0 <= (w_fire_out && r_do_pre)
                         ? (NUM_BANKS'(1) << r_bank) : '0;
            r_wrfire1 <= r_wrfire0;
            r_wrfire0 <= w_fire_out && r_do_wr;
            r_rdfire1 <= r_rdfire0;
            r_rdfire0 <= w_fire_out && r_do_rd;
            r_apguard1 <= r_apguard0;
            r_apguard0 <= '0;
            if (w_fire_out && (r_do_rd || r_do_wr) && r_ap_out)
                r_apguard0 <= (NUM_BANKS'(1) << r_bank);
        end
    )

    // ---- tRFC recovery counter ---------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rfc_cnt <= '0;
        end else if (w_fire_out && r_grant) begin
            r_rfc_cnt <= (r_op == OP_REFPB && t_rfc_pb_i != 8'd0)
                       ? {8'h0, t_rfc_pb_i} : t_rfc_i;
        end else if (w_rfc_busy) begin
            r_rfc_cnt <= r_rfc_cnt - 16'd1;
        end
    )

    // ---- tZQCS block counter ------------------------------------------------
    generate if (HAS_ZQ) begin : g_zqcs_cnt
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_zqcs_cnt <= '0;
            end else if (w_fire_out && r_zq_grant) begin
                r_zqcs_cnt <= t_zqcs_i;
            end else if (w_zq_busy) begin
                r_zqcs_cnt <= r_zqcs_cnt - 16'd1;
            end
        )
    end else begin : g_no_zqcs_cnt
        assign r_zqcs_cnt = 16'd0;
    end endgenerate

    // ---- L/S group drivers --------------------------------------------------
    assign w_pick_group = (NUM_BG > 1) ? r_bank[BKW-1 -: BGW_EFF] : '0;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_last_col_bg <= '0;
            r_last_act_bg <= '0;
        end else begin
            if (w_rd_col_fire || w_wr_col_fire) r_last_col_bg <= w_pick_group;
            if (w_fire_out && r_do_act)         r_last_act_bg <= w_pick_group;
        end
    )

    // Degenerates correctly at NUM_BG==1: w_pick_group/r_last_*_bg are both
    // zero, so the same-group term is true and the long window governs.
    assign w_tccd_ls_ok = (w_pick_group != r_last_col_bg) || tccd_l_ok_i;
    assign w_trrd_ls_ok = (w_pick_group != r_last_act_bg) || trrd_l_ok_i;
    assign pick_group_o = w_pick_group;

endmodule : mc_cmd_arbiter
