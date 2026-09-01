// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// pumice_page_policy — runtime page-policy engine + page/command telemetry.
//
// PUMICE-006 Axis 2. Watches the arbiter's ISSUED command stream (the same
// valid&&ready stream the cmd-history checker audits) plus the registered
// per-bank row state, and produces two things:
//
//   1. The auto-precharge decision, per bank (`ap_close_o` + `ap_mode_en_o`).
//      With POLICY_MODE==0 the arbiter keeps the legacy flat w_ap
//      (page_policy_i == CLOSE; the retired HYBRID encoding maps to OPEN);
//      any nonzero mode takes over:
//        1 static_open   ap=0 everywhere
//        2 static_close  ap=1 everywhere
//        3 fixed_open    ap=0; rows close by IDLE TIMEOUT instead
//        4 adapt_time    ap=0; per-bank timeout register TR adapts (Happy
//                        adaptive-timeout: mistake counter MC, premature-close
//                        vs held-too-long, TR += / -= step each check interval)
//        5 adapt_access  ap = per-row 2-bit close predictor (Happy "Hybrid",
//                        pumice_row_pred_table; knob-free)   NOT BUILT
//        6 rbl_static    ap = per-bank low-locality verdict from the RBLA
//                        miss-counter table (pumice_rbl_table) NOT BUILT
//        7 rbl_dyn       rbl_static + per-epoch hill-climb      NOT BUILT
//
//   MODES 5/6/7 ARE NOT BUILT (2026-09-01). Their predictor tables were 60% of
//   all failing timing endpoints on the Nexys A7 and are set aside under
//   rtl/OLD/ -- correct and mutation-proven, just too expensive for this part.
//   They decode to the default policy (no auto-precharge). The CSR field and
//   the PAGE_RBL_CFG / PAGE_POLICY_CFG inputs are UNCHANGED so nothing in the
//   register map, the host or the parent wiring has to move to restore them.
//
//   2. A background precharge REQUEST (`timeout_pre_req_o` / bank) for a row
//      whose idle timer expired. The ARBITER issues the actual PRE as its
//      lowest-priority pick, so demand traffic, refresh drain and JEDEC
//      timing (pre_ready, the 2-cycle guard) all still gate it — this block
//      never touches the wire.
//
// Telemetry (always on, mode-independent, feeds the *_STATS CSRs):
//   page_hit    every column op issued (columns only issue on row hits here)
//   page_miss   ACT to a bank whose previous close was a WRONG-ROW PRE
//   page_empty  ACT to a bank that was simply closed (no conflict)
//   act/pre/ref command-class counters
//
// adapt_time mistake taxonomy (per the Happy paper, at this command stream):
//   premature close : an ACT re-opens the SAME row a timeout PRE just closed
//                     on that bank -> the timer fired too early -> MC++
//   held too long   : a WRONG-ROW (conflict) PRE closes a bank whose timer had
//                     not expired -> holding gained nothing -> MC--
// Every check_interval cycles: MC > mc_high_thr -> TR += step;
// MC < mc_low_thr -> TR -= step; clamp [tr_min, tr_max]; MC re-arms to
// mc_init. TR is GLOBAL when policy_scope==1, per-bank when 0.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_page_policy
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // ---- mode-select CSR fields (SCHED/PAGE_* registers) -------------------
    input  logic [2:0]                 policy_mode_i,     // PAGE_POLICY_CFG.policy_mode
    input  logic                       policy_scope_i,    // 0=per-bank TR, 1=global TR
    input  logic [3:0]                 ctr_thresh_i,      // PAGE_POLICY_CFG.ctr_open_max
    input  logic [3:0]                 ctr_init_i,        // PAGE_POLICY_CFG.ctr_init
    input  logic [7:0]                 tr_init_i,         // PAGE_TIMEOUT_CFG
    input  logic [7:0]                 tr_min_i,
    input  logic [7:0]                 tr_max_i,
    input  logic [7:0]                 tr_step_i,
    input  logic [3:0]                 mc_high_thr_i,     // PAGE_ADAPT_CFG
    input  logic [3:0]                 mc_low_thr_i,
    input  logic [3:0]                 mc_init_i,
    input  logic [15:0]                check_interval_i,
    // UNUSED while modes 6/7 are not built (see the header). Kept as ports so
    // the CSR wiring in the parent is untouched and restoring the tables is a
    // change to this file alone.
    /* verilator lint_off UNUSED */
    input  logic [7:0]                 rbl_miss_thresh_i, // PAGE_RBL_CFG
    input  logic [1:0]                 rbl_ways_i,
    input  logic [3:0]                 rbl_sets_i,
    input  logic [15:0]                rbl_reset_ivl_i,
    /* verilator lint_on UNUSED */

    // ---- issued command stream (arbiter output, single-issue) --------------
    input  logic                       cmd_valid_i,       // cmd_valid && cmd_ready
    input  dram_op_e                   cmd_op_i,
    input  logic [BKW-1:0]             cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]       cmd_row_i,

    // ---- registered per-bank row state (same bus the arbiter registers) ----
    input  logic [NUM_BANKS-1:0]       bank_row_active_i,
    input  logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,

    // ---- decisions to the arbiter ------------------------------------------
    output logic                       ap_mode_en_o,      // 1 = ap_close_o overrides legacy w_ap
    output logic [NUM_BANKS-1:0]       ap_close_o,        // per-bank: close after this column op
    output logic                       timeout_pre_req_o, // background close request
    output logic [BKW-1:0]             timeout_pre_bank_o,

    // ---- telemetry (to the *_STATS CSRs; free-running, cleared on reset) ---
    output logic [31:0]                stat_page_hit_o,
    output logic [31:0]                stat_page_miss_o,
    output logic [31:0]                stat_page_empty_o,
    output logic [31:0]                stat_act_o,
    output logic [31:0]                stat_pre_o,
    output logic [31:0]                stat_ref_o
);

    localparam logic [2:0] MODE_DEFAULT      = 3'd0;
    localparam logic [2:0] MODE_STATIC_OPEN  = 3'd1;
    localparam logic [2:0] MODE_STATIC_CLOSE = 3'd2;
    localparam logic [2:0] MODE_FIXED_OPEN   = 3'd3;
    localparam logic [2:0] MODE_ADAPT_TIME   = 3'd4;
    localparam logic [2:0] MODE_ADAPT_ACCESS = 3'd5;
    localparam logic [2:0] MODE_RBL_STATIC   = 3'd6;
    localparam logic [2:0] MODE_RBL_DYN      = 3'd7;

    // MODES 5/6/7 ARE NOT BUILT (2026-09-01). Their predictor tables --
    // pumice_row_pred_table and pumice_rbl_table -- were 60% of all failing
    // timing endpoints on the Nexys A7 (u_rbl 1546, u_row_pred 1049 of 4307)
    // with only a single-generator harness in front of them. The RTL is set
    // aside under rtl/OLD/, correct and mutation-proven; see that README.
    //
    // They decode to the DEFAULT policy here rather than being rejected: the
    // CSR field is unchanged and software may still write 5/6/7, so this has
    // to be a defined, harmless behaviour rather than an X. A host that wants
    // to know reads PAGE_CAP below.
    logic w_mode_on, w_timeout_on, w_adapt_on;
    assign w_mode_on    = (policy_mode_i == MODE_STATIC_OPEN)
                       || (policy_mode_i == MODE_STATIC_CLOSE)
                       || (policy_mode_i == MODE_FIXED_OPEN)
                       || (policy_mode_i == MODE_ADAPT_TIME);
    assign w_timeout_on = (policy_mode_i == MODE_FIXED_OPEN)
                       || (policy_mode_i == MODE_ADAPT_TIME);
    assign w_adapt_on   = (policy_mode_i == MODE_ADAPT_TIME);

    // ---- auto-precharge decision -------------------------------------------
    assign ap_mode_en_o = w_mode_on;
    assign ap_close_o   = (policy_mode_i == MODE_STATIC_CLOSE) ? {NUM_BANKS{1'b1}}
                                                                : '0;



    // ---- issued-stream decodes ---------------------------------------------
    logic w_is_col, w_is_act, w_is_pre, w_is_ref;
    assign w_is_col = cmd_valid_i && is_column_op(cmd_op_i);
    assign w_is_act = cmd_valid_i && (cmd_op_i == OP_ACT);
    assign w_is_pre = cmd_valid_i && ((cmd_op_i == OP_PRE) || (cmd_op_i == OP_PREA));
    assign w_is_ref = cmd_valid_i && is_refresh_op(cmd_op_i);

    // ---- per-bank idle timers (fixed_open / adapt_time) --------------------
    // A bank's timer arms while its row is open and RELOADS on any command to
    // that bank (column keeps the row "warm", ACT starts fresh). At zero the
    // close request raises and holds until the row actually closes (PRE from
    // any path, or refresh). tr==0 disables that bank's timeout entirely
    // (matches "0 = build default" on the CSR field).
    logic [NUM_BANKS-1:0][7:0] r_tr;        // per-bank timeout register (adapt)
    logic [NUM_BANKS-1:0][7:0] r_idle;      // countdown
    logic [NUM_BANKS-1:0]      r_expired;   // sticky until the row closes

    // Effective TR for a bank: fixed_open always uses tr_init; adapt_time uses
    // the adapting register (global scope mirrors bank 0's register).
    function automatic logic [7:0] f_tr (input int b);
        if (!w_adapt_on)       return tr_init_i;
        else if (policy_scope_i) return r_tr[0];
        else                     return r_tr[b];
    endfunction

    // ---- adapt_time state ---------------------------------------------------
    // Last close cause + row per bank, for the mistake taxonomy.
    logic [NUM_BANKS-1:0]                 r_closed_by_timeout;
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0]  r_last_closed_row;
    logic signed [4:0]                    r_mc;         // mistake counter
    logic [15:0]                          r_check_cnt;

    // The timeout-PRE the arbiter issued THIS cycle (ours vs a conflict PRE):
    // it is ours when the arbiter tagged it (cmd from the timeout branch). The
    // arbiter cannot tell us which branch fired, so we infer: a PRE to a bank
    // whose r_expired is set is a timeout close; any other PRE is a conflict
    // close. (Refresh-drain PREs land on active banks whose timers may also
    // have expired — counting those as timeout closes is harmless: the row
    // was idle-expired either way.)
    logic w_pre_was_timeout;
    assign w_pre_was_timeout = w_is_pre && r_expired[cmd_bank_i];

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_idle              <= '0;
            r_expired           <= '0;
            r_closed_by_timeout <= '0;
            r_last_closed_row   <= '0;
            for (int b = 0; b < NUM_BANKS; b++) r_tr[b] <= 8'h0;
            r_mc                <= '0;
            r_check_cnt         <= 16'h0;
        end else begin
            // TR registers track tr_init whenever adapt mode is off, so
            // entering adapt_time starts from the programmed init point.
            if (!w_adapt_on)
                for (int b = 0; b < NUM_BANKS; b++) r_tr[b] <= tr_init_i;

            for (int b = 0; b < NUM_BANKS; b++) begin
                if (!w_timeout_on || !bank_row_active_i[b]) begin
                    // Row closed (or engine off): clear; remember why it closed.
                    if (r_expired[b] && !bank_row_active_i[b])
                        r_closed_by_timeout[b] <= 1'b1;
                    r_idle[b]    <= '0;
                    r_expired[b] <= r_expired[b] && bank_row_active_i[b];
                end else if (cmd_valid_i && (int'(cmd_bank_i) == b)) begin
                    // Any command to the bank re-warms the row.
                    r_idle[b]    <= f_tr(b);
                    r_expired[b] <= 1'b0;
                    if (cmd_op_i == OP_ACT) r_closed_by_timeout[b] <= 1'b0;
                end else if (r_idle[b] != 0) begin
                    r_idle[b] <= r_idle[b] - 8'h1;
                    if (r_idle[b] == 8'h1 && f_tr(b) != 0)
                        r_expired[b] <= 1'b1;
                end
            end

            // Track the row being closed, for premature-reopen detection. A
            // PRE carries no row field, but the registered open-row image for
            // that bank still holds the row it is closing this cycle.
            if (w_is_pre)
                r_last_closed_row[cmd_bank_i] <= bank_open_row_i[cmd_bank_i];

            // ---- adapt_time mistake counter + periodic TR adjust ----------
            if (w_adapt_on) begin
                // premature close: ACT re-opens the same row a timeout closed.
                if (w_is_act && r_closed_by_timeout[cmd_bank_i]
                             && (cmd_row_i == r_last_closed_row[cmd_bank_i])) begin
                    if (r_mc != 5'sd15) r_mc <= r_mc + 5'sd1;
                end
                // held too long: a conflict PRE on a non-expired open bank.
                else if (w_is_pre && !r_expired[cmd_bank_i]
                                  && bank_row_active_i[cmd_bank_i]) begin
                    if (r_mc != -5'sd16) r_mc <= r_mc - 5'sd1;
                end

                if (check_interval_i != 0) begin
                    if (r_check_cnt >= check_interval_i) begin
                        r_check_cnt <= 16'h0;
                        for (int b = 0; b < NUM_BANKS; b++) begin
                            automatic logic [7:0] tr_n = r_tr[b];
                            if (r_mc > $signed({1'b0, mc_high_thr_i})) begin
                                tr_n = (8'hFF - r_tr[b] < tr_step_i) ? tr_max_i
                                     : r_tr[b] + tr_step_i;
                                if (tr_n > tr_max_i) tr_n = tr_max_i;
                            end else if (r_mc < $signed({1'b0, mc_low_thr_i})) begin
                                tr_n = (r_tr[b] < tr_min_i + tr_step_i) ? tr_min_i
                                     : r_tr[b] - tr_step_i;
                            end
                            r_tr[b] <= tr_n;
                        end
                        r_mc <= $signed({1'b0, mc_init_i});
                    end else begin
                        r_check_cnt <= r_check_cnt + 16'h1;
                    end
                end
            end
        end
    end)

    // ---- background close request ------------------------------------------
    // Lowest-priority: pick the lowest-numbered expired open bank. The arbiter
    // gates on pre_ready/guards; we just name the bank.
    always_comb begin
        timeout_pre_req_o  = 1'b0;
        timeout_pre_bank_o = '0;
        if (w_timeout_on) begin
            for (int b = NUM_BANKS - 1; b >= 0; b--) begin
                if (r_expired[b] && bank_row_active_i[b]) begin
                    timeout_pre_req_o  = 1'b1;
                    timeout_pre_bank_o = BKW'(b);
                end
            end
        end
    end

    // ---- telemetry ----------------------------------------------------------
    // Miss vs empty: a wrong-row (conflict) PRE marks its bank; the next ACT
    // to a marked bank is a MISS, to an unmarked bank an EMPTY. Timeout and
    // refresh closes deliberately do NOT mark: the reopen cost after them is
    // the page-empty class.
    logic [NUM_BANKS-1:0] r_conflict_mark;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_conflict_mark   <= '0;
            stat_page_hit_o   <= 32'h0;
            stat_page_miss_o  <= 32'h0;
            stat_page_empty_o <= 32'h0;
            stat_act_o        <= 32'h0;
            stat_pre_o        <= 32'h0;
            stat_ref_o        <= 32'h0;
        end else begin
            if (w_is_pre && !w_pre_was_timeout)
                r_conflict_mark[cmd_bank_i] <= 1'b1;

            if (w_is_col) stat_page_hit_o <= stat_page_hit_o + 32'h1;
            if (w_is_act) begin
                stat_act_o <= stat_act_o + 32'h1;
                if (r_conflict_mark[cmd_bank_i]) begin
                    stat_page_miss_o <= stat_page_miss_o + 32'h1;
                    r_conflict_mark[cmd_bank_i] <= 1'b0;
                end else begin
                    stat_page_empty_o <= stat_page_empty_o + 32'h1;
                end
            end
            if (w_is_pre) stat_pre_o <= stat_pre_o + 32'h1;
            if (w_is_ref) stat_ref_o <= stat_ref_o + 32'h1;
        end
    end)

endmodule : pumice_page_policy
