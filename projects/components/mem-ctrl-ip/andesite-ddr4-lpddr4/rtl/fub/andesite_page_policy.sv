// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_page_policy
// Purpose: page_policy
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried unchanged from scoria_page_policy per andesite HAS ch02 (INHERITED).
// The only differences from the scoria source are the module name, the
// package import, and this header. Verification evidence transfers with
// scoria's suite (ported, not rewritten).
//
// Author: sean galloway
// Created: 2026-10-04 (carried)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_page_policy
    import andesite_pkg::*;
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
    input  logic [7:0]                 tr_init_i,         // PAGE_TIMEOUT_CFG.tr_init

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
    output logic [31:0]                stat_ref_o,

    // TASK-012. REF_STATS_REF free-runs: refresh is autonomous, so a
    // host-bracketed delta counts every microsecond between two UART reads,
    // not the workload. Measured on the board: a 186 us window carried a raw
    // delta of 61446 -- 479 ms implied, a 2584x overstatement, and near
    // identical across every config because it was timing the HOST.
    //
    // This counts only refreshes that fired WITH WORK PENDING, which is both
    // contamination-free (the CAMs are empty while the host is idle, so those
    // refreshes are not counted) and the number axis 3 actually wants: a
    // refresh during idle costs the workload nothing, one during traffic costs
    // bandwidth. No host arming, no window register, no write trigger -- so
    // nothing here can be fired by RegisterMap.walk().
    input  logic                       demand_i,          // any CAM entry schedulable
    // Per-bank ROW HITS (pumice BUG-020). Free-running like every other stat
    // here, so the host subtracts two reads for a window.
    //
    // A hit is a column op to a bank that did NOT need an activation. This is
    // counted from the issued stream directly rather than derived as
    // `col_ops - ACT`: that derivation is unsound under a background-close mode,
    // because a row can be opened, hit by the timeout precharge before its
    // column command issues, and reopened -- two ACTs, one column op, and a
    // NEGATIVE hit count (pumice ISSUE-014, measured 49 ACTs for 48 column ops).
    output logic [31:0]                stat_row_hit_o [NUM_BANKS],

    output logic [31:0]                stat_ref_busy_o
);

    localparam logic [2:0] MODE_DEFAULT      = 3'd0;
    localparam logic [2:0] MODE_STATIC_OPEN  = 3'd1;
    localparam logic [2:0] MODE_STATIC_CLOSE = 3'd2;
    localparam logic [2:0] MODE_FIXED_OPEN   = 3'd3;
    // 4 (adapt_time) and 5 (adapt_access) RETIRED 2026-09-27, by Sean:
    // "remove the adaptive modes as showing no benefit".
    //
    // Mode 4 was MEASURED to be redundant: moving only tr_min moved the result
    // and it landed exactly on the corresponding fixed point every time
    // (tr_min 2 -> 436.8 MB/s == fixed_open TR=2; 8 -> 338.5 == TR=8; 16 ->
    // 327.7 == TR=16). The mistake counter is dominated by the held-too-long
    // case, so TR decayed monotonically to the floor and stayed there --
    // adapt_time WAS fixed_open(tr_min) wearing another name, and mode 3 is
    // already its close path. Its r_mc was also a single GLOBAL counter driving
    // all eight r_tr[b] from one decision, so policy_scope=0's "per-bank TR"
    // could not diverge and was a fiction.
    //
    // Mode 5 was NOT disproven -- it was unproven and mis-plumbed, and is
    // removed as a DECISION rather than a measurement. It drove close_pred_o
    // into ap_close_o, i.e. auto-precharge, which measured 4.9x the activations
    // of a background precharge on identical traffic (160,006 vs 32,400 ACT)
    // and double the read latency. AP commits at the column op, before it is
    // known whether more requests to that row are coming, so on a controller
    // whose value is FR-FCFS reordering to batch same-row columns it fights the
    // reordering that justifies the design. Even a perfect predictor driving AP
    // is bounded by a mechanism that loses; re-plumbing it onto the background
    // precharge was the alternative and was not taken.
    //
    // 6 (rbl_static) and 7 (rbl_dyn) RETIRED 2026-09-26. Measured on silicon
    // at txn_scale=1000 on a workload built specifically to suit them
    // ([[TASK-011]]): mode 6 lost 26% of bandwidth (195.2 -> 144.2 MB/s) by
    // paying +22,827 ACTs to save precharges that never materialised, and
    // mode 7's hill-climb drove its threshold to "never close early", making
    // it bit-identical to plain open page (32,223 vs 32,224 ACTs). The
    // mechanism demonstrably worked -- thrash% fell 100% -> 57.8% -- and still
    // did not pay. A write to policy_mode 6/7 now falls through to the build
    // default, which is what mode 7 measured as anyway.

    logic w_mode_on, w_timeout_on;
    assign w_mode_on    = (policy_mode_i == MODE_STATIC_OPEN)
                       || (policy_mode_i == MODE_STATIC_CLOSE)
                       || (policy_mode_i == MODE_FIXED_OPEN);
    assign w_timeout_on = (policy_mode_i == MODE_FIXED_OPEN);

    // ---- auto-precharge decision -------------------------------------------
    // ONE producer now: static_close. The predictor path (mode 5) and its
    // scoria_row_pred_table instance are gone with the adaptive modes.
    assign ap_mode_en_o = w_mode_on;
    assign ap_close_o   = (policy_mode_i == MODE_STATIC_CLOSE) ? {NUM_BANKS{1'b1}}
                                                               : '0;



    // ---- issued-stream decodes ---------------------------------------------
    logic w_is_col, w_is_act, w_is_pre, w_is_pre1, w_is_ref;
    assign w_is_col  = cmd_valid_i && is_column_op(cmd_op_i);
    assign w_is_act  = cmd_valid_i && (cmd_op_i == OP_ACT);
    assign w_is_pre  = cmd_valid_i && ((cmd_op_i == OP_PRE) || (cmd_op_i == OP_PREA));
    // SINGLE-bank precharge only. PREA is the refresh drain's all-bank close
    // and its bank field carries nothing -- see the conflict-mark note below.
    assign w_is_pre1 = cmd_valid_i && (cmd_op_i == OP_PRE);
    assign w_is_ref  = cmd_valid_i && is_refresh_op(cmd_op_i);

    // ---- per-bank idle timers (fixed_open / adapt_time) --------------------
    // A bank's timer arms while its row is open and RELOADS on any command to
    // that bank (column keeps the row "warm", ACT starts fresh). At zero the
    // close request raises and holds until the row actually closes (PRE from
    // any path, or refresh). tr==0 disables that bank's timeout entirely
    // (matches "0 = build default" on the CSR field).
    logic [NUM_BANKS-1:0][7:0] r_tr;        // per-bank timeout register (adapt)
    logic [NUM_BANKS-1:0][7:0] r_idle;      // countdown
    logic [NUM_BANKS-1:0]      r_expired;   // sticky until the row closes

    // Effective TR for a bank. With adapt_time retired there is exactly one
    // source: the programmed tr_init. The per-bank r_tr[] registers, the global
    // vs per-bank policy_scope select and the mistake taxonomy that drove them
    // are all gone -- see the mode-retirement note above for why.
    function automatic logic [7:0] f_tr (input int b);
        return tr_init_i;
    endfunction

    // Was this cycle's PRE a TIMEOUT close or a conflict close? Needed by the
    // TELEMETRY below (a timeout close must not mark its bank, so the next ACT
    // classifies as page_empty rather than page_miss), not by any adaptive
    // logic -- it merely used to be declared inside the adapt block, and
    // deleting that block took it with it.
    //
    // The arbiter cannot tell us which branch fired, so we infer: a PRE to a
    // bank whose r_expired is set is a timeout close; any other PRE is a
    // conflict close. Refresh-drain PREs land on active banks whose timers may
    // also have expired -- counting those as timeout closes is harmless, the
    // row was idle-expired either way.
    logic w_pre_was_timeout;
    assign w_pre_was_timeout = w_is_pre && r_expired[cmd_bank_i];

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_idle              <= '0;
            r_expired           <= '0;
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (!w_timeout_on || !bank_row_active_i[b]) begin
                    // Row closed (or engine off): clear.
                    r_idle[b]    <= '0;
                    r_expired[b] <= r_expired[b] && bank_row_active_i[b];
                end else if (cmd_valid_i && (int'(cmd_bank_i) == b)) begin
                    // Any command to the bank re-warms the row.
                    r_idle[b]    <= f_tr(b);
                    r_expired[b] <= 1'b0;
                end else if (r_idle[b] != 0) begin
                    r_idle[b] <= r_idle[b] - 8'h1;
                    if (r_idle[b] == 8'h1 && f_tr(b) != 0)
                        r_expired[b] <= 1'b1;
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
    //
    // Only a SINGLE-bank PRE may mark. The mark used to be driven by w_is_pre,
    // which includes PREA -- the refresh drain's all-bank close, whose bank
    // field is not an address. That made one arbitrary bank's reopen a
    // conflict miss after every drain: measured 1 miss + 7 empties for eight
    // reopens after one PREA, where the class of all eight is page_empty. The
    // count was small but the attribution was wrong, and it was wrong in the
    // direction that makes an open-page policy look worse than it is.
    // (dv/tests/fub/test_scoria_page_policy.py::prea_marks_one_bank_only)
    logic [NUM_BANKS-1:0] r_conflict_mark;
    // An activation issued for bank b that has not yet seen its column op.
    logic [NUM_BANKS-1:0] r_act_pending;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_conflict_mark   <= '0;
            stat_page_hit_o   <= 32'h0;
            stat_page_miss_o  <= 32'h0;
            stat_page_empty_o <= 32'h0;
            stat_act_o        <= 32'h0;
            stat_pre_o        <= 32'h0;
            stat_ref_o        <= 32'h0;
            stat_ref_busy_o   <= 32'h0;
            r_act_pending     <= '0;
            for (int b = 0; b < NUM_BANKS; b++) stat_row_hit_o[b] <= 32'h0;
        end else begin
            if (w_is_pre1 && !w_pre_was_timeout)
                r_conflict_mark[cmd_bank_i] <= 1'b1;

            if (w_is_col) stat_page_hit_o <= stat_page_hit_o + 32'h1;

            // Per-bank row hits. `r_act_pending[b]` means "an activation for
            // bank b is still waiting for the column op it was issued for".
            // Set by any ACT to b; cleared by the first column op to b, which
            // is that activation's own access and therefore NOT a hit. A column
            // op arriving with the flag clear found the row already open.
            //
            // The re-activation case (open -> timeout close -> reopen, with no
            // column op in between) simply sets the flag twice, which is why
            // this counts correctly where col_ops - ACT does not.
            if (w_is_act) r_act_pending[cmd_bank_i] <= 1'b1;
            if (w_is_col) begin
                if (r_act_pending[cmd_bank_i])
                    r_act_pending[cmd_bank_i] <= 1'b0;
                else
                    stat_row_hit_o[cmd_bank_i] <= stat_row_hit_o[cmd_bank_i] + 32'h1;
            end
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
            if (w_is_ref) begin
                stat_ref_o <= stat_ref_o + 32'h1;
                // Sampled at the REF's own issue cycle, so it reflects demand
                // at the moment the refresh took the command slot.
                if (demand_i) stat_ref_busy_o <= stat_ref_busy_o + 32'h1;
            end
        end
    end)

endmodule : andesite_page_policy
