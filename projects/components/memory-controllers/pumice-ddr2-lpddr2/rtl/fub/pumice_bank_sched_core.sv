// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_bank_sched_core
// Purpose: The STAGE-2 (final) scheduler of the two-stage bank-partitioned
//   arbiter (PUMICE_BANK_SCHED). It arbitrates among the NUM_BANKS REGISTERED
//   per-bank candidates from pumice_bank_cmd_picker, applies the GLOBAL timing
//   constraints a single bank cannot see (bus 1/cyc, tRRD, tFAW, tWTR/tRTW
//   turnaround, tCCD), RE-CHECKS each candidate against live per-bank readiness
//   (a flopped candidate can go illegal in one cycle), overlays the
//   refresh / init OVERRIDE at highest priority (ported faithfully from the
//   flat pumice_cmd_arbiter, incl. the PRE-then-REF drain, REFpb rotor bank,
//   tRFC recovery and the double-issue !r_grant guard), registers the decision
//   into the cmd FIFO, and drives the evt / CAM-commit / CAM-issue / grant
//   strobes plus the per-bank issued_o strobe (+ issued_op_o) that advances the
//   winning picker and arms its guards.
//
// This is the production sibling of rtl/proto/pumice_bank_sched_core.sv (the
// depth-measurement scaffold, ~24 mux levels). Because the candidates are
// pre-selected and registered, the cross-bank pick is an 8-way TOURNAMENT TREE
// (clog2(NUM_BANKS) compares), never a serial `if pri>best` accumulator
// (PUMICE-017).
//
// Pipeline: [picker classify+select] -> candidate REG -> [this core: recheck +
// override + register] -> output REG. Two registers, matching the flat
// arbiter's pre-pick + output depth, so the neighbouring timing is unchanged.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_bank_sched_core
    import pumice_pkg::*;
#(
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int COL_WIDTH = 10,
    parameter int BKW       = 3,
    parameter int PTRW      = 3,
    parameter int AGE_WIDTH = 16,
    parameter int RKW       = 1
) (
    input  logic                                aclk,
    input  logic                                aresetn,

    // ---- per-bank registered candidates (from pumice_bank_cmd_picker) ----
    input  logic [NUM_BANKS-1:0]                cand_valid_i,
    input  dram_op_e                            cand_op_i    [NUM_BANKS],
    input  logic [NUM_BANKS-1:0]                cand_ap_i,
    input  logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] cand_row_i,
    input  logic [NUM_BANKS-1:0][COL_WIDTH-1:0] cand_col_i,
    input  logic [NUM_BANKS-1:0][PTRW-1:0]      cand_slot_i,
    input  logic [NUM_BANKS-1:0]                cand_is_rd_i,
    input  logic [NUM_BANKS-1:0][AGE_WIDTH-1:0] cand_pri_i,

    // ---- registered per-bank state (recheck + refresh) ----
    input  logic [NUM_BANKS-1:0]                bank_act_ready_i,
    input  logic [NUM_BANKS-1:0]                bank_rdwr_ready_i,
    input  logic [NUM_BANKS-1:0]                bank_pre_ready_i,
    input  logic [NUM_BANKS-1:0]                bank_row_active_i,

    // ---- global constraints (from global_timers) ----
    input  logic                                tfaw_ok_i,
    input  logic                                trrd_ok_i,
    input  logic                                twtr_ok_i,
    input  logic                                trtw_ok_i,
    input  logic                                tccd_ok_i,

    // ---- init passthrough (from init_sequencer) ----
    input  logic                                init_done_i,
    input  logic                                init_cmd_valid_i,
    input  dram_op_e                            init_cmd_op_i,
    input  logic [BKW-1:0]                       init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]                init_cmd_row_i,

    // ---- refresh (from refresh_ctrl) ----
    input  logic                                refresh_req_i,
    input  logic                                refresh_drain_i,
    input  logic                                refresh_kind_i,   // 0=REFab 1=REFpb
    input  logic [BKW-1:0]                       refresh_bank_i,   // rotor mirror
    input  logic [15:0]                          t_rfc_i,
    input  logic [7:0]                           t_rfc_pb_i,
    output logic                                refresh_grant_o,

    // ---- timeout precharge (pumice_page_policy, lowest priority) ----
    input  logic                                timeout_pre_req_i,
    input  logic [BKW-1:0]                       timeout_pre_bank_i,

    // ---- command push (scheduler -> DFI command FIFO) ----
    input  logic                                cmd_ready_i,
    output logic                                cmd_valid_o,
    output dram_op_e                            cmd_op_o,
    output logic [RKW-1:0]                       cmd_rank_o,
    output logic [BKW-1:0]                       cmd_bank_o,
    output logic [ROW_WIDTH-1:0]                cmd_row_o,
    output logic [COL_WIDTH-1:0]                cmd_col_o,
    output logic                                cmd_ap_o,

    // ---- event strobes to bank + global timers ----
    output logic                                evt_act_o,
    output logic                                evt_rd_o,
    output logic                                evt_wr_o,
    output logic                                evt_pre_o,
    output logic                                evt_ap_o,
    output logic [RKW-1:0]                       evt_rank_o,
    output logic [BKW-1:0]                       evt_bank_o,
    output logic [ROW_WIDTH-1:0]                evt_row_o,

    // ---- CAM commit / issue feedback ----
    output logic                                wr_commit_valid_o,
    output logic [PTRW-1:0]                      wr_commit_slot_o,
    output logic                                rd_issue_valid_o,
    output logic [PTRW-1:0]                      rd_issue_slot_o,

    // ---- picker feedback (winning bank advances + guards arm) ----
    output logic [NUM_BANKS-1:0]                issued_o,
    output dram_op_e                            issued_op_o
);

    localparam int RK0 = 0;   // v1 single-rank pick

    // ---- registered decision (output stage) --------------------------------
    logic                 r_pick_valid;
    dram_op_e             r_op;
    logic [BKW-1:0]       r_bank;
    logic [ROW_WIDTH-1:0] r_row;
    logic [COL_WIDTH-1:0] r_col_out;
    logic                 r_ap_out;
    logic                 r_do_act, r_do_rd, r_do_wr, r_do_pre, r_grant;
    logic                 r_wr_commit, r_rd_issue;
    logic [PTRW-1:0]      r_commit_slot, r_issue_slot;

    logic w_out_ready, w_fire_out;
    assign w_out_ready = !r_pick_valid || cmd_ready_i;
    assign w_fire_out  = r_pick_valid && cmd_ready_i;

    // ---- guards (registered), all driven by this core's own issued command --
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;   // block ACT/PRE re-issue (2 cyc)
    logic [NUM_BANKS-1:0] r_colguard0;          // block THIS BANK's columns (1 cyc)
    logic                 r_rdfire0, r_rdfire1;     // tRTW turnaround history
    logic                 r_wrfire0, r_wrfire1;     // tWTR turnaround history
    logic [15:0]          r_rfc_cnt;

    logic w_inflight_preact, w_inflight_col, w_rfc_busy;
    logic w_rd_turn_block, w_wr_turn_block;
    assign w_inflight_preact = r_pick_valid && (r_do_act || r_do_pre);
    assign w_inflight_col    = r_pick_valid && (r_do_rd  || r_do_wr);
    assign w_rfc_busy        = (r_rfc_cnt != 16'd0);
    assign w_rd_turn_block   = r_wrfire0 || r_wrfire1;   // WR fired < 2 cyc ago
    assign w_wr_turn_block   = r_rdfire0 || r_rdfire1;   // RD fired < 2 cyc ago

    // Bank guard: 2-cycle re-issue block + the in-flight (held/draining) bank.
    logic [NUM_BANKS-1:0] w_guarded;
    always_comb begin
        w_guarded = r_guard0 | r_guard1;
        if (w_inflight_preact || w_inflight_col)
            w_guarded |= (NUM_BANKS'(1) << r_bank);
    end

    // Per-bank COLUMN guard: block ONLY the just-fired column's own bank, for
    // the two cycles that bridge the candidate-reg + output-reg latency until
    // the CAM retires the slot -- w_inflight_col (the held/draining column's
    // bank) then r_colguard0 (one flop). This is the exact contract the flat
    // arbiter's 1-cycle w_inflight_col relied on (1-cycle CAM retire), so a
    // static single-bank column stream re-issues every other cycle just as the
    // flat path does. Per-bank (not a global stall) leaves OTHER banks free; a
    // deeper block would re-shape the pick cadence.
    logic [NUM_BANKS-1:0] w_col_guarded;
    always_comb begin
        w_col_guarded = r_colguard0;
        if (w_inflight_col) w_col_guarded |= (NUM_BANKS'(1) << r_bank);
    end

    // ---- re-check each registered candidate against live readiness + global -
    logic [NUM_BANKS-1:0] w_elig;
    always_comb begin
        w_elig = '0;
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic logic is_col = is_column_op(cand_op_i[b]);
            automatic logic is_act = (cand_op_i[b] == OP_ACT);
            automatic logic is_pre = (cand_op_i[b] == OP_PRE);
            automatic logic okc = is_col && bank_rdwr_ready_i[b] && tccd_ok_i
                                  && !w_col_guarded[b]
                                  && (cand_is_rd_i[b] ? (twtr_ok_i && !w_rd_turn_block)
                                                      : (trtw_ok_i && !w_wr_turn_block));
            automatic logic oka = is_act && bank_act_ready_i[b] && tfaw_ok_i && trrd_ok_i
                                  && !w_rfc_busy && !w_guarded[b];
            automatic logic okp = is_pre && bank_pre_ready_i[b] && !w_guarded[b];
            w_elig[b] = cand_valid_i[b] && (okc || oka || okp);
        end
    end

    // ---- 8-way pick among eligible candidates: oldest priority wins --------
    // Balanced TOURNAMENT TREE (clog2(NUM_BANKS) compares), NOT the serial
    // `for b: if elig && pri>best` accumulator (PUMICE-017). Prefer-left on ties.
    localparam int LV = $clog2(NUM_BANKS);
    logic                 tv [LV+1][NUM_BANKS];
    logic [AGE_WIDTH-1:0] tp [LV+1][NUM_BANKS];
    logic [BKW-1:0]       tb [LV+1][NUM_BANKS];
    logic                 sel_valid;
    logic [BKW-1:0]       sel_bank;
    logic [AGE_WIDTH-1:0] best_pri;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            tv[0][b] = w_elig[b];
            tp[0][b] = cand_pri_i[b];
            tb[0][b] = BKW'(b);
        end
        for (int l = 1; l <= LV; l++) begin
            for (int i = 0; i < (NUM_BANKS >> l); i++) begin
                automatic logic av = tv[l-1][2*i];
                automatic logic bv = tv[l-1][2*i+1];
                // right child wins only if left invalid, or right valid + strictly
                // higher priority (prefer-left on ties/none)
                automatic logic pick_r = (!av) || (bv && (tp[l-1][2*i+1] > tp[l-1][2*i]));
                tv[l][i] = av || bv;
                tp[l][i] = pick_r ? tp[l-1][2*i+1] : tp[l-1][2*i];
                tb[l][i] = pick_r ? tb[l-1][2*i+1] : tb[l-1][2*i];
            end
        end
        sel_valid = tv[LV][0];
        best_pri  = tp[LV][0];
        sel_bank  = tb[LV][0];
    end
    // best_pri is diagnostic only (the winner is named by sel_bank).
    wire _unused_best_pri = &{1'b0, best_pri};

    // ---- refresh: pick the lowest active bank that can precharge -----------
    logic           w_any_active, w_rfsh_pre_found, w_ref_safe, w_refpb_safe;
    logic [BKW-1:0] w_rfsh_pre_bank;
    always_comb begin
        w_any_active     = |bank_row_active_i;
        w_rfsh_pre_found = 1'b0;
        w_rfsh_pre_bank  = '0;
        for (int j = NUM_BANKS-1; j >= 0; j--)
            if (bank_row_active_i[j] && bank_pre_ready_i[j] && !w_guarded[j]) begin
                w_rfsh_pre_found = 1'b1;
                w_rfsh_pre_bank  = BKW'(j);
            end
    end
    // REF may fire only when NO bank can possibly have a row open, nothing
    // row-affecting is in flight / inside its guard window, tRFC elapsed, and no
    // grant is already in the output register (!r_grant stops the double-issue).
    assign w_ref_safe   = !w_any_active && !w_inflight_preact
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant;
    // REFpb: only the rotor bank must be closed; inflight/guard/rfc stay global.
    assign w_refpb_safe = !bank_row_active_i[refresh_bank_i] && !w_inflight_preact
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant;

    // ========================================================================
    // Priority pick (combinational): init > refresh > demand tournament >
    // timeout-PRE. Produces the abstract command + side-effect strobes.
    // ========================================================================
    dram_op_e             w_op;
    logic [BKW-1:0]       w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;
    logic                 w_ap_out, w_valid;
    logic                 w_do_act, w_do_rd, w_do_wr, w_do_pre, w_grant;
    logic                 w_wr_commit, w_rd_issue;
    logic [PTRW-1:0]      w_commit_slot, w_issue_slot;

    always_comb begin
        w_op = OP_NOP; w_bank = '0; w_row = '0; w_col = '0; w_ap_out = 1'b0;
        w_valid = 1'b0;
        w_do_act = 1'b0; w_do_rd = 1'b0; w_do_wr = 1'b0; w_do_pre = 1'b0; w_grant = 1'b0;
        w_wr_commit = 1'b0; w_rd_issue = 1'b0; w_commit_slot = '0; w_issue_slot = '0;

        if (!init_done_i) begin
            // 1. INIT -- forward the sequencer command verbatim.
            if (init_cmd_valid_i) begin
                w_valid = 1'b1; w_op = init_cmd_op_i;
                w_bank = init_cmd_bank_i; w_row = init_cmd_row_i;
            end
        end else if (refresh_req_i || refresh_drain_i) begin
            // 2. REFRESH -- precharge active banks first, then REF + grant.
            if (refresh_kind_i) begin
                // 2b. REFpb -- close ONLY the device's rotor bank.
                if (bank_row_active_i[refresh_bank_i]) begin
                    if (bank_pre_ready_i[refresh_bank_i] && !w_guarded[refresh_bank_i]) begin
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
        end else if (sel_valid) begin
            // 3. DEMAND -- the tournament winner (read-priority + oldest are
            // already resolved inside the picker; class order too).
            w_valid  = 1'b1;
            w_op     = cand_op_i[sel_bank];
            w_bank   = sel_bank;
            w_row    = cand_row_i[sel_bank];
            w_col    = cand_col_i[sel_bank];
            w_ap_out = cand_ap_i[sel_bank];
            if (is_read_op(cand_op_i[sel_bank])) begin
                w_do_rd = 1'b1; w_rd_issue = 1'b1; w_issue_slot = cand_slot_i[sel_bank];
            end else if (is_write_op(cand_op_i[sel_bank])) begin
                w_do_wr = 1'b1; w_wr_commit = 1'b1; w_commit_slot = cand_slot_i[sel_bank];
            end else if (cand_op_i[sel_bank] == OP_ACT) begin
                w_do_act = 1'b1;
            end else begin
                w_do_pre = 1'b1;   // OP_PRE
            end
        end else if (timeout_pre_req_i
                     && bank_row_active_i[timeout_pre_bank_i]
                     && bank_pre_ready_i[timeout_pre_bank_i]
                     && !w_guarded[timeout_pre_bank_i]) begin
            // 4. TIMEOUT PRECHARGE -- strictly lowest priority.
            w_valid = 1'b1; w_op = OP_PRE; w_bank = timeout_pre_bank_i;
            w_do_pre = 1'b1;
        end
    end

    // ---- output register: capture the pick, drain to the cmd FIFO ----------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pick_valid <= 1'b0;
            r_op         <= OP_NOP;
            r_bank       <= '0; r_row <= '0; r_col_out <= '0; r_ap_out <= 1'b0;
            r_do_act <= 1'b0; r_do_rd <= 1'b0; r_do_wr <= 1'b0; r_do_pre <= 1'b0;
            r_grant  <= 1'b0; r_wr_commit <= 1'b0; r_rd_issue <= 1'b0;
            r_commit_slot <= '0; r_issue_slot <= '0;
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
            r_wr_commit   <= w_wr_commit;
            r_commit_slot <= w_commit_slot;
            r_rd_issue    <= w_rd_issue;
            r_issue_slot  <= w_issue_slot;
        end
    )

    // ---- command push outputs (from the registered decision) ----
    assign cmd_valid_o = r_pick_valid;
    assign cmd_op_o    = r_op;
    assign cmd_rank_o  = RKW'(RK0);
    assign cmd_bank_o  = r_bank;
    assign cmd_row_o   = r_row;
    assign cmd_col_o   = r_col_out;
    assign cmd_ap_o    = r_ap_out;

    // ---- event strobes (fire when the registered command is accepted) ----
    assign evt_act_o  = w_fire_out && r_do_act;
    assign evt_rd_o   = w_fire_out && r_do_rd;
    assign evt_wr_o   = w_fire_out && r_do_wr;
    assign evt_pre_o  = w_fire_out && r_do_pre;
    assign evt_ap_o   = r_ap_out;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = r_bank;
    assign evt_row_o  = r_row;

    // ---- CAM commit / issue / refresh grant (on accepted issue) ----
    assign wr_commit_valid_o = w_fire_out && r_wr_commit;
    assign wr_commit_slot_o  = r_commit_slot;
    assign rd_issue_valid_o  = w_fire_out && r_rd_issue;
    assign rd_issue_slot_o   = r_issue_slot;
    assign refresh_grant_o   = w_fire_out && r_grant;

    // ---- picker feedback: advance the winning bank + broadcast the fired op -
    // Pulses for demand picks AND refresh PREs (any op that names a bank);
    // REF/REFpb-grant and init carry no bank -> no pulse.
    always_comb begin
        issued_o = '0;
        if (w_fire_out && (r_do_act || r_do_rd || r_do_wr || r_do_pre))
            issued_o[r_bank] = 1'b1;
    end
    assign issued_op_o = r_op;

    // ---- guard update -----------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0 <= '0; r_guard1 <= '0;
            r_colguard0 <= '0;
            r_wrfire0 <= 1'b0; r_wrfire1 <= 1'b0;
            r_rdfire0 <= 1'b0; r_rdfire1 <= 1'b0;
        end else begin
            r_guard1 <= r_guard0;
            r_guard0 <= '0;
            if (w_fire_out && (r_do_act || r_do_pre || r_do_rd || r_do_wr))
                r_guard0 <= (NUM_BANKS'(1) << r_bank);
            // per-bank column guard: one flop after this bank fires a column
            // (w_inflight_col covers the fire cycle; this covers the next, until
            // the CAM's 1-cycle retire drops the slot).
            r_colguard0 <= '0;
            if (w_fire_out && (r_do_rd || r_do_wr))
                r_colguard0 <= (NUM_BANKS'(1) << r_bank);
            // direction-turnaround history (see w_rd/wr_turn_block).
            r_wrfire1 <= r_wrfire0;
            r_wrfire0 <= w_fire_out && r_do_wr;
            r_rdfire1 <= r_rdfire0;
            r_rdfire0 <= w_fire_out && r_do_rd;
        end
    )

    // ---- tRFC recovery counter: load on a FIRED REF, count down to 0 -------
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

endmodule : pumice_bank_sched_core
