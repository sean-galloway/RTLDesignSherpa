// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_bank_sched_core
// Purpose: The STAGE-2 (final) scheduler of the two-stage bank-partitioned
//   arbiter (PUMICE_BANK_SCHED). It arbitrates among the NUM_BANKS REGISTERED
//   per-bank candidates from pumice_bank_cmd_picker and drives one DRAM command,
//   the evt / CAM-commit / CAM-issue / grant strobes, and the per-bank issued_o
//   (+ issued_op_o) feedback that advances the winning picker and arms its
//   guards.
//
// TWO INTERNAL PIPELINE STAGES (keeps each cone shallow):
//   STAGE A -- the balanced NUM_BANKS-way TOURNAMENT over the candidate keys,
//     eligibility-rechecked against live per-bank readiness + the global
//     constraints (tRRD/tFAW/tCCD/tWTR/tRTW turnaround) + the guards, then FLOP
//     the single winner {valid, op, bank, row, col, slot, is_rd, ap}.
//   STAGE B -- a LIVE re-check of that flopped winner (it can go illegal in the
//     extra cycle), the refresh / init OVERRIDE at highest priority (PRE-then-REF
//     drain, REFpb rotor bank, tRFC recovery, the !r_grant double-issue guard),
//     the timeout-PRE, then the output register + all strobes.
//
// This costs +1 issue-latency vs a single-stage core. The issued_o -> picker
// feedback therefore returns one cycle later, and the DOUBLE-ISSUE guard spans
// BOTH pipeline registers: a bank in flight in stage A (r_a) OR stage B (r_pick)
// is excluded from the stage-A tournament, and the picker's per-bank guards were
// deepened by one to match (see pumice_bank_cmd_picker).
//
// Depth discipline: the cross-bank pick is a balanced TOURNAMENT TREE
// (clog2(NUM_BANKS) key compares), and the refresh precharge target is a
// lowest-set isolate + reduce, never a serial `if pri>best` / priority scan
// (PUMICE-017).
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
    parameter int KEYW      = 15,
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
    input  logic [NUM_BANKS-1:0][KEYW-1:0]      cand_pri_i,

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
    // Column commit / issue FIFO room -- the pickers gate classification on
    // these, but the winner is registered for 2 more stages before it issues,
    // and the FIFO can fill in that window (esp. under the faster live-picker
    // demand). Re-check them here so a column commit is never launched into a
    // full drain / issue FIFO (that desyncs the wr CAM -> write channel wedge).
    input  logic                                wr_commit_ready_i,
    input  logic                                rd_issue_ready_i,

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
    localparam int LV  = $clog2(NUM_BANKS);

    // ---- STAGE A registered winner ----------------------------------------
    logic                 r_a_valid, r_a_is_rd, r_a_ap;
    dram_op_e             r_a_op;
    logic [BKW-1:0]       r_a_bank;
    logic [ROW_WIDTH-1:0] r_a_row;
    logic [COL_WIDTH-1:0] r_a_col;
    logic [PTRW-1:0]      r_a_slot;

    // ---- STAGE B registered decision (output stage) -----------------------
    logic                 r_pick_valid;
    dram_op_e             r_op;
    logic [BKW-1:0]       r_bank;
    logic [ROW_WIDTH-1:0] r_row;
    logic [COL_WIDTH-1:0] r_col_out;
    logic                 r_ap_out;
    logic                 r_do_act, r_do_rd, r_do_wr, r_do_pre, r_grant;
    logic                 r_wr_commit, r_rd_issue;
    logic [PTRW-1:0]      r_commit_slot, r_issue_slot;

    // ---- guards (registered), driven by the STAGE B fire ------------------
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;   // block ACT/PRE re-issue
    logic [NUM_BANKS-1:0] r_colguard0;          // block a bank's columns 1 cyc
    logic                 r_rdfire0, r_rdfire1; // tRTW turnaround history
    logic                 r_wrfire0, r_wrfire1; // tWTR turnaround history
    logic [15:0]          r_rfc_cnt;

    // ---- flow control ------------------------------------------------------
    logic w_out_ready, w_fire_out, w_a_ready;
    assign w_out_ready = !r_pick_valid || cmd_ready_i;    // stage B can accept
    assign w_fire_out  = r_pick_valid && cmd_ready_i;     // stage B issues
    assign w_a_ready   = !r_a_valid || w_out_ready;       // stage A can push to B

    // ---- inflight + guard views -------------------------------------------
    logic w_infl_a_pre, w_infl_a_col, w_infl_b_pre, w_infl_b_col, w_rfc_busy;
    assign w_infl_a_pre = r_a_valid && ((r_a_op == OP_ACT) || (r_a_op == OP_PRE));
    assign w_infl_a_col = r_a_valid && is_column_op(r_a_op);
    assign w_infl_b_pre = r_pick_valid && (r_do_act || r_do_pre);
    assign w_infl_b_col = r_pick_valid && (r_do_rd  || r_do_wr);
    assign w_rfc_busy   = (r_rfc_cnt != 16'd0);

    // ---- direction turnaround (tRTW rd->wr, tWTR wr->rd) -------------------
    // 2-deep FIRE history covers the POST-fire window; an OPPOSITE-direction
    // column still IN FLIGHT in a pipeline register (r_a / r_pick) also blocks,
    // else it would issue before the fire reaches the history (the opt-2 two-
    // stage tRTW/tWTR hole). Write-only streams are unaffected (no RD to block a
    // WR); same-direction (tCCD) spacing stays with tccd_ok + w_cg so the close-
    // page WRA rotation is not over-serialised. _a = stage-A tournament, _b =
    // stage-B recheck of r_a (must NOT count r_a itself).
    logic w_rd_infl_b, w_rd_infl_a, w_wr_infl_b, w_wr_infl_a;
    assign w_rd_infl_b = r_pick_valid && r_do_rd;
    assign w_rd_infl_a = w_rd_infl_b || (r_a_valid && is_read_op(r_a_op));
    assign w_wr_infl_b = r_pick_valid && r_do_wr;
    assign w_wr_infl_a = w_wr_infl_b || (r_a_valid && is_write_op(r_a_op));
    logic w_rd_turn_block_a, w_wr_turn_block_a, w_rd_turn_block_b, w_wr_turn_block_b;
    assign w_rd_turn_block_a = r_wrfire0 || r_wrfire1 || w_wr_infl_a;
    assign w_wr_turn_block_a = r_rdfire0 || r_rdfire1 || w_rd_infl_a;
    assign w_rd_turn_block_b = r_wrfire0 || r_wrfire1 || w_wr_infl_b;
    assign w_wr_turn_block_b = r_rdfire0 || r_rdfire1 || w_rd_infl_b;

    // ACT/PRE re-issue guard. _b (stage-B recheck / refresh) covers r_pick +
    // the post-issue shift; _a (stage-A tournament) adds r_a so a bank already
    // in EITHER pipeline register is excluded -- the two-stage double-issue net.
    logic [NUM_BANKS-1:0] w_g_b, w_g_a, w_cg_b, w_cg_a;
    always_comb begin
        w_g_b  = r_guard0 | r_guard1;
        if (w_infl_b_pre || w_infl_b_col) w_g_b |= (NUM_BANKS'(1) << r_bank);
        w_g_a  = w_g_b;
        if (w_infl_a_pre || w_infl_a_col) w_g_a |= (NUM_BANKS'(1) << r_a_bank);
        w_cg_b = r_colguard0;
        if (w_infl_b_col) w_cg_b |= (NUM_BANKS'(1) << r_bank);
        w_cg_a = w_cg_b;
        if (w_infl_a_col) w_cg_a |= (NUM_BANKS'(1) << r_a_bank);
    end

    // ========================================================================
    // STAGE A: eligibility re-check + balanced max-key tournament.
    // ========================================================================
    logic [NUM_BANKS-1:0] w_elig;
    always_comb begin
        w_elig = '0;
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic logic is_col = is_column_op(cand_op_i[b]);
            automatic logic is_act = (cand_op_i[b] == OP_ACT);
            automatic logic is_pre = (cand_op_i[b] == OP_PRE);
            automatic logic okc = is_col && bank_rdwr_ready_i[b] && tccd_ok_i && !w_cg_a[b]
                                  && (cand_is_rd_i[b]
                                      ? (rd_issue_ready_i && twtr_ok_i && !w_rd_turn_block_a)
                                      : (wr_commit_ready_i && trtw_ok_i && !w_wr_turn_block_a));
            automatic logic oka = is_act && bank_act_ready_i[b] && tfaw_ok_i && trrd_ok_i
                                  && !w_rfc_busy && !w_g_a[b];
            automatic logic okp = is_pre && bank_pre_ready_i[b] && !w_g_a[b];
            w_elig[b] = cand_valid_i[b] && (okc || oka || okp);
        end
    end

    // Balanced tournament tree: max cand_pri among eligible; prefer-left on ties.
    logic [KEYW:0] tk [LV+1][NUM_BANKS];   // {valid, key}
    logic [BKW-1:0] tb [LV+1][NUM_BANKS];
    logic           sel_valid;
    logic [BKW-1:0] sel_bank;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            tk[0][b] = {w_elig[b], cand_pri_i[b]};   // invalid -> MSB 0 -> loses
            tb[0][b] = BKW'(b);
        end
        for (int l = 1; l <= LV; l++) begin
            for (int i = 0; i < (NUM_BANKS >> l); i++) begin
                automatic logic pick_r = tk[l-1][2*i+1] > tk[l-1][2*i];
                tk[l][i] = pick_r ? tk[l-1][2*i+1] : tk[l-1][2*i];
                tb[l][i] = pick_r ? tb[l-1][2*i+1] : tb[l-1][2*i];
            end
        end
        sel_valid = tk[LV][0][KEYW];   // winner's validity bit
        sel_bank  = tb[LV][0];
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_a_valid <= 1'b0; r_a_op <= OP_NOP; r_a_bank <= '0; r_a_row <= '0;
            r_a_col <= '0; r_a_slot <= '0; r_a_is_rd <= 1'b1; r_a_ap <= 1'b0;
        end else if (w_a_ready) begin
            // Do NOT hold a demand candidate valid while a refresh owns the
            // pipe. A held demand ACT/PRE would assert w_infl_a_pre and poison
            // w_ref_safe, so the refresh could never reach its REF -- and the
            // held ACT could never issue (w_sel_dem is gated off during
            // refresh), a permanent deadlock. Demand is re-picked (one cycle)
            // once the refresh clears. Matches the flat arbiter, which never
            // carries a registered demand pick across a refresh.
            r_a_valid <= sel_valid && !(refresh_req_i || refresh_drain_i);
            r_a_op    <= cand_op_i[sel_bank];
            r_a_bank  <= sel_bank;
            r_a_row   <= cand_row_i[sel_bank];
            r_a_col   <= cand_col_i[sel_bank];
            r_a_slot  <= cand_slot_i[sel_bank];
            r_a_is_rd <= cand_is_rd_i[sel_bank];
            r_a_ap    <= cand_ap_i[sel_bank];
        end
    )

    // ========================================================================
    // STAGE B: live re-check of r_a + refresh/init override + timeout-PRE.
    // ========================================================================
    // live re-check: the flopped winner may have gone illegal in the extra cycle
    logic w_b_ok;
    always_comb begin
        automatic logic is_col = is_column_op(r_a_op);
        automatic logic is_act = (r_a_op == OP_ACT);
        automatic logic okc = is_col && bank_rdwr_ready_i[r_a_bank] && tccd_ok_i
                              && !w_cg_b[r_a_bank]
                              && (r_a_is_rd
                                  ? (rd_issue_ready_i && twtr_ok_i && !w_rd_turn_block_b)
                                  : (wr_commit_ready_i && trtw_ok_i && !w_wr_turn_block_b));
        automatic logic oka = is_act && bank_act_ready_i[r_a_bank] && tfaw_ok_i && trrd_ok_i
                              && !w_rfc_busy && !w_g_b[r_a_bank];
        automatic logic okp = (r_a_op == OP_PRE) && bank_pre_ready_i[r_a_bank] && !w_g_b[r_a_bank];
        w_b_ok = r_a_valid && (okc || oka || okp);
    end

    // refresh: lowest active bank that can precharge (isolate-lowest + reduce,
    // not a serial priority scan).
    logic [NUM_BANKS-1:0] w_rfsh_elig, w_rfsh_low;
    logic                 w_any_active, w_rfsh_pre_found, w_ref_safe, w_refpb_safe;
    logic [BKW-1:0]       w_rfsh_pre_bank;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_rfsh_elig[b] = bank_row_active_i[b] && bank_pre_ready_i[b] && !w_g_b[b];
        w_rfsh_low       = w_rfsh_elig & (~w_rfsh_elig + NUM_BANKS'(1));  // lowest set
        w_rfsh_pre_found = |w_rfsh_elig;
        w_any_active     = |bank_row_active_i;
        w_rfsh_pre_bank  = '0;
        for (int p = 0; p < BKW; p++) begin
            automatic logic [NUM_BANKS-1:0] pm;
            for (int b = 0; b < NUM_BANKS; b++) pm[b] = w_rfsh_low[b] && b[p];
            w_rfsh_pre_bank[p] = |pm;
        end
    end
    assign w_ref_safe   = !w_any_active && !w_infl_a_pre && !w_infl_b_pre
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant;
    assign w_refpb_safe = !bank_row_active_i[refresh_bank_i]
                        && !w_infl_a_pre && !w_infl_b_pre
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant;

    // Refresh sub-decision, in its OWN small block (PRE active banks first, then
    // REF + grant; REFpb rotor variant). Kept nested here where the depth is
    // bounded, so the TOP-LEVEL priority below is a FLAT parallel select rather
    // than a deep procmux chain (that nested if-else was the 19-mux cone).
    logic     w_ref_valid, w_ref_do_pre, w_ref_grant;
    dram_op_e w_ref_op;
    logic [BKW-1:0] w_ref_bank;
    always_comb begin
        w_ref_valid = 1'b0; w_ref_do_pre = 1'b0; w_ref_grant = 1'b0;
        w_ref_op = OP_NOP; w_ref_bank = '0;
        if (refresh_kind_i) begin
            if (bank_row_active_i[refresh_bank_i]) begin
                if (bank_pre_ready_i[refresh_bank_i] && !w_g_b[refresh_bank_i]) begin
                    w_ref_valid = 1'b1; w_ref_op = OP_PRE;
                    w_ref_bank = refresh_bank_i; w_ref_do_pre = 1'b1;
                end
            end else if (w_refpb_safe) begin
                w_ref_valid = 1'b1; w_ref_op = OP_REFPB;
                w_ref_bank = refresh_bank_i; w_ref_grant = 1'b1;
            end
        end else if (w_any_active) begin
            if (w_rfsh_pre_found) begin
                w_ref_valid = 1'b1; w_ref_op = OP_PRE;
                w_ref_bank = w_rfsh_pre_bank; w_ref_do_pre = 1'b1;
            end
        end else if (w_ref_safe) begin
            w_ref_valid = 1'b1; w_ref_op = OP_REF; w_ref_grant = 1'b1;
        end
    end

    // Timeout-PRE legality (lowest priority).
    logic w_to_ok;
    assign w_to_ok = timeout_pre_req_i
                   && bank_row_active_i[timeout_pre_bank_i]
                   && bank_pre_ready_i[timeout_pre_bank_i]
                   && !w_g_b[timeout_pre_bank_i];

    // ---- FLAT branch selects (priority folded into the conditions) ---------
    // init > refresh > demand > timeout. Demand/timeout are suppressed whenever
    // a refresh is requested (matches the flat else-if fall-through: the refresh
    // branch owns the cycle even when it emits nothing).
    logic w_refresh_active, w_sel_init, w_sel_ref, w_sel_dem, w_sel_to;
    assign w_refresh_active = refresh_req_i || refresh_drain_i;
    assign w_sel_init = !init_done_i && init_cmd_valid_i;
    assign w_sel_ref  = init_done_i && w_refresh_active && w_ref_valid;
    assign w_sel_dem  = init_done_i && !w_refresh_active && w_b_ok;
    assign w_sel_to   = init_done_i && !w_refresh_active && !w_b_ok && w_to_ok;

    dram_op_e             w_op;
    logic [BKW-1:0]       w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;
    logic                 w_ap_out, w_valid;
    logic                 w_do_act, w_do_rd, w_do_wr, w_do_pre, w_grant;
    logic                 w_wr_commit, w_rd_issue;
    logic [PTRW-1:0]      w_commit_slot, w_issue_slot;
    logic                 w_dem_rd, w_dem_wr;
    assign w_dem_rd = w_sel_dem && is_read_op(r_a_op);
    assign w_dem_wr = w_sel_dem && is_write_op(r_a_op);
    assign w_valid   = w_sel_init || w_sel_ref || w_sel_dem || w_sel_to;
    assign w_do_rd   = w_dem_rd;
    assign w_do_wr   = w_dem_wr;
    assign w_do_act  = w_sel_dem && (r_a_op == OP_ACT);
    assign w_do_pre  = (w_sel_dem && (r_a_op == OP_PRE))
                     || (w_sel_ref && w_ref_do_pre) || w_sel_to;
    assign w_grant   = w_sel_ref && w_ref_grant;
    assign w_rd_issue  = w_dem_rd;
    assign w_wr_commit = w_dem_wr;
    assign w_issue_slot  = r_a_slot;
    assign w_commit_slot = r_a_slot;
    assign w_ap_out  = w_sel_dem && r_a_ap;
    // one flat select per wide field (idle default = NOP / bank 0, as the flat
    // path did -- consumers gate on cmd_valid, but keeping op==NOP when idle also
    // avoids a stale OP_PRE lingering in the registered cmd_op).
    assign w_op   = w_sel_init ? init_cmd_op_i
                  : w_sel_ref  ? w_ref_op
                  : w_sel_dem  ? r_a_op
                  : w_sel_to   ? OP_PRE : OP_NOP;
    assign w_bank = w_sel_init ? init_cmd_bank_i
                  : w_sel_ref  ? w_ref_bank
                  : w_sel_dem  ? r_a_bank
                  : w_sel_to   ? timeout_pre_bank_i : '0;
    assign w_row  = w_sel_init ? init_cmd_row_i : (w_sel_dem ? r_a_row : '0);
    assign w_col  = w_sel_dem ? r_a_col : '0;

    // ---- output register ---------------------------------------------------
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
    always_comb begin
        issued_o = '0;
        if (w_fire_out && (r_do_act || r_do_rd || r_do_wr || r_do_pre))
            issued_o[r_bank] = 1'b1;
    end
    assign issued_op_o = r_op;

    // ---- guard update (on STAGE B fire) -----------------------------------
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
            r_colguard0 <= '0;
            if (w_fire_out && (r_do_rd || r_do_wr))
                r_colguard0 <= (NUM_BANKS'(1) << r_bank);
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
