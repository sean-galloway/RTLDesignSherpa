// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_bank_cmd_picker
// Purpose: Per-bank command selection, ONE instance per DRAM bank, the STAGE-1
//   half of the two-stage bank-partitioned scheduler (PUMICE_BANK_SCHED). For a
//   FIXED bank it classifies only THIS bank's rd + wr CAM entries into
//   column / activate / precharge against this bank's (registered) open-row
//   image + per-bank readiness, picks the bank's single best legal command,
//   and REGISTERS it as this bank's candidate. pumice_bank_sched_core then
//   arbitrates the NUM_BANKS registered candidates -- an 8-way pick, not the
//   old cross-bank associative cone.
//
// This is the production sibling of rtl/proto/pumice_bank_cmd_picker.sv
// (the depth-measurement scaffold, ~19 mux levels). Differences from the
// scaffold: real pumice_pkg dram_op_e / page_policy_e, per-bank AUTO-PRECHARGE
// (RDA/WRA) decode, a real relative-age priority (from the CAM's older matrix,
// not the slot proxy), and the PER-BANK guards that the flat arbiter carried at
// bank scope and that fixed real data-corruption bugs:
//   - same-bank ACT/PRE re-issue guard (r_guard0/1): the bank timers register
//     their readiness (2-cycle latency from an evt), so re-classifying ACT/PRE
//     to a bank we just issued to would double-issue before the timers reflect
//     it. Column ops self-limit (the CAM retires the slot on issue/commit).
//   - PRE-column staleness guard (r_preguard0/1/2): a column picked within 3
//     cycles of a PRE on this bank lands on the just-closed row (registered row
//     image is stale end-to-end). 3-deep, matching the flat arbiter.
//   - AP-column guard (r_apguard0/1): under CLOSE an RDA/WRA precharges the
//     bank as part of the access, so the next access must re-ACTivate; block
//     this bank's columns for 2 cycles after a fired auto-precharge column.
//   - rd_issue_ready / wr_commit_ready: a column may only fire when the CAM's
//     issue / drain FIFO has room, else the command issues but the CAM drops it.
//
// The GLOBAL constraints (tCCD, tRRD, tFAW, tWTR/tRTW turnaround, refresh/init
// override, the cross-bank tCCD/turnaround re-check) live in the final stage
// (pumice_bank_sched_core), which a single bank cannot see. Feedback: issued_i
// (this bank's command was accepted) + issued_op_i (what the core actually
// fired, so the guards latch on the true issued op even under backpressure).
//
// Depth-critical coding rules (why this cone stays shallow -- do NOT reintroduce
// the deep chains): reductions use $reduce operators (&terms, |mask), field
// extraction is a single variable part-select v[slot*W +: W] (log depth), and
// the winner select resolves class/direction on 1-bit FOUND flags then extracts
// the wide fields ONCE. No `for j: if(c) x=0` accumulator chains (PUMICE-017).
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_bank_cmd_picker
    import pumice_pkg::*;
#(
    parameter int BANK_ID     = 0,
    parameter int NUM_ENTRIES = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int BKW         = 3,
    parameter int PTRW        = 3,
    parameter int AGE_WIDTH   = 16
) (
    input  logic                               aclk,
    input  logic                               aresetn,

    // ---- policy (per-bank auto-precharge decode) ----
    input  page_policy_e                       page_policy_i,
    input  logic                               ap_mode_en_i,
    input  logic                               ap_close_bit_i,   // this bank's ap_close
    input  logic                               read_pref_i,      // 1 = read-priority

    // ---- this bank's registered live state (from pumice_bank_timers) ----
    input  logic                               bank_act_ready_i,
    input  logic                               bank_rdwr_ready_i,
    input  logic                               bank_pre_ready_i,
    input  logic                               bank_row_active_i,
    input  logic [ROW_WIDTH-1:0]               bank_open_row_i,

    // ---- rd CAM per-entry vectors (registered, whole CAM) + issue-FIFO room -
    input  logic [NUM_ENTRIES-1:0]             rd_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]         rd_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]   rd_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]   rd_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] rd_older_i,
    input  logic                               rd_issue_ready_i,

    // ---- wr CAM per-entry vectors (registered, whole CAM) + drain-FIFO room -
    input  logic [NUM_ENTRIES-1:0]             wr_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]         wr_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]   wr_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]   wr_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] wr_older_i,
    input  logic                               wr_commit_ready_i,

    // ---- final-scheduler feedback ----
    input  logic                               issued_i,     // my candidate accepted
    input  dram_op_e                           issued_op_i,  // the op the core fired

    // ---- registered candidate out ----
    output logic                               cand_valid_o,
    output dram_op_e                           cand_op_o,
    output logic                               cand_ap_o,
    output logic [ROW_WIDTH-1:0]               cand_row_o,
    output logic [COL_WIDTH-1:0]               cand_col_o,
    output logic [PTRW-1:0]                    cand_slot_o,
    output logic                               cand_is_rd_o,
    output logic [AGE_WIDTH-1:0]               cand_pri_o
);

    // ---- per-entry field extractors (single variable part-select each) ------
    function automatic logic [BKW-1:0] f_bank(
        input logic [NUM_ENTRIES*BKW-1:0] v, input logic [PTRW-1:0] e);
        return v[e*BKW +: BKW];
    endfunction
    function automatic logic [ROW_WIDTH-1:0] f_row(
        input logic [NUM_ENTRIES*ROW_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*ROW_WIDTH +: ROW_WIDTH];
    endfunction
    function automatic logic [COL_WIDTH-1:0] f_col(
        input logic [NUM_ENTRIES*COL_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*COL_WIDTH +: COL_WIDTH];
    endfunction

    // oldest-in-mask via the age-order matrix -> one-hot is_old, then slot.
    // Reduction operators (&terms, |bmask), not accumulator loops: a reduce is
    // one $reduce cell; the obvious `for j: if(...) ge=0` / `for i: if(old)
    // slot=i` synthesize as NUM_ENTRIES-deep mux chains (PUMICE-017).
    function automatic logic [PTRW:0] arg_oldest(
        input logic [NUM_ENTRIES-1:0]              mask,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  older);
        logic                   found;
        logic [PTRW-1:0]        slot;
        logic [NUM_ENTRIES-1:0] is_old;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic [NUM_ENTRIES-1:0] orow  = older[i*NUM_ENTRIES +: NUM_ENTRIES];
            automatic logic [NUM_ENTRIES-1:0] terms;
            // i is >= entry j iff j is itself, not masked, or i is older than j
            for (int j = 0; j < NUM_ENTRIES; j++)
                terms[j] = (j == i) || !mask[j] || orow[j];
            is_old[i] = mask[i] && (&terms);      // one reduce-AND
        end
        found = |is_old;                          // one reduce-OR
        slot  = '0;
        // one-hot -> binary: each index bit is a masked reduce-OR
        for (int b = 0; b < PTRW; b++) begin
            automatic logic [NUM_ENTRIES-1:0] bmask;
            for (int i = 0; i < NUM_ENTRIES; i++) bmask[i] = is_old[i] && i[b];
            slot[b] = |bmask;
        end
        return {found, slot};
    endfunction

    // Relative-age priority of a slot: how many VALID same-CAM entries this slot
    // is older than (older[slot][j] over valid j). The globally-oldest entry in
    // the CAM is older than all others -> max; the final-stage tournament picks
    // the max across banks, so this is a real cross-bank age key (within the CAM
    // epoch), not the scaffold's slot proxy. The count is a small popcount (the
    // same 3-bit-adder pattern the flat arbiter uses for rd_pop/wr_pop).
    function automatic logic [AGE_WIDTH-1:0] age_rank(
        input logic [PTRW-1:0]                     slot,
        input logic [NUM_ENTRIES-1:0]              valid,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  older);
        logic [NUM_ENTRIES-1:0] orow;
        logic [AGE_WIDTH-1:0]   cnt;
        orow = older[slot*NUM_ENTRIES +: NUM_ENTRIES];
        cnt  = '0;
        for (int j = 0; j < NUM_ENTRIES; j++)
            if (valid[j] && orow[j] && (PTRW'(j) != slot)) cnt = cnt + AGE_WIDTH'(1);
        return cnt;
    endfunction

    // ---- per-bank guards (registered) --------------------------------------
    logic r_guard0, r_guard1;                    // block ACT/PRE re-issue (2 cyc)
    logic r_preguard0, r_preguard1, r_preguard2; // block columns after PRE (3 cyc)
    logic r_apguard0, r_apguard1;                // block columns after AP col (2 cyc)
    logic w_guard, w_preguard, w_apguard;
    assign w_guard    = r_guard0 || r_guard1;
    assign w_preguard = r_preguard0 || r_preguard1 || r_preguard2;
    assign w_apguard  = r_apguard0 || r_apguard1;

    // ---- per-bank auto-precharge decision ----------------------------------
    logic w_ap;
    assign w_ap = ap_mode_en_i ? ap_close_bit_i : (page_policy_i == PAGE_POLICY_CLOSE);

    // ---- classify THIS bank's entries (BANK_ID fixed: open_row is direct) ---
    logic [NUM_ENTRIES-1:0] rd_col_m, rd_act_m, rd_pre_m;
    logic [NUM_ENTRIES-1:0] wr_col_m, wr_act_m, wr_pre_m;
    always_comb begin
        rd_col_m = '0; rd_act_m = '0; rd_pre_m = '0;
        wr_col_m = '0; wr_act_m = '0; wr_pre_m = '0;
        for (int e = 0; e < NUM_ENTRIES; e++) begin
            automatic logic [PTRW-1:0] ei    = PTRW'(e);
            automatic logic mine_r = rd_valid_i[e] && (f_bank(rd_bank_i, ei) == BKW'(BANK_ID));
            automatic logic mine_w = wr_valid_i[e] && (f_bank(wr_bank_i, ei) == BKW'(BANK_ID));
            automatic logic rhit   = bank_row_active_i && (f_row(rd_row_i, ei) == bank_open_row_i);
            automatic logic whit   = bank_row_active_i && (f_row(wr_row_i, ei) == bank_open_row_i);
            if (mine_r) begin
                rd_col_m[e] = rhit && bank_rdwr_ready_i && rd_issue_ready_i
                              && !w_preguard && !w_apguard;
                rd_act_m[e] = !bank_row_active_i && bank_act_ready_i && !w_guard;
                rd_pre_m[e] = bank_row_active_i && !rhit && bank_pre_ready_i && !w_guard;
            end
            if (mine_w) begin
                wr_col_m[e] = whit && bank_rdwr_ready_i && wr_commit_ready_i
                              && !w_preguard && !w_apguard;
                wr_act_m[e] = !bank_row_active_i && bank_act_ready_i && !w_guard;
                wr_pre_m[e] = bank_row_active_i && !whit && bank_pre_ready_i && !w_guard;
            end
        end
    end

    // ---- oldest-per-class {found,slot}, all six in parallel ----------------
    logic [PTRW:0] rc, ra, rp, wc, wa, wp;
    assign rc = arg_oldest(rd_col_m, rd_older_i);
    assign ra = arg_oldest(rd_act_m, rd_older_i);
    assign rp = arg_oldest(rd_pre_m, rd_older_i);
    assign wc = arg_oldest(wr_col_m, wr_older_i);
    assign wa = arg_oldest(wr_act_m, wr_older_i);
    assign wp = arg_oldest(wr_pre_m, wr_older_i);
    logic rc_f, ra_f, rp_f, wc_f, wa_f, wp_f;
    assign rc_f = rc[PTRW]; assign ra_f = ra[PTRW]; assign rp_f = rp[PTRW];
    assign wc_f = wc[PTRW]; assign wa_f = wa[PTRW]; assign wp_f = wp[PTRW];

    // ---- parallel winner select (class order col > act > pre; read-priority
    // resolves rd/wr ties). Resolved on the six 1-bit FOUND flags, NOT by
    // re-muxing the wide fields six times.
    logic col_any, act_any;
    assign col_any = rc_f || wc_f;
    assign act_any = ra_f || wa_f;
    logic sel_col_rd, sel_col_wr, sel_act_rd, sel_act_wr, sel_pre_rd;
    // read-priority: read wins ties (read_pref_i=1). read_pref_i=0 -> write wins.
    // The write-precharge case is the fallthrough (n_op default = OP_PRE), so it
    // needs no explicit select bit.
    assign sel_col_rd = read_pref_i ? rc_f            : (rc_f && !wc_f);
    assign sel_col_wr = read_pref_i ? (wc_f && !rc_f) : wc_f;
    assign sel_act_rd = ra_f            && !col_any;
    assign sel_act_wr = (wa_f && !ra_f) && !col_any;
    assign sel_pre_rd = rp_f            && !col_any && !act_any;

    logic n_is_rd, n_valid, n_ap;
    assign n_is_rd = sel_col_rd || sel_act_rd || sel_pre_rd;
    assign n_valid = col_any || act_any || rp_f || wp_f;
    assign n_ap    = (sel_col_rd || sel_col_wr) && w_ap;

    // winning slot inside each CAM (small 3:1 mux of PTRW-bit slots), then ONE
    // part-select per field on the chosen CAM/slot.
    logic [PTRW-1:0] rd_slot, wr_slot, n_slot;
    assign rd_slot = sel_col_rd ? rc[PTRW-1:0] : sel_act_rd ? ra[PTRW-1:0] : rp[PTRW-1:0];
    assign wr_slot = sel_col_wr ? wc[PTRW-1:0] : sel_act_wr ? wa[PTRW-1:0] : wp[PTRW-1:0];
    assign n_slot  = n_is_rd ? rd_slot : wr_slot;

    logic [ROW_WIDTH-1:0] n_row;
    logic [COL_WIDTH-1:0] n_col;
    assign n_row = n_is_rd ? f_row(rd_row_i, rd_slot) : f_row(wr_row_i, wr_slot);
    assign n_col = n_is_rd ? f_col(rd_col_i, rd_slot) : f_col(wr_col_i, wr_slot);

    // final op incl per-bank auto-precharge (RDA/WRA under CLOSE).
    dram_op_e n_op;
    always_comb begin
        if      (sel_col_rd) n_op = w_ap ? OP_RDA : OP_RD;
        else if (sel_col_wr) n_op = w_ap ? OP_WRA : OP_WR;
        else if (sel_act_rd || sel_act_wr) n_op = OP_ACT;
        else                 n_op = OP_PRE;
    end

    // relative-age priority of the winner (over its own CAM's valid set).
    logic [AGE_WIDTH-1:0] n_pri;
    assign n_pri = n_is_rd ? age_rank(rd_slot, rd_valid_i, rd_older_i)
                           : age_rank(wr_slot, wr_valid_i, wr_older_i);

    // ---- register this bank's candidate ------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            cand_valid_o <= 1'b0;
            cand_op_o    <= OP_NOP;
            cand_ap_o    <= 1'b0;
            cand_row_o   <= '0;
            cand_col_o   <= '0;
            cand_slot_o  <= '0;
            cand_is_rd_o <= 1'b1;
            cand_pri_o   <= '0;
        end else begin
            cand_valid_o <= n_valid;
            cand_op_o    <= n_op;
            cand_ap_o    <= n_ap;
            cand_row_o   <= n_row;
            cand_col_o   <= n_col;
            cand_slot_o  <= n_slot;
            cand_is_rd_o <= n_is_rd;
            cand_pri_o   <= n_pri;
        end
    )

    // ---- guard update: latch on the TRUE issued op (issued_op_i), so it is
    // correct even when the core held the decision under backpressure. -------
    logic w_iss_actpre, w_iss_pre, w_iss_apcol;
    assign w_iss_actpre = issued_i && ((issued_op_i == OP_ACT) || (issued_op_i == OP_PRE));
    assign w_iss_pre    = issued_i && (issued_op_i == OP_PRE);
    assign w_iss_apcol  = issued_i && ((issued_op_i == OP_RDA) || (issued_op_i == OP_WRA));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0    <= 1'b0; r_guard1    <= 1'b0;
            r_preguard0 <= 1'b0; r_preguard1 <= 1'b0; r_preguard2 <= 1'b0;
            r_apguard0  <= 1'b0; r_apguard1  <= 1'b0;
        end else begin
            r_guard1    <= r_guard0;
            r_guard0    <= w_iss_actpre;
            r_preguard2 <= r_preguard1;
            r_preguard1 <= r_preguard0;
            r_preguard0 <= w_iss_pre;
            r_apguard1  <= r_apguard0;
            r_apguard0  <= w_iss_apcol;
        end
    )

endmodule : pumice_bank_cmd_picker
