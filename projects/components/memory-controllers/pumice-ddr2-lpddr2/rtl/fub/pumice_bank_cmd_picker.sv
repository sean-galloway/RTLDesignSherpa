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
//   image + per-bank readiness, builds a COMPOSITE PRIORITY KEY for EVERY entry
//   in parallel, and REGISTERS the single max-key entry as this bank's
//   candidate. pumice_bank_sched_core then arbitrates the NUM_BANKS candidates
//   by that key (a max-key tournament) -- reproducing the flat arbiter's global
//   SCHED_POLICY pick without the flat cross-bank associative cone.
//
// DEPTH-CRITICAL STRUCTURE (why cand_pri is shallow): the per-entry key is a
// pure function of THAT ENTRY's own fields plus its own row of the older matrix
// (age_rank_e = $countones of entry e's older-row -- who e outranks -- a
// PARALLEL per-entry popcount, NOT a function of the selected slot). All 2*N
// keys are computed at once; a single balanced max-key tournament then selects
// the winner, and cand_pri is the winner's ALREADY-COMPUTED key via one mux.
// Nothing is recomputed from the winning slot, so the old 95-level key cone
// (key depended on arg_sel's selected slot, which depended on the key) is gone.
//
// Composite key (MSB..LSB, so one unsigned max compares them lexicographically):
//   { class_pri[1:0], dir_pri[1:0], qos[3:0], pop_key[POPW-1:0], age_rank[PTRW-1:0] }
//   - class_pri : class rank under sched_access_pref (column / row / precharge
//                 first) -- the OUTER key, class before entry (flat w_pick_class).
//   - dir_pri   : direction-preference score. Read outranks write EXCEPT under
//                 write-batching drain / prio_sub=none(fair-alt) / prio_sub=
//                 age_boost where a boosted write outranks a non-boosted read.
//                 Encoded per-entry so it needs no winner feedback (see f_dir).
//   - qos       : AxQOS when qos_en, so the max-QoS candidate wins within a
//                 class+direction (subsumes the flat qos_top narrowing).
//   - pop_key   : sched_col_sel (columns) / sched_row_sel (activates) population
//                 term -- most -> pop, fewest -> (MAXPOP-pop), oldest -> 0.
//   - age_rank  : relative age (count of same-CAM valid entries e is older than).
//
// The order-mode overlay (in_order / age_threshold) arrives as per-entry KEEP
// masks (computed once in the wrapper, incl. the cross-CAM head compare) and
// simply gates candidacy. Write-batch occupancy/drain and the fair-alternation
// toggle are global, computed once in the wrapper and fanned in.
//
// PER-BANK guards carried here (fixed real data-corruption bugs; kept identical):
//   - r_guard0/1/2   same-bank ACT/PRE re-issue (bank-timer latency + core 2-stage),
//   - r_preguard0/1/2 PRE-column staleness (a column within 3 cycles of a PRE
//                     lands on the just-closed row),
//   - r_apguard0/1   AP-column (RDA/WRA precharges the bank; next access re-ACTs),
//   - rd_issue_ready / wr_commit_ready column FIFO-room gating.
// Feedback: issued_i + issued_op_i (the op the core actually fired), so guards
// latch on the true issued op even under cmd-FIFO backpressure. The guard SHIFT
// depths (3/3/2) span the pipelined issued_i round-trip incl. the core's TWO
// register stages (A + B), so a candidate cannot double-issue.
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
    parameter int POPW        = 4,
    parameter int KEYW        = 15
) (
    input  logic                               aclk,
    input  logic                               aresetn,

    // ---- policy (per-bank auto-precharge decode + SCHED_POLICY axes) ----
    input  page_policy_e                       page_policy_i,
    input  logic                               ap_mode_en_i,
    input  logic                               ap_close_bit_i,     // this bank's ap_close
    input  logic [1:0]                         sched_access_pref_i,
    input  logic [1:0]                         sched_row_sel_i,
    input  logic [1:0]                         sched_col_sel_i,
    input  logic [1:0]                         sched_prio_sub_i,
    input  logic                               sched_qos_en_i,
    input  logic                               wr_drain_i,         // global write-batch drain
    input  logic                               dir_rr_i,           // global fair-alt toggle

    // ---- this bank's registered live state (from pumice_bank_timers) ----
    input  logic                               bank_act_ready_i,
    input  logic                               bank_rdwr_ready_i,
    input  logic                               bank_pre_ready_i,
    input  logic                               bank_row_active_i,
    input  logic [ROW_WIDTH-1:0]               bank_open_row_i,

    // ---- rd CAM per-entry vectors (registered, whole CAM) + overlays --------
    input  logic [NUM_ENTRIES-1:0]             rd_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]         rd_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]   rd_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]   rd_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] rd_older_i,
    input  logic                               rd_issue_ready_i,
    input  logic [NUM_ENTRIES-1:0]             rd_keep_i,          // order-mode narrow
    input  logic [NUM_ENTRIES*POPW-1:0]        rd_pop_i,
    input  logic [NUM_ENTRIES*4-1:0]           rd_qos_i,
    input  logic [NUM_ENTRIES-1:0]             rd_age_exceed_i,

    // ---- wr CAM per-entry vectors (registered, whole CAM) + overlays --------
    input  logic [NUM_ENTRIES-1:0]             wr_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]         wr_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]   wr_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]   wr_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] wr_older_i,
    input  logic                               wr_commit_ready_i,
    input  logic [NUM_ENTRIES-1:0]             wr_keep_i,
    input  logic [NUM_ENTRIES*POPW-1:0]        wr_pop_i,
    input  logic [NUM_ENTRIES*4-1:0]           wr_qos_i,
    input  logic [NUM_ENTRIES-1:0]             wr_age_exceed_i,

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
    output logic [KEYW-1:0]                     cand_pri_o
);

    localparam int M    = 2 * NUM_ENTRIES;        // rd pool [0..N-1] + wr pool [N..2N-1]
    localparam int LV   = $clog2(M);
    localparam logic [1:0] CCOL = 2'd1, CACT = 2'd2, CPRE = 2'd3;  // class code
    localparam logic [1:0] PRIONONE = 2'd1;       // prio_sub: fair alternation
    localparam logic [1:0] PRIOAGE  = 2'd3;       // prio_sub: age_boost
    localparam logic [1:0] PREFROW  = 2'd2;       // access_pref: row_first
    localparam logic [1:0] PREFPRE  = 2'd3;       // access_pref: precharge_first
    localparam logic [1:0] SELMOST  = 2'd1;       // row/col_sel: most_pending
    localparam logic [1:0] SELFEWEST = 2'd2;      // row/col_sel: fewest_pending

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

    // class rank under access_pref (2=top, 0=low).
    function automatic logic [1:0] f_class_pri(input logic [1:0] cls, input logic [1:0] pref);
        logic is_c, is_a;
        is_c = (cls == CCOL);
        is_a = (cls == CACT);
        case (pref)
            PREFROW: return is_a ? 2'd2 : is_c ? 2'd1 : 2'd0;
            PREFPRE: return is_c ? 2'd1 : is_a ? 2'd0 : 2'd2;
            default: return is_c ? 2'd2 : is_a ? 2'd1 : 2'd0;
        endcase
    endfunction

    // direction-preference score (2 bits). Read outranks write by default; drain
    // / fair-alt flip it; age_boost lets a boosted write beat a NON-boosted read
    // (and, crucially, a boosted read still beats a boosted write -- exactly the
    // flat w_*_wrf = wr_boost && !rd_boost rule, expressed per-entry).
    function automatic logic [1:0] f_dir(
        input logic is_wr, input logic boost,
        input logic [1:0] prio, input logic drain, input logic rr);
        automatic logic wf_global = drain || ((prio == PRIONONE) && rr);
        if (wf_global)              return is_wr ? 2'd1 : 2'd0;   // write-first
        else if (prio == PRIOAGE)   return is_wr ? (boost ? 2'd2 : 2'd0)
                                                 : (boost ? 2'd3 : 2'd1);
        else                        return is_wr ? 2'd0 : 2'd1;   // read-priority
    endfunction

    // pop_key term (direction per most/fewest/oldest).
    function automatic logic [POPW-1:0] f_pop_key(
        input logic [1:0] sel, input logic [POPW-1:0] pop);
        case (sel)
            SELMOST:   return pop;
            SELFEWEST: return POPW'(NUM_ENTRIES) - pop;
            default:   return '0;
        endcase
    endfunction

    // ---- per-bank guards (registered) --------------------------------------
    logic r_guard0, r_guard1, r_guard2;           // block ACT/PRE re-issue (3 cyc)
    logic r_preguard0, r_preguard1, r_preguard2; // block columns after PRE (3 cyc)
    logic r_apguard0, r_apguard1;                // block columns after AP col (2 cyc)
    logic w_guard, w_preguard, w_apguard;
    assign w_guard    = r_guard0 || r_guard1 || r_guard2;
    assign w_preguard = r_preguard0 || r_preguard1 || r_preguard2;
    assign w_apguard  = r_apguard0 || r_apguard1;

    // ---- per-bank auto-precharge decision ----------------------------------
    logic w_ap;
    assign w_ap = ap_mode_en_i ? ap_close_bit_i : (page_policy_i == PAGE_POLICY_CLOSE);

    // ======================================================================
    // PER-ENTRY, PARALLEL: legality, class, key, op, ap, row, col -- one lane
    // per entry in each CAM. No cross-entry / slot dependence; all 2*N lanes are
    // peers. The tournament key carries LEGAL as its MSB so an illegal lane (key
    // MSB 0) always loses to any legal lane -- which makes each tournament level
    // a plain gt->mux (no separate valid book-keeping on the compare path). The
    // row/col are per-entry CONSTANT slices (the loop index e is unrolled), so
    // they are carried as tournament payload -- no post-select variable
    // part-select (that multiply-indexed shift was the old tail).
    // ======================================================================
    localparam int KTW = KEYW + 1;                // {legal, key}
    logic [KTW-1:0]       e_tkey [M];
    logic [PTRW-1:0]      e_slot [M];
    logic [M-1:0]         e_isrd;
    dram_op_e             e_op   [M];
    logic [M-1:0]         e_ap;
    logic [ROW_WIDTH-1:0] e_row  [M];
    logic [COL_WIDTH-1:0] e_col  [M];

    always_comb begin
        for (int c = 0; c < 2; c++) begin
            for (int e = 0; e < NUM_ENTRIES; e++) begin
                automatic logic [LV-1:0] m     = LV'(c*NUM_ENTRIES + e);
                automatic logic          is_wr = (c == 1);
                automatic logic [PTRW-1:0] ei  = PTRW'(e);
                automatic logic [NUM_ENTRIES-1:0] valv  = is_wr ? wr_valid_i : rd_valid_i;
                automatic logic [NUM_ENTRIES*BKW-1:0] bnkv = is_wr ? wr_bank_i : rd_bank_i;
                automatic logic [NUM_ENTRIES*ROW_WIDTH-1:0] rowv = is_wr ? wr_row_i : rd_row_i;
                automatic logic [NUM_ENTRIES*COL_WIDTH-1:0] colv = is_wr ? wr_col_i : rd_col_i;
                automatic logic [NUM_ENTRIES*NUM_ENTRIES-1:0] oldv = is_wr ? wr_older_i
                                                                             : rd_older_i;
                automatic logic [NUM_ENTRIES-1:0] keepv = is_wr ? wr_keep_i : rd_keep_i;
                automatic logic [NUM_ENTRIES-1:0] agxv = is_wr ? wr_age_exceed_i
                                                                            : rd_age_exceed_i;
                automatic logic [NUM_ENTRIES*4-1:0] qosv = is_wr ? wr_qos_i : rd_qos_i;
                automatic logic [NUM_ENTRIES*POPW-1:0] popv = is_wr ? wr_pop_i : rd_pop_i;
                automatic logic cfifo = is_wr ? wr_commit_ready_i : rd_issue_ready_i;

                // classify: reduction-AND conjunctions (one $reduce cell each,
                // not a serial && chain).
                automatic logic mine = &{valv[e], (f_bank(bnkv, ei) == BKW'(BANK_ID)), keepv[e]};
                automatic logic rhit = bank_row_active_i && (f_row(rowv, ei) == bank_open_row_i);
                automatic logic is_col = &{mine, rhit, bank_rdwr_ready_i, cfifo,
                                           ~w_preguard, ~w_apguard};
                automatic logic is_act = &{mine, ~bank_row_active_i, bank_act_ready_i, ~w_guard};
                automatic logic is_pre = &{mine, bank_row_active_i, ~rhit,
                                           bank_pre_ready_i, ~w_guard};
                automatic logic legal  = is_col || is_act || is_pre;
                automatic logic [1:0] eclass = is_col ? CCOL : is_act ? CACT : CPRE;

                // per-entry key fields (pure functions of e's own state)
                automatic logic [1:0]      k_class = f_class_pri(eclass, sched_access_pref_i);
                automatic logic [1:0]      k_dir   = f_dir(is_wr, agxv[e], sched_prio_sub_i,
                                                           wr_drain_i, dir_rr_i);
                automatic logic [3:0]      k_qos   = sched_qos_en_i ? qosv[e*4 +: 4] : 4'd0;
                automatic logic [1:0]      psel    = is_col ? sched_col_sel_i
                                                   : is_act ? sched_row_sel_i : 2'd0;
                automatic logic [POPW-1:0] k_pop   = f_pop_key(psel, popv[e*POPW +: POPW]);
                // age_rank: PARALLEL per-entry popcount of e's own older-row.
                automatic logic [NUM_ENTRIES-1:0] orow = oldv[e*NUM_ENTRIES +: NUM_ENTRIES];
                automatic logic [PTRW-1:0] k_age   = PTRW'($countones(orow & valv));

                e_tkey[m] = {legal, k_class, k_dir, k_qos, k_pop, k_age};
                e_slot[m] = ei;
                e_isrd[m] = !is_wr;
                e_ap[m]   = is_col && w_ap;
                e_op[m]   = is_col ? (is_wr ? (w_ap ? OP_WRA : OP_WR) : (w_ap ? OP_RDA : OP_RD))
                          : is_act ? OP_ACT : OP_PRE;
                e_row[m]  = f_row(rowv, ei);      // constant slice (e unrolled)
                e_col[m]  = f_col(colv, ei);      // constant slice
            end
        end
    end

    // ======================================================================
    // Single balanced MAX-KEY tournament over the 2*N per-entry lanes. Each
    // level is a plain gt->mux (legal is the key MSB, so validity rides the
    // compare); the payload (slot/is_rd/op/ap/row/col) follows the same select.
    // Prefer lower index on ties (strict gt -> left wins). LV = clog2(2N) levels.
    // ======================================================================
    logic [KTW-1:0]       tk [LV+1][M];
    logic [PTRW-1:0]      ts [LV+1][M];
    logic                 ti [LV+1][M];   // is_rd
    dram_op_e             to [LV+1][M];
    logic                 ta [LV+1][M];   // ap
    logic [ROW_WIDTH-1:0] tr [LV+1][M];
    logic [COL_WIDTH-1:0] tc [LV+1][M];
    logic [KTW-1:0]       n_tkey;
    logic                 n_is_rd, n_ap;
    logic [PTRW-1:0]      n_slot;
    dram_op_e             n_op;
    logic [ROW_WIDTH-1:0] n_row;
    logic [COL_WIDTH-1:0] n_col;
    always_comb begin
        for (int m = 0; m < M; m++) begin
            tk[0][m] = e_tkey[m]; ts[0][m] = e_slot[m]; ti[0][m] = e_isrd[m];
            to[0][m] = e_op[m];   ta[0][m] = e_ap[m];   tr[0][m] = e_row[m];
            tc[0][m] = e_col[m];
        end
        for (int l = 1; l <= LV; l++) begin
            for (int i = 0; i < (M >> l); i++) begin
                automatic logic pick_r = tk[l-1][2*i+1] > tk[l-1][2*i];
                tk[l][i] = pick_r ? tk[l-1][2*i+1] : tk[l-1][2*i];
                ts[l][i] = pick_r ? ts[l-1][2*i+1] : ts[l-1][2*i];
                ti[l][i] = pick_r ? ti[l-1][2*i+1] : ti[l-1][2*i];
                to[l][i] = pick_r ? to[l-1][2*i+1] : to[l-1][2*i];
                ta[l][i] = pick_r ? ta[l-1][2*i+1] : ta[l-1][2*i];
                tr[l][i] = pick_r ? tr[l-1][2*i+1] : tr[l-1][2*i];
                tc[l][i] = pick_r ? tc[l-1][2*i+1] : tc[l-1][2*i];
            end
        end
        n_tkey = tk[LV][0]; n_slot = ts[LV][0]; n_is_rd = ti[LV][0];
        n_op   = to[LV][0]; n_ap   = ta[LV][0]; n_row   = tr[LV][0];
        n_col  = tc[LV][0];
    end

    logic            n_valid;
    logic [KEYW-1:0] n_key;
    assign n_valid = n_tkey[KEYW];        // the legal MSB
    assign n_key   = n_tkey[KEYW-1:0];    // key for the core's tournament

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
            cand_pri_o   <= n_key;
        end
    )

    // ---- guard update: latch on the TRUE issued op (issued_op_i) ------------
    logic w_iss_actpre, w_iss_pre, w_iss_apcol;
    assign w_iss_actpre = issued_i && ((issued_op_i == OP_ACT) || (issued_op_i == OP_PRE));
    assign w_iss_pre    = issued_i && (issued_op_i == OP_PRE);
    assign w_iss_apcol  = issued_i && ((issued_op_i == OP_RDA) || (issued_op_i == OP_WRA));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0    <= 1'b0; r_guard1    <= 1'b0; r_guard2 <= 1'b0;
            r_preguard0 <= 1'b0; r_preguard1 <= 1'b0; r_preguard2 <= 1'b0;
            r_apguard0  <= 1'b0; r_apguard1  <= 1'b0;
        end else begin
            r_guard2    <= r_guard1;
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
