// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: scheduler
// Purpose: Arbiter at the heart of the controller core. Each cycle,
//          decide what to issue on the DFI command bus.
//
//          v1 priority (high → low):
//            1. init_busy_i      → NOP (init_sequencer owns the bus)
//            2. mr_req_i         → MRS (mode-register write)
//            3. refresh_req_i    → grant + REF
//            4. pdn_req_i        → grant + NOP (CKE drop handled by
//                                   powerdown_ctrl)
//            5. WR CAM op        → ACT / WRA / PRE-state-machine
//            6. RD CAM op        → ACT / RDA / PRE-state-machine
//            7. else             → NOP
//
//          Page policy is selected by the PAGE_POLICY parameter:
//            CLOSE       — every column command is RDA/WRA (auto-pre).
//                          Bank returns to IDLE via xbank_timers's
//                          ap_pending logic. No row-hit reuse.
//            OPEN        — row-hit slots skip ACT (issue plain RD/WR);
//                          row-miss slots issue PRE → ACT → RD/WR.
//                          Banks stay open until evicted.
//            HAPPY_HYBRID— uses the page_predictor FUB's per-bank
//                          "predict_open" hint to decide ap on each
//                          column command. On hit: behaves OPEN; on
//                          miss: behaves CLOSE.
//
//          State for an in-progress column op:
//            * `r_pending` = the (rank, bank, row, col, len, slot)
//              chosen for the current pass.
//            * On entry: determine action by policy + bank state:
//                row-hit (bank ACTIVE + open_row matches) → skip to RDWR
//                row-miss (bank ACTIVE + open_row mismatches) → PRE, ACT, RDWR
//                bank IDLE → ACT, RDWR
//
// v2 (TODO):
//   * Bank-parallel multi-cmd issue per DFI cycle (multi-phase).
//   * Write-clustering hysteresis.
//   * Age-weighted W/R arbitration (currently round-robin).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scheduler
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int AXI_ID_WIDTH    = 4,
    // PAGE_POLICY values: 0=OPEN, 1=CLOSE, 2=HAPPY_HYBRID (mirrors
    // page_policy_e in the package). Typed as `int` so the test runner
    // can pass -GPAGE_POLICY=N without WIDTHTRUNC warnings.
    parameter int PAGE_POLICY     = 32'(PAGE_POLICY_CLOSE),

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- CAM query (drive into axi_frontend_macro) -----
    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [ROW_WIDTH-1:0]       q_row_o,

    // ----- CAM match vectors -----
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    // ----- per-slot metadata snapshots -----
    input  logic [WR_CAM_DEPTH-1:0][RKW-1:0]             wr_snap_rank_i,
    input  logic [WR_CAM_DEPTH-1:0][BKW-1:0]             wr_snap_bank_i,
    input  logic [WR_CAM_DEPTH-1:0][ROW_WIDTH-1:0]       wr_snap_row_i,
    input  logic [WR_CAM_DEPTH-1:0][COL_WIDTH-1:0]       wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] wr_snap_len_i,
    input  logic [WR_CAM_DEPTH-1:0][3:0]                 wr_snap_qos_i,
    input  logic [WR_CAM_DEPTH-1:0][7:0]                 wr_snap_age_i,
    input  logic [RD_CAM_DEPTH-1:0][RKW-1:0]             rd_snap_rank_i,
    input  logic [RD_CAM_DEPTH-1:0][BKW-1:0]             rd_snap_bank_i,
    input  logic [RD_CAM_DEPTH-1:0][ROW_WIDTH-1:0]       rd_snap_row_i,
    input  logic [RD_CAM_DEPTH-1:0][COL_WIDTH-1:0]       rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] rd_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][3:0]                 rd_snap_qos_i,
    // Per-slot push-order tag from rd_cmd_cam. Used to break QoS
    // ties by AR-arrival order so same-id R returns honor AXI4
    // in-order ordering even when slot indices are reused (a freed
    // slot at index 0 must not jump in front of older pending slots
    // at higher indices).
    input  logic [RD_CAM_DEPTH-1:0][7:0]                 rd_snap_age_i,

    // ----- mark-issued strobes back to CAMs -----
    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    // ----- timer readiness -----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,
    input  logic [NUM_RANKS-1:0]       tfaw_window_ok_i,

    // ----- page predictor hint (HAPPY_HYBRID only; tie-low otherwise) -----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] predict_open_i,

    // ----- refresh / power injection -----
    input  logic                       refresh_req_i,
    output logic                       refresh_grant_o,
    input  logic                       pdn_req_i,
    output logic                       pdn_grant_o,

    // ----- init / mode-reg injection -----
    input  logic                       init_busy_i,
    input  logic                       mr_req_i,
    output logic                       mr_grant_o,

    // ----- chosen op into dfi_cmd_formatter -----
    output logic                       cmd_valid_o,
    input  logic                       cmd_ready_i,
    output dram_op_e                   cmd_op_o,
    output logic [RKW-1:0]             cmd_rank_o,
    output logic [BKW-1:0]             cmd_bank_o,
    output logic [ROW_WIDTH-1:0]       cmd_row_o,
    output logic [COL_WIDTH-1:0]       cmd_col_o,
    output logic [BURST_LEN_WIDTH-1:0] cmd_len_o,
    output logic [WSL-1:0]             cmd_wr_slot_o,
    output logic [RSL-1:0]             cmd_rd_slot_o,

    // ----- bank-event strobes to xbank_timers -----
    output logic                       evt_act_o,
    output logic                       evt_rd_o,
    output logic                       evt_wr_o,
    output logic                       evt_pre_o,
    output logic                       evt_ap_o,    // 1 when evt_rd/evt_wr
                                                    // accompanies RDA/WRA so
                                                    // xbank_timers auto-PREs
    output logic [RKW-1:0]             evt_rank_o,
    output logic [BKW-1:0]             evt_bank_o
);

    //=========================================================================
    // FSM for an in-progress column-op (page-policy-aware):
    //   S_IDLE       : choose next slot; query bank state; transition to
    //                  S_NEED_RDWR (row hit), S_NEED_PRE (row miss),
    //                  or S_NEED_ACT (bank IDLE), based on PAGE_POLICY.
    //   S_NEED_PRE   : wait until bank_pre_ready; issue PRE; → S_NEED_ACT.
    //                  (open-page row miss only)
    //   S_NEED_ACT   : wait until bank_act_ready; issue ACT
    //   S_NEED_RDWR  : wait until bank_rdwr_ready; issue RD/WR or RDA/WRA
    //                  per policy + predictor.
    //   S_DONE       : mark_issued pulse; back to IDLE
    //=========================================================================
    typedef enum logic [2:0] {
        S_IDLE      = 3'd0,
        S_NEED_PRE  = 3'd1,
        S_NEED_ACT  = 3'd2,
        S_NEED_RDWR = 3'd3,
        S_DONE      = 3'd4
    } state_e;

    state_e             r_state;

    // Pending op context
    logic               r_pending_is_wr;
    logic [WSL-1:0]     r_pending_wr_slot;
    logic [RSL-1:0]     r_pending_rd_slot;
    logic [RKW-1:0]     r_pending_rank;
    logic [BKW-1:0]     r_pending_bank;
    logic [ROW_WIDTH-1:0] r_pending_row;
    logic [COL_WIDTH-1:0] r_pending_col;
    logic [BURST_LEN_WIDTH-1:0] r_pending_len;

    //=========================================================================
    // Slot pick: lowest-index pending slot. We use the snapshot's
    // rank/bank/row/col/len for that slot directly — no CAM query bus.
    // (`wr_match_pending_i` here is effectively the same as `snap_valid &
    // !snap_issued` since we don't drive q_*. A future revision can use
    // a per-cycle query to filter on (rank, bank, row) for row-hit-first.)
    //=========================================================================
    logic                w_have_wr;
    logic                w_have_rd;
    logic [WSL-1:0]      w_wr_pick;
    logic [RSL-1:0]      w_rd_pick;

    // F4c: QoS-aware slot picker with age tie-break (issue #21),
    // restructured for 100 MHz timing closure.
    //
    // Highest AXI QoS wins. On QoS ties, OLDEST age wins (signed-diff for
    // wraparound safety). On a full tie, the LOWER slot index wins — this
    // preserves AXI4 same-id ordering and matches the original picker's
    // lowest-index-wins behaviour (a freed/reused slot must not jump ahead
    // of older pending slots).
    //
    // The original picker was a LINEAR scan that carried the running "best"
    // across all CAM_DEPTH iterations — an N-deep ripple of {8-bit signed
    // age subtract + QoS compare + select}. At depth 16 that synthesized to
    // ~30 CARRY4 in series and, feeding combinationally into r_pending_*,
    // produced a 68-level / ~40 ns path (WNS -30 ns @ 100 MHz). Two changes:
    //   (1) Balanced-tree reduction: pairwise tournament, depth
    //       ceil(log2(CAM_DEPTH)) compare stages instead of CAM_DEPTH.
    //   (2) Pipeline the pick: the winning candidate is REGISTERED
    //       (r_wr_cand / r_rd_cand) and S_IDLE consumes the registered pick.
    //       The FSM already spends >=4 cycles per op, so one cycle of pick
    //       latency costs ~no throughput but splits the cone into
    //       (CAM -> tree -> pick reg) and (pick reg -> index mux -> pending).
    //
    // Candidate packing: {valid, qos[3:0], age[7:0], slot_idx}.
    localparam int WCW   = 1 + 4 + 8 + WSL;             // WR candidate width
    localparam int RCW   = 1 + 4 + 8 + RSL;             // RD candidate width
    localparam int WLVLS = (WR_CAM_DEPTH > 1) ? $clog2(WR_CAM_DEPTH) : 0;
    localparam int RLVLS = (RD_CAM_DEPTH > 1) ? $clog2(RD_CAM_DEPTH) : 0;
    localparam int WNPOT = 1 << WLVLS;   // next pow2 >= depth (== depth if pow2)
    localparam int RNPOT = 1 << RLVLS;
    // Pick tree is pipelined at its MIDPOINT: stage A folds the first WHALF
    // levels and registers the WMID survivors; stage B folds the rest into the
    // final candidate register. This halves the CAM-age -> pick-register
    // combinational cone (the 19-level / 8-CARRY4 age-compare tournament that
    // held post-route WNS at -1.5 ns). Costs one more cycle of pick latency,
    // hidden by the FSM's multi-cycle op (the pick is prefetched during the
    // prior op in steady state; only the first pick from idle sees it).
    localparam int WHALF = WLVLS / 2;
    localparam int RHALF = RLVLS / 2;
    localparam int WMID  = WNPOT >> WHALF;   // stage-A survivors
    localparam int RMID  = RNPOT >> RHALF;

    // Pick the better of two packed candidates: valid > QoS > older-age,
    // lower index (== left/`a`) on a full tie.
    // Single 8-bit subtract + flat select (was two $signed subtracts + a
    // priority else-if chain). Semantics identical: valid > QoS > older-age,
    // lower index (a) on a full tie. b_older uses one subtract w_d=ag-bg:
    // ag>bg (signed) ⇒ a is newer ⇒ b older ⇒ !w_d[7] & (|w_d).
    function automatic logic [WCW-1:0] wr_best2(input logic [WCW-1:0] a,
                                                input logic [WCW-1:0] b);
        logic av, bv; logic [3:0] aq, bq; logic [7:0] ag, bg, w_d;
        logic b_older, b_wins;
        av = a[WCW-1]; aq = a[WCW-2 -: 4]; ag = a[WSL +: 8];
        bv = b[WCW-1]; bq = b[WCW-2 -: 4]; bg = b[WSL +: 8];
        w_d     = ag - bg;
        b_older = (|w_d) & ~w_d[7];
        b_wins  = (bv & ~av)
                | (av & bv & (bq > aq))
                | (av & bv & (bq == aq) & b_older);
        wr_best2 = b_wins ? b : a;
    endfunction

    function automatic logic [RCW-1:0] rd_best2(input logic [RCW-1:0] a,
                                                input logic [RCW-1:0] b);
        logic av, bv; logic [3:0] aq, bq; logic [7:0] ag, bg, w_d;
        logic b_older, b_wins;
        av = a[RCW-1]; aq = a[RCW-2 -: 4]; ag = a[RSL +: 8];
        bv = b[RCW-1]; bq = b[RCW-2 -: 4]; bg = b[RSL +: 8];
        w_d     = ag - bg;
        b_older = (|w_d) & ~w_d[7];
        b_wins  = (bv & ~av)
                | (av & bv & (bq > aq))
                | (av & bv & (bq == aq) & b_older);
        rd_best2 = b_wins ? b : a;
    endfunction

    // ---- Stage A: fold the first WHALF/RHALF levels (combinational) ----
    // In-place fold is safe: at each level we write red[0..h-1] from
    // red[0..2h-1] and read index 2k >= k. Arrays padded to a power of two
    // with invalid entries so the fold is exactly WLVLS/RLVLS deep.
    logic [WCW-1:0] w_wr_redA [WNPOT];
    logic [RCW-1:0] w_rd_redA [RNPOT];

    always_comb begin
        for (int unsigned i = 0; i < WNPOT; i++)
            w_wr_redA[i] = (i < WR_CAM_DEPTH)
                ? {wr_match_pending_i[i], wr_snap_qos_i[i],
                   wr_snap_age_i[i], WSL'(i)}
                : '0;
        for (int lvl = 0; lvl < WHALF; lvl++)
            for (int k = 0; k < WNPOT/2; k++)
                if (k < (WNPOT >> (lvl+1)))
                    w_wr_redA[k] = wr_best2(w_wr_redA[2*k], w_wr_redA[2*k+1]);
    end

    always_comb begin
        for (int unsigned i = 0; i < RNPOT; i++)
            w_rd_redA[i] = (i < RD_CAM_DEPTH)
                ? {rd_match_pending_i[i], rd_snap_qos_i[i],
                   rd_snap_age_i[i], RSL'(i)}
                : '0;
        for (int lvl = 0; lvl < RHALF; lvl++)
            for (int k = 0; k < RNPOT/2; k++)
                if (k < (RNPOT >> (lvl+1)))
                    w_rd_redA[k] = rd_best2(w_rd_redA[2*k], w_rd_redA[2*k+1]);
    end

    // ---- Midpoint pipeline register: the stage-A survivors ----
    logic [WCW-1:0] r_wr_mid [WMID];
    logic [RCW-1:0] r_rd_mid [RMID];
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int i = 0; i < WMID; i++) r_wr_mid[i] <= '0;
            for (int i = 0; i < RMID; i++) r_rd_mid[i] <= '0;
        end else begin
            for (int i = 0; i < WMID; i++) r_wr_mid[i] <= w_wr_redA[i];
            for (int i = 0; i < RMID; i++) r_rd_mid[i] <= w_rd_redA[i];
        end
    end)

    // ---- Stage B: fold the remaining levels on the registered survivors ----
    logic [WCW-1:0] w_wr_redB [WMID];
    logic [RCW-1:0] w_rd_redB [RMID];

    always_comb begin
        for (int i = 0; i < WMID; i++) w_wr_redB[i] = r_wr_mid[i];
        for (int lvl = 0; lvl < (WLVLS - WHALF); lvl++)
            for (int k = 0; k < WMID/2; k++)
                if (k < (WMID >> (lvl+1)))
                    w_wr_redB[k] = wr_best2(w_wr_redB[2*k], w_wr_redB[2*k+1]);
    end

    always_comb begin
        for (int i = 0; i < RMID; i++) w_rd_redB[i] = r_rd_mid[i];
        for (int lvl = 0; lvl < (RLVLS - RHALF); lvl++)
            for (int k = 0; k < RMID/2; k++)
                if (k < (RMID >> (lvl+1)))
                    w_rd_redB[k] = rd_best2(w_rd_redB[2*k], w_rd_redB[2*k+1]);
    end

    // ---- Stage-B output register: the final winning candidate ----
    logic [WCW-1:0] r_wr_cand;
    logic [RCW-1:0] r_rd_cand;
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_wr_cand <= '0;
            r_rd_cand <= '0;
        end else begin
            r_wr_cand <= w_wr_redB[0];
            r_rd_cand <= w_rd_redB[0];
        end
    end)

    // Decode the registered pick, and RE-VALIDATE against the live
    // match_pending vector: a slot the pipeline picked last cycle may have
    // been freed (b_complete) in the meantime, so gate w_have_* on the slot
    // still being pending. If it went stale we simply stay in S_IDLE and
    // re-pick next cycle from the fresh tree output.
    assign w_wr_pick = r_wr_cand[WSL-1:0];
    assign w_rd_pick = r_rd_cand[RSL-1:0];
    assign w_have_wr = r_wr_cand[WCW-1] && wr_match_pending_i[w_wr_pick];
    assign w_have_rd = r_rd_cand[RCW-1] && rd_match_pending_i[w_rd_pick];

    //=========================================================================
    // W/R arbitration: age-weighted starvation scheme. Per-direction
    // "wait counters" increment while pending and reset on issue. When
    // both directions have pending, whichever has been waiting longer
    // wins. Falls back to a fairness toggle if both ages are equal.
    //
    // Saturating 8-bit ages: under sustained pressure on one side, the
    // counter pins at 0xFF and the other side wins every contention
    // until the OPPOSING age catches up.
    //=========================================================================
    logic [7:0] r_w_age;
    logic [7:0] r_r_age;
    logic       r_arb_prefer_rd;   // fairness toggle for age ties

    logic w_pick_wr_first;
    always_comb begin
        if (w_have_wr && !w_have_rd) w_pick_wr_first = 1'b1;
        else if (!w_have_wr)         w_pick_wr_first = 1'b0;
        // both have pending — choose by age, break ties with toggle.
        else if (r_w_age > r_r_age)  w_pick_wr_first = 1'b1;
        else if (r_r_age > r_w_age)  w_pick_wr_first = 1'b0;
        else                          w_pick_wr_first = !r_arb_prefer_rd;
    end

    //=========================================================================
    // Page-policy initial-state decision: when picking a slot in S_IDLE,
    // figure out whether the bank is open on the right row (skip ACT),
    // open on the wrong row (need PRE then ACT), or closed (just ACT).
    // CLOSE always goes ACT first because xbank_timers auto-precharges
    // on RDA/WRA so the bank is always IDLE between accesses.
    //=========================================================================
    logic [RKW-1:0]       w_pick_rank;
    logic [BKW-1:0]       w_pick_bank;
    logic [ROW_WIDTH-1:0] w_pick_row;
    logic                 w_pick_is_wr;
    always_comb begin
        if (w_pick_wr_first) begin
            w_pick_is_wr = 1'b1;
            w_pick_rank  = wr_snap_rank_i[w_wr_pick];
            w_pick_bank  = wr_snap_bank_i[w_wr_pick];
            w_pick_row   = wr_snap_row_i [w_wr_pick];
        end else begin
            w_pick_is_wr = 1'b0;
            w_pick_rank  = rd_snap_rank_i[w_rd_pick];
            w_pick_bank  = rd_snap_bank_i[w_rd_pick];
            w_pick_row   = rd_snap_row_i [w_rd_pick];
        end
    end

    logic w_row_hit, w_row_miss;
    assign w_row_hit  = bank_row_active_i[w_pick_rank][w_pick_bank]
                     && (bank_open_row_i[w_pick_rank][w_pick_bank] == w_pick_row);
    assign w_row_miss = bank_row_active_i[w_pick_rank][w_pick_bank]
                     && (bank_open_row_i[w_pick_rank][w_pick_bank] != w_pick_row);

    state_e w_initial_state;
    always_comb begin
        if (PAGE_POLICY == 32'(PAGE_POLICY_CLOSE)) begin
            w_initial_state = S_NEED_ACT;
        end else begin
            // OPEN or HAPPY_HYBRID
            if      (w_row_hit)  w_initial_state = S_NEED_RDWR;
            else if (w_row_miss) w_initial_state = S_NEED_PRE;
            else                 w_initial_state = S_NEED_ACT;
        end
    end

    // Per-cycle auto-precharge decision for the current r_pending op
    // (consumed in S_NEED_RDWR).
    logic w_ap_for_rdwr;
    always_comb begin
        unique case (PAGE_POLICY)
            32'(PAGE_POLICY_CLOSE):        w_ap_for_rdwr = 1'b1;
            32'(PAGE_POLICY_OPEN):         w_ap_for_rdwr = 1'b0;
            32'(PAGE_POLICY_HAPPY_HYBRID): w_ap_for_rdwr =
                !predict_open_i[r_pending_rank][r_pending_bank];
            default:                       w_ap_for_rdwr = 1'b1;
        endcase
    end

    //=========================================================================
    // Next-cycle output values — combinational on r_state.
    //=========================================================================
    dram_op_e            w_op;
    logic                w_cmd_valid;
    logic [RKW-1:0]      w_cmd_rank, w_evt_rank;
    logic [BKW-1:0]      w_cmd_bank, w_evt_bank;
    logic [ROW_WIDTH-1:0] w_cmd_row;
    logic [COL_WIDTH-1:0] w_cmd_col;
    logic [BURST_LEN_WIDTH-1:0] w_cmd_len;
    logic [WSL-1:0]      w_cmd_wr_slot, w_wr_issued_slot;
    logic [RSL-1:0]      w_cmd_rd_slot, w_rd_issued_slot;
    logic                w_evt_act, w_evt_rd, w_evt_wr, w_evt_pre, w_evt_ap;
    logic                w_refresh_grant, w_pdn_grant, w_mr_grant;
    logic                w_wr_issued_we, w_rd_issued_we;

    always_comb begin
        // Defaults
        w_op             = OP_NOP;
        w_cmd_valid      = 1'b0;
        w_cmd_rank       = '0;
        w_cmd_bank       = '0;
        w_cmd_row        = '0;
        w_cmd_col        = '0;
        w_cmd_len        = '0;
        w_cmd_wr_slot    = '0;
        w_cmd_rd_slot    = '0;
        w_evt_act        = 1'b0;
        w_evt_rd         = 1'b0;
        w_evt_wr         = 1'b0;
        w_evt_pre        = 1'b0;
        w_evt_ap         = 1'b0;
        w_evt_rank       = '0;
        w_evt_bank       = '0;
        w_refresh_grant  = 1'b0;
        w_pdn_grant      = 1'b0;
        w_mr_grant       = 1'b0;
        w_wr_issued_we   = 1'b0;
        w_wr_issued_slot = '0;
        w_rd_issued_we   = 1'b0;
        w_rd_issued_slot = '0;

        unique case (r_state)
            S_IDLE: begin
                if (init_busy_i) begin
                    // NOP — init_sequencer owns the bus.
                end else if (mr_req_i) begin
                    w_op            = OP_MRS;
                    w_cmd_valid     = 1'b1;
                    w_mr_grant      = cmd_ready_i;
                end else if (refresh_req_i) begin
                    w_op            = OP_REF;
                    w_cmd_valid     = 1'b1;
                    w_refresh_grant = cmd_ready_i;
                end else if (pdn_req_i) begin
                    w_pdn_grant     = 1'b1;
                end
            end

            S_NEED_ACT: begin
                if (bank_act_ready_i[r_pending_rank][r_pending_bank]
                 && tfaw_window_ok_i[r_pending_rank]) begin
                    w_op         = OP_ACT;
                    w_cmd_valid  = 1'b1;
                    w_cmd_rank   = r_pending_rank;
                    w_cmd_bank   = r_pending_bank;
                    w_cmd_row    = r_pending_row;
                    if (cmd_ready_i) begin
                        w_evt_act  = 1'b1;
                        w_evt_rank = r_pending_rank;
                        w_evt_bank = r_pending_bank;
                    end
                end
            end

            S_NEED_PRE: begin
                if (bank_pre_ready_i[r_pending_rank][r_pending_bank]) begin
                    w_op         = OP_PRE;
                    w_cmd_valid  = 1'b1;
                    w_cmd_rank   = r_pending_rank;
                    w_cmd_bank   = r_pending_bank;
                    if (cmd_ready_i) begin
                        w_evt_pre  = 1'b1;
                        w_evt_rank = r_pending_rank;
                        w_evt_bank = r_pending_bank;
                    end
                end
            end

            S_NEED_RDWR: begin
                if (bank_rdwr_ready_i[r_pending_rank][r_pending_bank]) begin
                    // Op selection: WR/RD vs WRA/RDA based on policy +
                    // (HAPPY only) per-bank predictor hint.
                    if (r_pending_is_wr)
                        w_op = w_ap_for_rdwr ? OP_WRA : OP_WR;
                    else
                        w_op = w_ap_for_rdwr ? OP_RDA : OP_RD;
                    w_cmd_valid  = 1'b1;
                    w_cmd_rank   = r_pending_rank;
                    w_cmd_bank   = r_pending_bank;
                    w_cmd_col    = r_pending_col;
                    w_cmd_len    = r_pending_len;
                    w_cmd_wr_slot = r_pending_wr_slot;
                    w_cmd_rd_slot = r_pending_rd_slot;
                    if (cmd_ready_i) begin
                        if (r_pending_is_wr) w_evt_wr = 1'b1;
                        else                 w_evt_rd = 1'b1;
                        w_evt_ap   = w_ap_for_rdwr;
                        w_evt_rank = r_pending_rank;
                        w_evt_bank = r_pending_bank;
                        // Fire issued_we here (on the cmd accept), NOT in
                        // S_DONE. Reason: wr/rd_issued_we_o is registered,
                        // so the strobe reaches the CAM 1 cycle later. If
                        // we fire it in S_DONE, the FSM goes back to S_IDLE
                        // the SAME cycle the CAM observes the strobe, so
                        // the picker re-picks the same slot before
                        // r_issued has propagated. Asserting one cycle
                        // earlier (here, on RDWR accept) makes r_issued
                        // visible to the picker by the time we're back in
                        // S_IDLE.
                        if (r_pending_is_wr) begin
                            w_wr_issued_we   = 1'b1;
                            w_wr_issued_slot = r_pending_wr_slot;
                        end else begin
                            w_rd_issued_we   = 1'b1;
                            w_rd_issued_slot = r_pending_rd_slot;
                        end
                    end
                end
            end

            S_DONE: begin
                // FSM bookkeeping only — issued_we already fired on the
                // RDWR cmd accept above.
            end

            default: ;
        endcase
    end

    //=========================================================================
    // Strict-flop outputs.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            cmd_valid_o      <= 1'b0;
            cmd_op_o         <= OP_NOP;
            cmd_rank_o       <= '0;
            cmd_bank_o       <= '0;
            cmd_row_o        <= '0;
            cmd_col_o        <= '0;
            cmd_len_o        <= '0;
            cmd_wr_slot_o    <= '0;
            cmd_rd_slot_o    <= '0;
            evt_act_o        <= 1'b0;
            evt_rd_o         <= 1'b0;
            evt_wr_o         <= 1'b0;
            evt_pre_o        <= 1'b0;
            evt_ap_o         <= 1'b0;
            evt_rank_o       <= '0;
            evt_bank_o       <= '0;
            refresh_grant_o  <= 1'b0;
            pdn_grant_o      <= 1'b0;
            mr_grant_o       <= 1'b0;
            wr_issued_we_o   <= 1'b0;
            wr_issued_slot_o <= '0;
            rd_issued_we_o   <= 1'b0;
            rd_issued_slot_o <= '0;
            q_rank_o         <= '0;
            q_bank_o         <= '0;
            q_row_o          <= '0;
        end else begin
            cmd_valid_o      <= w_cmd_valid;
            cmd_op_o         <= w_op;
            cmd_rank_o       <= w_cmd_rank;
            cmd_bank_o       <= w_cmd_bank;
            cmd_row_o        <= w_cmd_row;
            cmd_col_o        <= w_cmd_col;
            cmd_len_o        <= w_cmd_len;
            cmd_wr_slot_o    <= w_cmd_wr_slot;
            cmd_rd_slot_o    <= w_cmd_rd_slot;
            evt_act_o        <= w_evt_act;
            evt_rd_o         <= w_evt_rd;
            evt_wr_o         <= w_evt_wr;
            evt_pre_o        <= w_evt_pre;
            evt_ap_o         <= w_evt_ap;
            evt_rank_o       <= w_evt_rank;
            evt_bank_o       <= w_evt_bank;
            refresh_grant_o  <= w_refresh_grant;
            pdn_grant_o      <= w_pdn_grant;
            mr_grant_o       <= w_mr_grant;
            wr_issued_we_o   <= w_wr_issued_we;
            wr_issued_slot_o <= w_wr_issued_slot;
            rd_issued_we_o   <= w_rd_issued_we;
            rd_issued_slot_o <= w_rd_issued_slot;
            q_rank_o         <= '0;
            q_bank_o         <= '0;
            q_row_o          <= '0;
        end
    end)

    //=========================================================================
    // Sequential FSM
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state           <= S_IDLE;
            r_pending_is_wr   <= 1'b0;
            r_pending_wr_slot <= '0;
            r_pending_rd_slot <= '0;
            r_pending_rank    <= '0;
            r_pending_bank    <= '0;
            r_pending_row     <= '0;
            r_pending_col     <= '0;
            r_pending_len     <= '0;
            r_arb_prefer_rd   <= 1'b0;   // first contention picks WR
            r_w_age           <= 8'd0;
            r_r_age           <= 8'd0;
        end else begin
            // Age accumulators — increment each cycle while pending,
            // reset when there's nothing pending on that side. Saturating
            // at 0xFF so a runaway side stays "max-old" but doesn't roll.
            if (w_have_wr && r_w_age != 8'hFF) r_w_age <= r_w_age + 8'd1;
            else if (!w_have_wr)               r_w_age <= 8'd0;
            if (w_have_rd && r_r_age != 8'hFF) r_r_age <= r_r_age + 8'd1;
            else if (!w_have_rd)               r_r_age <= 8'd0;

            unique case (r_state)
                S_IDLE: begin
                    if (init_busy_i || mr_req_i || refresh_req_i || pdn_req_i) begin
                        // Stay IDLE; output logic emits the injection cmd.
                    end else if (w_pick_wr_first) begin
                        r_pending_is_wr   <= 1'b1;
                        r_pending_wr_slot <= w_wr_pick;
                        r_pending_rank    <= w_pick_rank;
                        r_pending_bank    <= w_pick_bank;
                        r_pending_row     <= w_pick_row;
                        r_pending_col     <= wr_snap_col_i [w_wr_pick];
                        r_pending_len     <= wr_snap_len_i [w_wr_pick];
                        r_state           <= w_initial_state;
                    end else if (w_have_rd) begin
                        r_pending_is_wr   <= 1'b0;
                        r_pending_rd_slot <= w_rd_pick;
                        r_pending_rank    <= w_pick_rank;
                        r_pending_bank    <= w_pick_bank;
                        r_pending_row     <= w_pick_row;
                        r_pending_col     <= rd_snap_col_i [w_rd_pick];
                        r_pending_len     <= rd_snap_len_i [w_rd_pick];
                        r_state           <= w_initial_state;
                    end
                end

                S_NEED_PRE: begin
                    if (w_cmd_valid && cmd_ready_i) begin
                        r_state <= S_NEED_ACT;
                    end
                end

                S_NEED_ACT: begin
                    if (w_cmd_valid && cmd_ready_i) begin
                        r_state <= S_NEED_RDWR;
                    end
                end

                S_NEED_RDWR: begin
                    if (w_cmd_valid && cmd_ready_i) begin
                        r_state <= S_DONE;
                    end
                end

                S_DONE: begin
                    r_state         <= S_IDLE;
                    // Toggle fairness bit for age ties.
                    r_arb_prefer_rd <= ~r_arb_prefer_rd;
                    // Reset the AGE of the side that just issued; the
                    // other side keeps accumulating.
                    if (r_pending_is_wr) r_w_age <= 8'd0;
                    else                 r_r_age <= 8'd0;
                end

                default: r_state <= S_IDLE;
            endcase
        end
    end)

    // wr_match_rowhit_i / rd_match_rowhit_i are not yet consumed — the
    // current scheduler uses per-slot snapshot rank/bank/row from
    // wr_snap_* / rd_snap_* and computes hits inline. The match_rowhit
    // signals are useful for "prefer row-hit slots" arbitration which
    // is a future enhancement (HAS §3.2.3).
    wire unused_v2 = |{ wr_match_rowhit_i, rd_match_rowhit_i };

endmodule : scheduler
