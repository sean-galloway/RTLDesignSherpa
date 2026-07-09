// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: scheduler
// Purpose: Arbiter at the heart of the controller core. Each cycle,
//          decide what to issue on the DFI command bus.
//
//          v2 issue-per-clock, bank-parallel design:
//            Rather than one global op-in-flight FSM (ACT->RDWR serialized,
//            ~4 cyc/op, no bank parallelism), each DRAM bank has its own tiny
//            "in-flight op" machine, and a shallow per-cycle arbiter picks one
//            bank whose next-needed command is SAFE now (per the xbank_timers
//            safe-timer inputs) to drive this cycle. While bank A waits tRCD
//            after its ACT, the arbiter issues bank B's ACT / bank C's RD, etc.
//            -> command-per-cycle across banks + intra-page batching.
//
//          Issue priority (high -> low):
//            1. init_busy_i      -> forward init_sequencer command (owns bus)
//            2. mr_req_i         -> MRS (mode-register write)
//            3. refresh_req_i    -> grant + REF (forces all bank phases re-ACT)
//            4. pdn_req_i        -> grant (CKE drop handled by powerdown_ctrl)
//            5. bank arbiter     -> one bank's ACT / PRE / RD / WR / RDA / WRA
//            6. else             -> NOP
//
//          Feedback-latency discipline (the reason a stateless per-cycle
//          picker fails here): xbank_timers' ready/row-state outputs are
//          registered, and evt_* is registered, so a just-issued command is
//          NOT reflected in the timers for 2 cycles. Each bank machine tracks
//          its own phase LOCALLY (ACT issued -> next is RD/WR), so it never
//          re-derives "needs ACT" from the stale bank_row_active. Only the
//          INITIAL phase (set when an op is first assigned to a free/settled
//          bank) reads bank_row_active/open_row. Under CLOSE we always ACT
//          first and gate on bank_act_ready, which correctly waits out the
//          auto-precharge, so a stale row_active can never mis-issue.
//
//          Bank machine phases:
//            PH_PRE  : row miss (open page) -> wait bank_pre_ready, issue PRE
//            PH_ACT  : bank idle / closed   -> wait bank_act_ready+tFAW, ACT
//            PH_RDWR : row open             -> wait bank_rdwr_ready, RD/WR(A)
//          ACT/PRE only advance the phase; RD/WR retires the CAM slot.
//
//          Page policy (runtime cfg_page_policy_i, PAGE_POLICY = reset default):
//            CLOSE       — every column command is RDA/WRA (auto-pre); initial
//                          phase always PH_ACT. No row-hit reuse.
//            OPEN        — row-hit slots skip ACT (plain RD/WR); row-miss slots
//                          PRE -> ACT -> RD/WR. Banks stay open until evicted.
//            HAPPY_HYBRID— page_predictor's per-bank predict_open hint decides
//                          the auto-precharge bit on each column command.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scheduler
    import pumice_pkg::*;
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
    // v3 pre-pull: expose the pending write early + gate the WR command on the
    // sequencer's wr_data_ready so wrdata is staged by command time.
    parameter bit PREPULL_EN      = 1'b0,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- runtime page policy (REFRESH_TUNING.page_policy_or) -----
    // Encoding: 0 = use PAGE_POLICY param (reset default), 1 = OPEN,
    // 2 = CLOSE, 3 = HAPPY_HYBRID. Selected LIVE at runtime; the PAGE_POLICY
    // parameter is now only the power-on default (no compile-time policy lock).
    input  logic [1:0]                 cfg_page_policy_i,

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

    // ----- pre-pull: expose the pending write early + gate on data-ready -----
    output logic                       wr_prepull_valid_o,
    output logic [WSL-1:0]             wr_prepull_slot_o,
    output logic [BURST_LEN_WIDTH-1:0] wr_prepull_len_o,
    input  logic                       wr_data_ready_i,

    // ----- init-sequencer command injection (issued while init_busy_i) -----
    // The init_sequencer drives DRAM bring-up commands (PRECHARGE_ALL /
    // AUTO_REFRESH / MRS) that the scheduler forwards to dfi_cmd_formatter
    // while init owns the bus. MRS MR-data rides the wide cmd_row path
    // (COL_WIDTH is too narrow for MR0=0x532's bit-10).
    input  logic                       init_cmd_valid_i,
    input  dram_op_e                   init_cmd_op_i,
    input  logic [BKW-1:0]             init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]       init_cmd_row_i,

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
    // Per-bank in-flight op machine. One op in flight per bank; NB_TOT banks
    // run in parallel. Phase advances LOCALLY on issue (immune to the 2-cycle
    // timer feedback latency).
    //=========================================================================
    localparam int NB_TOT = NUM_RANKS * NUM_BANKS;
    localparam int BFW    = (NB_TOT > 1) ? $clog2(NB_TOT) : 1;
    localparam int SLW    = (WSL > RSL) ? WSL : RSL;   // common slot-index width

    typedef enum logic [1:0] {
        PH_PRE  = 2'd0,
        PH_ACT  = 2'd1,
        PH_RDWR = 2'd2
    } phase_e;

    phase_e                     r_pphase [NB_TOT];
    logic                       r_pv     [NB_TOT];   // pending valid
    logic                       r_pwr    [NB_TOT];   // is-write
    logic [SLW-1:0]             r_pslot  [NB_TOT];   // CAM slot (dir by r_pwr)
    logic [ROW_WIDTH-1:0]       r_prow   [NB_TOT];
    logic [COL_WIDTH-1:0]       r_pcol   [NB_TOT];
    logic [BURST_LEN_WIDTH-1:0] r_plen   [NB_TOT];
    logic [3:0]                 r_pqos   [NB_TOT];
    logic [7:0]                 r_page   [NB_TOT];

    // 2-deep just-issued shadow. issued_we -> CAM match_pending drop is 2 cyc
    // (both registered), so a just-retired slot is excluded from re-assignment
    // for 2 cycles until match_pending reflects the retire (else the tournament
    // re-picks it -> double issue).
    logic          r_wr_ji_v [2];
    logic [WSL-1:0] r_wr_ji_s [2];
    logic          r_rd_ji_v [2];
    logic [RSL-1:0] r_rd_ji_s [2];

    // Command-hold lock. The DFI command bus is a valid/ready handshake
    // (cmd_ready_i can be low for several cycles), and the presented command
    // MUST stay stable until accepted. Once a bank command is presented but
    // not yet accepted, lock the arbiter to that bank so the per-cycle winner
    // cannot switch mid-handshake (which would drop the write -> corruption).
    logic           r_lock_v;
    logic [BFW-1:0] r_lock_f;

    // Flat bank index helper: f = rank*NUM_BANKS + bank (== bank when 1 rank).
    function automatic int unsigned flat_of(input int unsigned rk,
                                             input int unsigned bk);
        flat_of = (NUM_RANKS > 1) ? (rk * NUM_BANKS + bk) : bk;
    endfunction

    // Arbiter comparator: candidate (qa,aga) strictly beats incumbent (qb,agb)
    // on higher QoS, else older age (signed-diff wraparound-safe). Ties keep
    // the incumbent (lower flat index, since we scan ascending).
    function automatic logic bank_better(input logic [3:0] qa, input logic [7:0] aga,
                                          input logic [3:0] qb, input logic [7:0] agb);
        logic [7:0] d; logic older;
        d     = aga - agb;
        older = (|d) & ~d[7];
        bank_better = (qa > qb) | ((qa == qb) & older);
    endfunction

    //=========================================================================
    // QoS-aware slot picker (unchanged 2-stage pipelined tournament from the
    // FSM design — proven to close at 100 MHz). Highest AXI QoS wins; QoS ties
    // -> oldest age (signed-diff wraparound-safe); full tie -> lower slot index.
    // Only the LEAF VALIDITY changes: a slot is a candidate only if it is
    // pending, its bank is FREE (no op in flight -> assignable), and it is not
    // in the just-issued shadow.
    //=========================================================================
    localparam int WCW   = 1 + 4 + 8 + WSL;             // WR candidate width
    localparam int RCW   = 1 + 4 + 8 + RSL;             // RD candidate width
    localparam int WLVLS = (WR_CAM_DEPTH > 1) ? $clog2(WR_CAM_DEPTH) : 0;
    localparam int RLVLS = (RD_CAM_DEPTH > 1) ? $clog2(RD_CAM_DEPTH) : 0;
    localparam int WNPOT = 1 << WLVLS;
    localparam int RNPOT = 1 << RLVLS;
    localparam int WHALF = WLVLS / 2;
    localparam int RHALF = RLVLS / 2;
    localparam int WMID  = WNPOT >> WHALF;
    localparam int RMID  = RNPOT >> RHALF;

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

    // Leaf validity masks: bank-busy (op in flight on that bank) + just-issued.
    logic [WR_CAM_DEPTH-1:0] w_wr_leaf_ok;
    logic [RD_CAM_DEPTH-1:0] w_rd_leaf_ok;
    always_comb begin
        for (int unsigned i = 0; i < WR_CAM_DEPTH; i++) begin
            automatic int unsigned bf = flat_of(int'(wr_snap_rank_i[i]), int'(wr_snap_bank_i[i]));
            automatic logic ji = (r_wr_ji_v[0] && r_wr_ji_s[0] == WSL'(i))
                               || (r_wr_ji_v[1] && r_wr_ji_s[1] == WSL'(i));
            w_wr_leaf_ok[i] = wr_match_pending_i[i] && !r_pv[bf] && !ji;
        end
        for (int unsigned i = 0; i < RD_CAM_DEPTH; i++) begin
            // Reads: do NOT mask on bank-busy — the tournament must always
            // surface the GLOBALLY oldest pending read so a younger read on a
            // free bank can never be assigned ahead of it. Bank-free is enforced
            // at assignment (!r_pv[w_asg_f]) and one-read-in-flight
            // (!w_any_read_if) keeps reads issuing strictly in AR order.
            automatic logic ji = (r_rd_ji_v[0] && r_rd_ji_s[0] == RSL'(i))
                               || (r_rd_ji_v[1] && r_rd_ji_s[1] == RSL'(i));
            w_rd_leaf_ok[i] = rd_match_pending_i[i] && !ji;
        end
    end

    // ---- Stage A: fold the first WHALF/RHALF levels (combinational) ----
    logic [WCW-1:0] w_wr_redA [WNPOT];
    logic [RCW-1:0] w_rd_redA [RNPOT];

    always_comb begin
        for (int unsigned i = 0; i < WNPOT; i++)
            w_wr_redA[i] = (i < WR_CAM_DEPTH)
                ? {w_wr_leaf_ok[i], wr_snap_qos_i[i],
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
                ? {w_rd_leaf_ok[i], rd_snap_qos_i[i],
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

    // Decode the registered pick and re-validate against the LIVE leaf mask
    // (a slot picked last cycle may have been freed / its bank filled since).
    logic           w_have_wr, w_have_rd;
    logic [WSL-1:0] w_wr_pick;
    logic [RSL-1:0] w_rd_pick;
    assign w_wr_pick = r_wr_cand[WSL-1:0];
    assign w_rd_pick = r_rd_cand[RSL-1:0];
    assign w_have_wr = r_wr_cand[WCW-1] && w_wr_leaf_ok[w_wr_pick];
    assign w_have_rd = r_rd_cand[RCW-1] && w_rd_leaf_ok[w_rd_pick];

    //=========================================================================
    // W/R direction arbitration for the assignment source: age-weighted
    // starvation scheme. Whichever direction has waited longer is assigned
    // first; fairness toggle breaks age ties.
    //=========================================================================
    logic [7:0] r_w_age;
    logic [7:0] r_r_age;
    logic       r_arb_prefer_rd;

    logic w_pick_wr_first;
    always_comb begin
        if (w_have_wr && !w_have_rd) w_pick_wr_first = 1'b1;
        else if (!w_have_wr)         w_pick_wr_first = 1'b0;
        else if (r_w_age > r_r_age)  w_pick_wr_first = 1'b1;
        else if (r_r_age > r_w_age)  w_pick_wr_first = 1'b0;
        else                          w_pick_wr_first = !r_arb_prefer_rd;
    end

    //=========================================================================
    // The single "global best assignable op" this cycle (metadata for the
    // pick, used only at assignment into a free bank machine).
    //=========================================================================
    logic                       w_asg_have;
    logic                       w_asg_is_wr;
    logic [RKW-1:0]             w_asg_rank;
    logic [BKW-1:0]             w_asg_bank;
    logic [ROW_WIDTH-1:0]       w_asg_row;
    logic [COL_WIDTH-1:0]       w_asg_col;
    logic [BURST_LEN_WIDTH-1:0] w_asg_len;
    logic [SLW-1:0]             w_asg_slot;
    logic [3:0]                 w_asg_qos;
    logic [7:0]                 w_asg_age;
    always_comb begin
        w_asg_have  = w_have_wr || w_have_rd;
        w_asg_is_wr = w_pick_wr_first;
        if (w_pick_wr_first) begin
            w_asg_rank = wr_snap_rank_i[w_wr_pick];
            w_asg_bank = wr_snap_bank_i[w_wr_pick];
            w_asg_row  = wr_snap_row_i [w_wr_pick];
            w_asg_col  = wr_snap_col_i [w_wr_pick];
            w_asg_len  = wr_snap_len_i [w_wr_pick];
            w_asg_slot = SLW'(w_wr_pick);
            w_asg_qos  = wr_snap_qos_i [w_wr_pick];
            w_asg_age  = wr_snap_age_i [w_wr_pick];
        end else begin
            w_asg_rank = rd_snap_rank_i[w_rd_pick];
            w_asg_bank = rd_snap_bank_i[w_rd_pick];
            w_asg_row  = rd_snap_row_i [w_rd_pick];
            w_asg_col  = rd_snap_col_i [w_rd_pick];
            w_asg_len  = rd_snap_len_i [w_rd_pick];
            w_asg_slot = SLW'(w_rd_pick);
            w_asg_qos  = rd_snap_qos_i [w_rd_pick];
            w_asg_age  = rd_snap_age_i [w_rd_pick];
        end
    end

    // Effective page policy: runtime CSR overrides; 0 = PAGE_POLICY reset
    // default. CSR encoding is offset by 1 (1=OPEN,2=CLOSE,3=HYBRID) vs the
    // pumice_pkg enum (OPEN=0, CLOSE=1, HYBRID=2).
    logic [1:0] w_eff_policy;
    always_comb begin
        if (cfg_page_policy_i == 2'd0) w_eff_policy = PAGE_POLICY[1:0];
        else                           w_eff_policy = cfg_page_policy_i - 2'd1;
    end

    // Row hit/miss for the op being assigned (its bank is free/settled).
    logic w_asg_row_hit, w_asg_row_miss;
    assign w_asg_row_hit  = bank_row_active_i[w_asg_rank][w_asg_bank]
                         && (bank_open_row_i[w_asg_rank][w_asg_bank] == w_asg_row);
    assign w_asg_row_miss = bank_row_active_i[w_asg_rank][w_asg_bank]
                         && (bank_open_row_i[w_asg_rank][w_asg_bank] != w_asg_row);

    // Initial phase for a newly-assigned op.
    phase_e w_asg_phase;
    always_comb begin
        if (w_eff_policy == 2'(PAGE_POLICY_CLOSE)) begin
            w_asg_phase = PH_ACT;                       // always ACT first
        end else begin
            if      (w_asg_row_hit)  w_asg_phase = PH_RDWR;
            else if (w_asg_row_miss) w_asg_phase = PH_PRE;
            else                     w_asg_phase = PH_ACT;
        end
    end

    // Any bank machine currently occupied? Used to quiesce before a
    // refresh/MRS: those commands need all banks idle (JEDEC), and — unlike
    // the old single-op FSM which only granted refresh between ops — the
    // bank-parallel issuer could otherwise grant refresh while a column op is
    // mid ACT->RDWR, interrupting its data transfer and corrupting it.
    logic w_any_pv;
    always_comb begin
        w_any_pv = 1'b0;
        for (int unsigned f = 0; f < NB_TOT; f++)
            if (r_pv[f]) w_any_pv = 1'b1;
    end

    // A refresh/MRS request is pending: stop launching NEW ops so the in-flight
    // ones drain, then grant once fully quiesced.
    logic w_quiesce_req;
    assign w_quiesce_req = refresh_req_i || mr_req_i || pdn_req_i;

    // Read ordering: the read return path (rd_cl_aligner + axi_intake R-emit)
    // emits strictly in RD-issue order and the host matches the Nth R burst to
    // the Nth AR (per id). Bank-parallel read issue would reorder same-id reads
    // (a read whose bank readies first jumps an older read on a busier bank) ->
    // the in-order R path mis-pairs data. So keep at most ONE read op in flight:
    // a read is assigned only when no read is already in a bank machine. With
    // the oldest-first tournament (and the read leaf below NOT masking bank-busy,
    // so the GLOBAL oldest read is always the one surfaced) this forces reads to
    // issue strictly in AR (age) order. Writes stay fully bank-parallel (each
    // carries its own address, so their issue order is immaterial to data).
    logic w_any_read_if;
    always_comb begin
        w_any_read_if = 1'b0;
        for (int unsigned f = 0; f < NB_TOT; f++)
            if (r_pv[f] && !r_pwr[f]) w_any_read_if = 1'b1;
    end

    // Do-assign: a valid best op whose bank machine is free — but NOT while a
    // refresh/MRS is pending (let the banks drain to idle first), and a READ
    // only when no read is already in flight (in-order read discipline).
    logic          w_do_assign;
    int unsigned   w_asg_f;
    always_comb begin
        w_asg_f     = flat_of(int'(w_asg_rank), int'(w_asg_bank));
        w_do_assign = w_asg_have && !r_pv[w_asg_f] && !w_quiesce_req
                   && (w_asg_is_wr || !w_any_read_if);
    end

    //=========================================================================
    // Per-bank request: for each bank with a pending op, the command it wants
    // next and whether the safe timer allows issuing it THIS cycle.
    //=========================================================================
    logic     [NB_TOT-1:0] w_bank_req;
    dram_op_e              w_bank_op  [NB_TOT];
    logic     [NB_TOT-1:0] w_bank_ap;
    always_comb begin
        for (int unsigned f = 0; f < NB_TOT; f++) begin
            automatic int unsigned rk = (NUM_RANKS > 1) ? (f / NUM_BANKS) : 0;
            automatic int unsigned bk = (NUM_RANKS > 1) ? (f % NUM_BANKS) : f;
            automatic logic ap;
            w_bank_op[f] = OP_NOP;
            w_bank_ap[f] = 1'b0;
            w_bank_req[f] = 1'b0;
            if (r_pv[f]) begin
                unique case (r_pphase[f])
                    PH_PRE: begin
                        w_bank_op[f]  = OP_PRE;
                        w_bank_req[f] = bank_pre_ready_i[rk][bk];
                    end
                    PH_ACT: begin
                        w_bank_op[f]  = OP_ACT;
                        w_bank_req[f] = bank_act_ready_i[rk][bk]
                                     && tfaw_window_ok_i[rk];
                    end
                    PH_RDWR: begin
                        unique case (w_eff_policy)
                            2'(PAGE_POLICY_CLOSE):        ap = 1'b1;
                            2'(PAGE_POLICY_OPEN):         ap = 1'b0;
                            2'(PAGE_POLICY_HAPPY_HYBRID): ap = !predict_open_i[rk][bk];
                            default:                       ap = 1'b1;
                        endcase
                        w_bank_ap[f]  = ap;
                        w_bank_op[f]  = r_pwr[f] ? (ap ? OP_WRA : OP_WR)
                                                 : (ap ? OP_RDA : OP_RD);
                        w_bank_req[f] = bank_rdwr_ready_i[rk][bk]
                                     && (!(PREPULL_EN && r_pwr[f]) || wr_data_ready_i);
                    end
                    default: ;
                endcase
            end
        end
    end

    //=========================================================================
    // Bank arbiter: choose the requesting bank with highest QoS, then oldest
    // age, then lowest flat index (a strictly-better test keeps the lower
    // index on ties).
    //=========================================================================
    logic        w_any_req;
    int unsigned w_win;
    always_comb begin
        w_any_req = 1'b0;
        w_win     = 0;
        for (int unsigned f = 0; f < NB_TOT; f++) begin
            if (w_bank_req[f]) begin
                if (!w_any_req) begin
                    w_any_req = 1'b1;
                    w_win     = f;
                end else if (bank_better(r_pqos[f], r_page[f],
                                         r_pqos[w_win], r_page[w_win])) begin
                    w_win = f;
                end
            end
        end
        // Command-hold: while a presented command awaits acceptance, force the
        // winner back to the locked bank so the DFI command bus sees a stable
        // command across the whole valid/ready handshake.
        if (r_lock_v) begin
            w_any_req = 1'b1;
            w_win     = int'(r_lock_f);
        end
    end

    //=========================================================================
    // Issue mux (combinational). Priority: init > MR > refresh > pdn > bank.
    // While injection owns the bus, no bank command is issued (bank machine
    // state is preserved; a refresh forces all bank phases back to PH_ACT).
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

    logic                w_inject;    // injection owns the bus this cycle
    logic                w_bank_go;   // a bank command is issued this cycle
    logic                w_bank_acc;  // bank command accepted (cmd_ready)

    always_comb begin
        automatic int unsigned wrk = (NUM_RANKS > 1) ? (w_win / NUM_BANKS) : 0;
        automatic int unsigned wbk = (NUM_RANKS > 1) ? (w_win % NUM_BANKS) : w_win;

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
        w_inject         = 1'b0;
        w_bank_go        = 1'b0;
        w_bank_acc       = 1'b0;

        // Injection (init/MR/refresh/pdn) owns the bus, but must NOT preempt a
        // bank command that has already been presented and is awaiting accept
        // (r_lock_v) — that would drop the in-flight write.
        if (!r_lock_v && init_busy_i) begin
            w_inject = 1'b1;
            if (init_cmd_valid_i) begin
                w_op        = init_cmd_op_i;
                w_cmd_valid = 1'b1;
                w_cmd_bank  = init_cmd_bank_i;
                w_cmd_row   = init_cmd_row_i;
            end
        // MRS / refresh / pdn are granted ONLY when all banks are idle
        // (!w_any_pv). While such a request is pending but banks are still
        // busy, these conditions are false so bank commands fall through and
        // issue — draining the in-flight ops (new ops are held off by
        // w_quiesce_req in w_do_assign). This restores the old FSM's invariant
        // that refresh/MRS never interrupt a column op mid-transfer.
        end else if (!r_lock_v && mr_req_i && !w_any_pv) begin
            w_inject    = 1'b1;
            w_op        = OP_MRS;
            w_cmd_valid = 1'b1;
            w_mr_grant  = cmd_ready_i;
        end else if (!r_lock_v && refresh_req_i && !w_any_pv) begin
            w_inject        = 1'b1;
            w_op            = OP_REF;
            w_cmd_valid     = 1'b1;
            w_refresh_grant = cmd_ready_i;
        end else if (!r_lock_v && pdn_req_i && !w_any_pv) begin
            w_inject     = 1'b1;
            w_pdn_grant  = 1'b1;
        end else if (w_any_req) begin
            // ----- bank command -----
            w_bank_go    = 1'b1;
            w_op         = w_bank_op[w_win];
            w_cmd_valid  = 1'b1;
            w_cmd_rank   = RKW'(wrk);
            w_cmd_bank   = BKW'(wbk);
            w_cmd_row    = r_prow[w_win];
            w_cmd_col    = r_pcol[w_win];
            w_cmd_len    = r_plen[w_win];
            w_bank_acc   = cmd_ready_i;
            if (r_pwr[w_win]) w_cmd_wr_slot = r_pslot[w_win][WSL-1:0];
            else              w_cmd_rd_slot = r_pslot[w_win][RSL-1:0];
            if (cmd_ready_i) begin
                w_evt_rank = RKW'(wrk);
                w_evt_bank = BKW'(wbk);
                unique case (r_pphase[w_win])
                    PH_PRE:  w_evt_pre = 1'b1;
                    PH_ACT:  w_evt_act = 1'b1;
                    PH_RDWR: begin
                        w_evt_ap = w_bank_ap[w_win];
                        if (r_pwr[w_win]) begin
                            w_evt_wr         = 1'b1;
                            w_wr_issued_we   = 1'b1;
                            w_wr_issued_slot = r_pslot[w_win][WSL-1:0];
                        end else begin
                            w_evt_rd         = 1'b1;
                            w_rd_issued_we   = 1'b1;
                            w_rd_issued_slot = r_pslot[w_win][RSL-1:0];
                        end
                    end
                    default: ;
                endcase
            end
        end
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
    // Sequential: per-bank machines, assignment, W/R age, just-issued shadow.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int i = 0; i < NB_TOT; i++) begin
                r_pphase[i] <= PH_ACT;
                r_pv[i]     <= 1'b0;
                r_pwr[i]    <= 1'b0;
                r_pslot[i]  <= '0;
                r_prow[i]   <= '0;
                r_pcol[i]   <= '0;
                r_plen[i]   <= '0;
                r_pqos[i]   <= '0;
                r_page[i]   <= '0;
            end
            r_wr_ji_v[0] <= 1'b0; r_wr_ji_v[1] <= 1'b0;
            r_rd_ji_v[0] <= 1'b0; r_rd_ji_v[1] <= 1'b0;
            r_wr_ji_s[0] <= '0;   r_wr_ji_s[1] <= '0;
            r_rd_ji_s[0] <= '0;   r_rd_ji_s[1] <= '0;
            r_arb_prefer_rd <= 1'b0;
            r_w_age <= 8'd0;
            r_r_age <= 8'd0;
            r_lock_v <= 1'b0;
            r_lock_f <= '0;
        end else begin
            // ----- command-hold lock: set when a bank command is presented
            // but not accepted; clear on accept (or when nothing is presented).
            if (w_bank_go && !cmd_ready_i) begin
                r_lock_v <= 1'b1;
                r_lock_f <= BFW'(w_win);
            end else begin
                r_lock_v <= 1'b0;
            end
            // ----- W/R starvation ages (assignment-source fairness) -----
            if (w_have_wr && r_w_age != 8'hFF) r_w_age <= r_w_age + 8'd1;
            else if (!w_have_wr)               r_w_age <= 8'd0;
            if (w_have_rd && r_r_age != 8'hFF) r_r_age <= r_r_age + 8'd1;
            else if (!w_have_rd)               r_r_age <= 8'd0;

            // ----- just-issued shadow: shift stage0 -> stage1; load stage0 -----
            r_wr_ji_v[1] <= r_wr_ji_v[0];  r_wr_ji_s[1] <= r_wr_ji_s[0];
            r_rd_ji_v[1] <= r_rd_ji_v[0];  r_rd_ji_s[1] <= r_rd_ji_s[0];
            r_wr_ji_v[0] <= 1'b0;
            r_rd_ji_v[0] <= 1'b0;

            // ----- bank machine advance on the accepted bank command -----
            if (w_bank_go && w_bank_acc) begin
                unique case (r_pphase[w_win])
                    PH_PRE:  r_pphase[w_win] <= PH_ACT;
                    PH_ACT:  r_pphase[w_win] <= PH_RDWR;
                    PH_RDWR: begin
                        // Retire: free the bank; push slot into the shadow so
                        // the tournament can't re-pick it before match_pending
                        // drops. Reset the issuing direction's starvation age.
                        r_pv[w_win] <= 1'b0;
                        if (r_pwr[w_win]) begin
                            r_wr_ji_v[0] <= 1'b1;
                            r_wr_ji_s[0] <= r_pslot[w_win][WSL-1:0];
                            r_w_age      <= 8'd0;
                        end else begin
                            r_rd_ji_v[0] <= 1'b1;
                            r_rd_ji_s[0] <= r_pslot[w_win][RSL-1:0];
                            r_r_age      <= 8'd0;
                        end
                        r_arb_prefer_rd <= ~r_arb_prefer_rd;
                    end
                    default: ;
                endcase
            end

            // NOTE: refresh does NOT force in-flight bank phases to re-ACT.
            // xbank_timers does not precharge a bank on REF (REF is rank-level),
            // so a bank left ACTIVE stays ACTIVE in the timer model; an in-flight
            // PH_RDWR op correctly resumes on the still-open row after the REF
            // (matching the proven single-op FSM behavior). Forcing PH_ACT here
            // would wait on bank_act_ready (needs IDLE) forever -> wedge.

            // ----- assignment: latch the global best op into its free bank.
            // Guarded by !r_pv so a bank retiring THIS cycle (r_pv still 1) is
            // naturally deferred to next cycle. -----
            if (w_do_assign) begin
                r_pv[w_asg_f]     <= 1'b1;
                r_pwr[w_asg_f]    <= w_asg_is_wr;
                r_pslot[w_asg_f]  <= w_asg_slot;
                r_prow[w_asg_f]   <= w_asg_row;
                r_pcol[w_asg_f]   <= w_asg_col;
                r_plen[w_asg_f]   <= w_asg_len;
                r_pqos[w_asg_f]   <= w_asg_qos;
                r_page[w_asg_f]   <= w_asg_age;
                r_pphase[w_asg_f] <= w_asg_phase;
            end
        end
    end)

    // wr_match_rowhit_i / rd_match_rowhit_i are not consumed — row hit/miss is
    // computed inline from the snapshot rank/bank/row vs bank_open_row_i.
    wire unused_v2 = |{ wr_match_rowhit_i, rd_match_rowhit_i };

    //=========================================================================
    // Pre-pull: expose the arbiter-winning write (heading to its RD/WR issue)
    // so the sequencer can stage its data ahead of the command.
    //=========================================================================
    assign wr_prepull_valid_o = PREPULL_EN && w_any_req && r_pv[w_win]
                             && r_pwr[w_win] && (r_pphase[w_win] == PH_RDWR);
    assign wr_prepull_slot_o  = r_pslot[w_win][WSL-1:0];
    assign wr_prepull_len_o   = r_plen[w_win];




endmodule : scheduler
