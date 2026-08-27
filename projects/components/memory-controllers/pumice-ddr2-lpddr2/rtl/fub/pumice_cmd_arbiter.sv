// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_cmd_arbiter
// Purpose: The command arbiter for the pumice scheduler layer. Each cycle it
//          picks ONE abstract DRAM command and pushes it into the scheduler->DFI
//          command interface. PHY/nphases-agnostic; single-issue. JEDEC timing
//          is enforced via the per-bank (pumice_bank_timers) and global
//          (global_timers) readiness inputs.
//
// The arbiter reads the CAMs' per-entry state as flat REGISTERED vectors
// ({valid,bank,row,col,age} indexed by entry) and does the match + argmax
// itself. No sched-lookup query round-trip into the CAMs, and — crucially —
// it can ACTIVATE MANY BANKS IN PARALLEL: the fallback opens the oldest pending
// op's row among ANY idle+ready bank, not just the single global-oldest bank.
// That bank-parallel activation is what removes the per-transaction bubble
// (previously bank N sat through its whole tRCD before bank N+1 was even
// activated, serializing every access to full ACT->data latency).
//
// Priority per cycle:
//   1. init      : !init_done -> forward the init_sequencer command.
//   2. refresh   : refresh_req -> PRE active banks (one/cycle), then REF+grant.
//   3. column    : row-hit RD/WR to an open, tRCD-met row (READ-priority;
//                  OLDEST CAM age tie-break). Streams at tCCD rate.
//   4. activate  : oldest pending op whose bank is idle+act-ready -> ACT it.
//                  Scans ALL entries, so successive cycles open DIFFERENT banks
//                  (their tRCDs overlap) => no activate bubble.
//   5. precharge : oldest pending op whose bank is open on the WRONG row -> PRE.
//
// Page policy (page_policy_i): OPEN (ap=0, rows stay open) | CLOSE (ap=1, every
// column op auto-precharges). Runtime adaptive policies override via
// ap_mode_en_i/ap_close_i + the timeout-PRE request (pumice_page_policy).
//
// v1 scope: single-rank pick (rank 0). Documentation:
// rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_cmd_arbiter
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int IW   = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  page_policy_e              page_policy_i,

    // ---- SCHED_POLICY order mode (PUMICE-006 Axis 1) ----
    // 0/2 = FR-FCFS (build default), 1 = in_order, 3 = age_threshold.
    input  logic [1:0]                sched_order_mode_i,
    // Row/column arbiter selects (SCHED_POLICY.row_sel / col_sel):
    // 0 = default (oldest), 1 = most_pending, 2 = fewest_pending. row_sel
    // steers the ACTIVATE pick, col_sel the COLUMN pick; tie-break is
    // always oldest. Pending population is counted per CAM over its own
    // schedulable entries sharing {bank,row}.
    input  logic [1:0]                sched_row_sel_i,
    input  logic [1:0]                sched_col_sel_i,
    // Address-arbiter class preference (SCHED_POLICY.access_pref):
    // 0/1 = column_first (default), 2 = row_first (bank parallelism:
    // activates outrank row-hits), 3 = precharge_first (close wrong
    // rows eagerly). Read-over-write priority holds WITHIN the class.
    input  logic [1:0]                sched_access_pref_i,
    // Write-batching watermarks (SCHED_WR_WM): once the wr CAM's
    // schedulable occupancy crosses high_wm, WRITES outrank reads in
    // every demand class until occupancy falls to low_wm -- back-to-back
    // write drain amortizes the tWTR/tRTW bus turnaround instead of
    // ping-ponging RD/WR. high_wm == 0 disables (build default,
    // bit-identical read-priority).
    input  logic [7:0]                sched_wr_high_wm_i,
    input  logic [7:0]                sched_wr_low_wm_i,
    // Priority sub-policy (SCHED_POLICY.prio_sub): 0/2 = load_over_store
    // (reads first -- the build default), 1 = none (fair: the direction
    // alternates on each fired demand op), 3 = age_boost (reads first
    // UNLESS the write-class winner is age-boosted and the read-class
    // winner is not -- aged writes pierce read priority). The write-
    // batching drain overrides all of these while active.
    input  logic [1:0]                sched_prio_sub_i,
    // QoS-aware pick (SCHED_POLICY.qos_en): when set, the per-class
    // winner is the HIGHEST AxQOS ready candidate, oldest as tie-break
    // (population selects still apply within an equal-QoS set only when
    // qos_en is clear -- QoS is the outer key by design). qos_en=0 is
    // the build default and bit-identical.
    input  logic                      sched_qos_en_i,
    input  logic [NUM_ENTRIES*4-1:0]  rd_sch_qos_i,
    input  logic [NUM_ENTRIES*4-1:0]  wr_sch_qos_i,
    input  logic [NUM_ENTRIES-1:0]    rd_sch_age_exceed_i, // per-entry age boost
    input  logic [NUM_ENTRIES-1:0]    wr_sch_age_exceed_i,
    input  logic [AGE_WIDTH-1:0]      rd_sch_head_rel_i,   // oldest entry's rel age
    input  logic [AGE_WIDTH-1:0]      wr_sch_head_rel_i,

    // ---- runtime page-policy engine (pumice_page_policy, PUMICE-006) ----
    // ap_mode_en overrides the legacy flat w_ap with the per-bank ap_close
    // mask; timeout_pre_req names an idle-expired open bank to close as the
    // LOWEST-priority pick (JEDEC gating identical to the conflict-PRE path).
    input  logic                      ap_mode_en_i,
    input  logic [NUM_BANKS-1:0]      ap_close_i,
    input  logic                      timeout_pre_req_i,
    input  logic [BKW-1:0]            timeout_pre_bank_i,

    // ---- init passthrough (from init_sequencer) ----
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    // ---- refresh (from refresh_ctrl) ----
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    // REFpb (LPDDR2 per-bank): kind selects the branch, bank names the
    // DEVICE'S internal rotor bank that the next REFpb will hit — only that
    // bank must be precharged; the other banks keep their rows.
    input  logic                      refresh_kind_i,   // 0=REFab, 1=REFpb
    input  logic [BKW-1:0]            refresh_bank_i,   // rotor mirror
    output logic                      refresh_grant_o,
    // REF -> next-command recovery (tRFC/tRFCab, MC cycles). Mission-mode REF
    // recovery is enforced HERE (init_sequencer separately waits t_rfc_wait for
    // its own init refreshes); no evt reaches the bank timers for REF.
    input  logic [15:0]               t_rfc_i,
    input  logic [7:0]                t_rfc_pb_i,       // REFpb recovery; 0 = t_rfc_i

    // ---- per-bank readiness (from pumice_bank_timers) ----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_i,

    // ---- global readiness (from global_timers) ----
    input  logic [NUM_RANKS-1:0]      tfaw_ok_i,
    input  logic [NUM_RANKS-1:0]      trrd_ok_i,
    input  logic                      twtr_ok_i,
    input  logic                      trtw_ok_i,
    input  logic                      tccd_ok_i,

    // ---- wr CAM per-entry vectors (registered) + commit ----
    input  logic [NUM_ENTRIES-1:0]              wr_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_i,
    input  logic                                wr_commit_ready_i,   // wr CAM drain-FIFO room
    output logic                                wr_commit_valid_o,
    output logic [PTRW-1:0]                     wr_commit_slot_o,

    // ---- rd CAM per-entry vectors (registered) + issue ----
    input  logic [NUM_ENTRIES-1:0]              rd_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_i,
    input  logic                                rd_issue_ready_i,    // rd CAM issue-FIFO room
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
    output logic                      cmd_ap_o
);

    localparam int RK0 = 0;   // v1 single-rank pick

    // Column auto-precharge bit from the page policy. With the runtime
    // page-policy engine active (ap_mode_en_i) the decision is per-bank.
    logic w_ap;
    assign w_ap = (page_policy_i == PAGE_POLICY_CLOSE);

    function automatic logic f_ap (input logic [BKW-1:0] b);
        return ap_mode_en_i ? ap_close_i[b] : w_ap;
    endfunction

    // Per-bank ACT/PRE re-issue GUARD. The bank timers register their readiness
    // outputs (2-cycle latency from an evt to act/pre_ready dropping), so a
    // stateless combinational arbiter would re-issue ACT/PRE to the same bank
    // before the timers reflect it. Guard a bank for 2 cycles after issuing an
    // ACT/PRE to it. (Column ops self-limit: the CAM retires the entry on
    // commit/issue, so sch_valid drops the next cycle => no re-issue.)
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;

    // ---- output pipeline: the registered arbiter DECISION ------------------
    // The pick -> bank-timer / CAM fan-out is registered into its own cycle so
    // the scheduler cone splits (fan-in | logic | fan-out). Declared early so
    // the in-flight forward-masks below can reference it. Backpressure: the
    // decision is held until the cmd FIFO accepts it (see the ALWAYS_FF at the
    // end).
    logic                 r_pick_valid;
    dram_op_e             r_op;
    logic [BKW-1:0]       r_bank;
    logic [ROW_WIDTH-1:0] r_row;
    logic [COL_WIDTH-1:0] r_col_out;
    logic                 r_ap_out;
    logic                 r_do_act, r_do_rd, r_do_wr, r_do_pre, r_grant;
    logic                 r_wr_commit, r_rd_issue;
    logic [PTRW-1:0]      r_commit_slot, r_issue_slot;

    // Forward-masks covering the extra output-register cycle:
    //  - an in-flight (registered) ACT/PRE keeps ITS bank guarded until the
    //    timers reflect it (folded into w_guarded below);
    //  - an in-flight column blocks the NEXT column pick, so the arbiter can't
    //    re-issue the same slot before the CAM r_sched update is visible, and
    //    can't overrun tCCD (which the 1-cycle-stale registered bank-readiness
    //    would otherwise allow). Free: tCCD already spaces columns >=2 apart.
    logic w_inflight_col, w_inflight_preact;
    assign w_inflight_col    = r_pick_valid && (r_do_rd || r_do_wr);
    assign w_inflight_preact = r_pick_valid && (r_do_act || r_do_pre);

    // The guard covers ALL bank-state-changing ops (ACT/PRE *and* columns):
    // a column fired <2 cycles ago has not yet dropped this bank's registered
    // pre_ready (tRTP/tWR load), so an unguarded PRE pick — normal or
    // refresh-drain — could precharge on stale readiness. Columns never gate
    // other columns through this (col masks use w_inflight_col + tCCD only);
    // the ONE exception is an auto-precharge column, which does close its bank
    // — see w_ap_col_guard below.
    logic [NUM_BANKS-1:0] w_guarded;
    assign w_guarded = r_guard0 | r_guard1
                     | ((w_inflight_preact || w_inflight_col)
                        ? (NUM_BANKS'(1) << r_bank) : '0);

    // ---- direction-turnaround guard (tWTR/tRTW staleness) ------------------
    // The global turnaround oks are FLOPPED in global_timers (a fired column's
    // ok drops at fire+2) and w_inflight_col covers only the in-flight cycle,
    // so a DIRECTION-CROSSING column picked at fire+1 issues on a stale ok —
    // firing 2 cycles after its opposite, inside that burst's DQ occupancy ->
    // bus-turnaround contention (the 471/471 concurrent-soak corruption,
    // issue #42; invisible to every phase-separated flow). Block CROSS-
    // direction column picks for the 2 cycles after a fired column, until the
    // flopped ok reflects the event. Same-direction pacing remains tCCD's job
    // (>= 2, fully covered by w_inflight_col + the flop latency).
    logic r_wrfire0, r_wrfire1, r_rdfire0, r_rdfire1;
    logic w_rd_turn_block, w_wr_turn_block;
    assign w_rd_turn_block = r_wrfire0 || r_wrfire1;  // WR fired < 2 cyc ago
    assign w_wr_turn_block = r_rdfire0 || r_rdfire1;  // RD fired < 2 cyc ago

    // ---- auto-precharge column guard (CLOSE-policy staleness) --------------
    // Under CLOSE (w_ap) a COLUMN also changes bank state: the xDA precharges
    // the bank as part of the access. The generic w_guarded above deliberately
    // does NOT gate columns against columns, and r_bank_row_active is a cycle
    // stale, so the NEXT entry targeting that same bank+row still saw "row
    // active" and issued a second column into a bank the xDA had already
    // committed to precharge. On the DRAM that column has no open row; the
    // access lands wherever the device last had one (issue #42: batch-2 row-1
    // writes landed on row 0, clobbering batch 1 -- 64 beats / 48 unique).
    // Guard the bank for the 2 cycles after a fired AP column, exactly as
    // r_guard0/1 do for ACT/PRE, so the next access must re-ACTivate.
    // No-op when w_ap is low (OPEN): those columns leave the
    // row open and legitimately stream at tCCD.
    logic [NUM_BANKS-1:0] r_apguard0, r_apguard1;
    logic [NUM_BANKS-1:0] w_ap_col_guard;
    assign w_ap_col_guard = r_apguard0 | r_apguard1;

    // PRE-only column guard (see the column-mask comment). THREE stages:
    // the registered bank image is up to 3 cycles stale end-to-end
    // (bank_timer update + its output register + the arbiter's input
    // register) — a 2-deep guard left a 1-cycle hole that still wedged
    // the parked-victim pattern intermittently.
    logic [NUM_BANKS-1:0] r_preguard0, r_preguard1, r_preguard2;
    logic [NUM_BANKS-1:0] w_pre_col_guard;
    assign w_pre_col_guard = r_preguard0 | r_preguard1 | r_preguard2;

    // ---- REF recovery (tRFC) -----------------------------------------------
    // Loaded when a REF fires; while nonzero the DRAM is refreshing internally
    // and no ACT (or further REF) may issue to the rank. Previously enforced by
    // NOTHING in mission mode: refresh_req dropped ~2 cycles after the grant
    // and the arbiter re-ACTivated the just-precharged rows ~3 cycles after
    // REF, against a ~127.5ns (tRFC) device requirement -> the refresh-rate-
    // correlated row corruption seen on silicon.
    logic [15:0] r_rfc_cnt;
    logic        w_rfc_busy;
    assign w_rfc_busy = (r_rfc_cnt != 16'd0);

    // ---- pipeline: register the bank-timer fan-in at the arbiter input ------
    // The worst w_sys_i path is bank_timer -> arbiter pick -> bank_timer (the
    // scheduler cone: ~83% route, from the 8 scattered per-bank timers fanning
    // into the arbiter and set_* fanning back out). Register the per-bank
    // readiness / open-row here so that fan-in becomes a clean register hop; the
    // pick then reads 1-cycle-old bank state. The existing ACT/PRE guard already
    // covers this staleness (a bank is guarded 2 cycles after an ACT/PRE, which
    // spans the register delay before the timer load is visible). Columns still
    // use the COMBINATIONAL CAM exclusion (sch_valid) + tCCD, so no column
    // double-issue / tCCD hazard is introduced.
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bank_act_ready, r_bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bank_pre_ready,  r_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] r_bank_open_row;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bank_act_ready <= '0; r_bank_rdwr_ready <= '0;
            r_bank_pre_ready <= '0; r_bank_row_active <= '0; r_bank_open_row <= '0;
        end else begin
            r_bank_act_ready  <= bank_act_ready_i;
            r_bank_rdwr_ready <= bank_rdwr_ready_i;
            r_bank_pre_ready  <= bank_pre_ready_i;
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

    // ---- classify each entry into column / activate / precharge -----------
    // Mutually exclusive per entry: an open bank is either on the right row
    // (column) or the wrong row (precharge); a closed bank activates.
    logic [NUM_ENTRIES-1:0] rd_col_m, rd_act_m, rd_pre_m;
    logic [NUM_ENTRIES-1:0] wr_col_m, wr_act_m, wr_pre_m;
    always_comb begin
        rd_col_m = '0; rd_act_m = '0; rd_pre_m = '0;
        wr_col_m = '0; wr_act_m = '0; wr_pre_m = '0;
        for (int e = 0; e < NUM_ENTRIES; e++) begin
            automatic logic [PTRW-1:0]      ei = PTRW'(e);
            automatic logic [BKW-1:0]       rb = f_bank(rd_sch_bank_i, ei);
            automatic logic [BKW-1:0]       wb = f_bank(wr_sch_bank_i, ei);
            automatic logic                 rhit = r_bank_row_active[RK0][rb]
                                                   && (f_row(rd_sch_row_i, ei) == r_bank_open_row[RK0][rb]);
            automatic logic                 whit = r_bank_row_active[RK0][wb]
                                                   && (f_row(wr_sch_row_i, ei) == r_bank_open_row[RK0][wb]);
            // READ entry. The column (RD) commit enqueues into the rd CAM's
            // issue-order FIFO, so it may ONLY fire when that FIFO has room
            // (rd_issue_ready_i) — otherwise the read would issue to DRAM but
            // the CAM would drop it (double-issue + misrouted return). ACT/PRE
            // don't touch the CAM, so they stay free -> the arbiter does other
            // work while the FIFO is full (no bubble).
            if (rd_sch_valid_i[e]) begin
                // !w_pre_col_guard: a PRE fired on this bank within the
                // last 3 cycles — the registered row image is STALE and a
                // column picked against it lands on the just-closed row
                // (the RD issues, its data never returns, and the AR-order
                // drain wedges behind it forever). PRE-only on purpose:
                // the general w_guarded also covers RD/WR fires and would
                // throttle back-to-back same-bank columns. Found by the
                // parked-victim pattern in test_pumice_core_sched_order;
                // latent since the bank-parallel refactor.
                rd_col_m[e] = rhit && r_bank_rdwr_ready[RK0][rb] && tccd_ok_i && twtr_ok_i
                              && rd_issue_ready_i && !w_inflight_col
                              && !w_rd_turn_block && !w_ap_col_guard[rb]
                              && !w_pre_col_guard[rb];
                rd_act_m[e] = !r_bank_row_active[RK0][rb] && !w_guarded[rb]
                              && r_bank_act_ready[RK0][rb] && tfaw_ok_i[RK0] && trrd_ok_i[RK0]
                              && !w_rfc_busy;
                rd_pre_m[e] = r_bank_row_active[RK0][rb] && !w_guarded[rb] && !rhit
                              && r_bank_pre_ready[RK0][rb];
            end
            // WRITE entry. The column (WR) commit enqueues into the wr CAM's
            // drain FIFO, so gate it on drain-FIFO room (wr_commit_ready_i) —
            // else the write issues to DRAM but its data never drains (stale
            // DRAM) and the slot re-issues. ACT/PRE stay free.
            if (wr_sch_valid_i[e]) begin
                wr_col_m[e] = whit && r_bank_rdwr_ready[RK0][wb] && tccd_ok_i && trtw_ok_i
                              && wr_commit_ready_i && !w_inflight_col
                              && !w_wr_turn_block && !w_ap_col_guard[wb]
                              && !w_pre_col_guard[wb];
                wr_act_m[e] = !r_bank_row_active[RK0][wb] && !w_guarded[wb]
                              && r_bank_act_ready[RK0][wb] && tfaw_ok_i[RK0] && trrd_ok_i[RK0]
                              && !w_rfc_busy;
                wr_pre_m[e] = r_bank_row_active[RK0][wb] && !w_guarded[wb] && !whit
                              && r_bank_pre_ready[RK0][wb];
            end
        end
    end

    // ---- oldest-in-mask via the age-order matrix : returns {found, slot} ----
    // Entry i is the oldest of `mask` iff it is masked AND older than every
    // OTHER masked entry (older[i][j] for all masked j != i). With a total
    // insertion order exactly one entry qualifies -> `is_old` is one-hot. All
    // 1-bit ops (an N-input AND per entry) — no wide age compares.
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

    // ---- ORDER_MODE overlay (SCHED_POLICY.order_mode, PUMICE-006 Axis 1) ---
    // The class masks above are FR-FCFS (modes 0/2, the build default). The
    // overlay only NARROWS them — the branch chain below is untouched, so the
    // column > activate > precharge preference and read-over-write priority
    // hold within whatever survives the narrowing.
    //   1 in_order      only the single oldest not-issued reference across
    //                   both CAMs may drive picks (no lookahead). Head-of-CAM
    //                   comes from the age-order matrix; between CAMs the
    //                   older head wins by relative-age compare (both CAM age
    //                   counters free-run from reset, so the values share an
    //                   epoch; tie -> read).
    //   3 age_threshold FR-FCFS until any CANDIDATE crosses
    //                   SCHED_POLICY.age_thresh; then every class narrows to
    //                   boosted entries — an aged reference's PRE outranks a
    //                   fresh row-hit, bounding starvation.
    localparam logic [1:0] ORDER_IN_ORDER = 2'd1;
    localparam logic [1:0] ORDER_AGE_THR  = 2'd3;

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

    // Boost triggers on a boosted entry's EXISTENCE (the CAM gates the flag
    // on schedulability), NOT on its momentary candidacy: a boosted PRE
    // blocked by its bank's 2-cycle guard would otherwise never engage the
    // narrowing, while the competing un-boosted column keeps firing and
    // re-arming that same guard — the aged entry starves forever on its own
    // trigger condition.
    logic w_boost_any;
    assign w_boost_any = (|rd_sch_age_exceed_i) || (|wr_sch_age_exceed_i);

    logic [NUM_ENTRIES-1:0] rd_col_me, rd_act_me, rd_pre_me;
    logic [NUM_ENTRIES-1:0] wr_col_me, wr_act_me, wr_pre_me;
    always_comb begin
        rd_col_me = rd_col_m; rd_act_me = rd_act_m; rd_pre_me = rd_pre_m;
        wr_col_me = wr_col_m; wr_act_me = wr_act_m; wr_pre_me = wr_pre_m;
        if (sched_order_mode_i == ORDER_IN_ORDER) begin
            if (w_rd_head_wins) begin
                rd_col_me &= w_rd_head; rd_act_me &= w_rd_head;
                rd_pre_me &= w_rd_head;
                wr_col_me = '0; wr_act_me = '0; wr_pre_me = '0;
            end else begin
                wr_col_me &= w_wr_head; wr_act_me &= w_wr_head;
                wr_pre_me &= w_wr_head;
                rd_col_me = '0; rd_act_me = '0; rd_pre_me = '0;
            end
        end else if (sched_order_mode_i == ORDER_AGE_THR && w_boost_any) begin
            rd_col_me &= rd_sch_age_exceed_i; rd_act_me &= rd_sch_age_exceed_i;
            rd_pre_me &= rd_sch_age_exceed_i;
            wr_col_me &= wr_sch_age_exceed_i; wr_act_me &= wr_sch_age_exceed_i;
            wr_pre_me &= wr_sch_age_exceed_i;
        end
    end

    // ---- per-entry pending population (SCHED_POLICY.row_sel / col_sel) ----
    // pop[i] = number of SCHEDULABLE entries in the SAME CAM sharing entry
    // i's {bank,row} (including itself). At NUM_ENTRIES=8 this is a cheap
    // 8x8 match triangle -- the paper's "expensive population counters"
    // degenerate to a handful of 3-bit adders at this CAM depth.
    localparam int POPW = $clog2(NUM_ENTRIES + 1);
    logic [POPW-1:0] rd_pop [NUM_ENTRIES];
    logic [POPW-1:0] wr_pop [NUM_ENTRIES];
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            rd_pop[i] = '0;
            wr_pop[i] = '0;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if (rd_sch_valid_i[j]
                    && (f_bank(rd_sch_bank_i, PTRW'(j)) == f_bank(rd_sch_bank_i, PTRW'(i)))
                    && (f_row(rd_sch_row_i, PTRW'(j))  == f_row(rd_sch_row_i, PTRW'(i))))
                    rd_pop[i] = rd_pop[i] + POPW'(1);
                if (wr_sch_valid_i[j]
                    && (f_bank(wr_sch_bank_i, PTRW'(j)) == f_bank(wr_sch_bank_i, PTRW'(i)))
                    && (f_row(wr_sch_row_i, PTRW'(j))  == f_row(wr_sch_row_i, PTRW'(i))))
                    wr_pop[i] = wr_pop[i] + POPW'(1);
            end
        end
    end

    // ---- oldest-with-population-policy pick : returns {found, slot} ----
    // sel 0 = oldest (pure age-order matrix, identical to arg_oldest);
    // sel 1 = most_pending, sel 2 = fewest_pending -- population first,
    // OLDEST as the tie-break. All compares are POPW-bit + the 1-bit
    // older matrix; entry i wins iff no other masked entry beats it.
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

    // ---- ACCESS_PREF: pick the demand CLASS first, then read-over-write
    // within it. The class availability comes from the (possibly
    // ORDER_MODE-narrowed) per-class picks, so in_order / age_threshold
    // compose: they narrow WHO is a candidate, access_pref reorders WHICH
    // CLASS of the survivors is served first. 0/1 = column_first (the
    // legacy chain order), 2 = row_first, 3 = precharge_first.
    typedef enum logic [1:0] {CL_NONE, CL_COL, CL_ACT, CL_PRE} pick_class_e;

    // col_sel steers columns, row_sel steers activates; precharge picks
    // stay strictly oldest (closing the "most pending" row would be
    // anti-productive, and PRE ordering is a correctness-adjacent path).
    // QOS_EN: narrow each class to its MAX-QoS candidates before the
    // population/oldest select runs, so QoS is the outer key and the
    // existing selects break ties inside the winning QoS level.
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

    logic            rd_col_f, wr_col_f, rd_act_f, wr_act_f, rd_pre_f, wr_pre_f;
    logic [PTRW-1:0] rd_col_s, wr_col_s, rd_act_s, wr_act_s, rd_pre_s, wr_pre_s;
    always_comb begin
        {rd_col_f, rd_col_s} = arg_sel(sched_col_sel_i, rd_col_q, rd_sch_older_i, rd_pop);
        {wr_col_f, wr_col_s} = arg_sel(sched_col_sel_i, wr_col_q, wr_sch_older_i, wr_pop);
        {rd_act_f, rd_act_s} = arg_sel(sched_row_sel_i, rd_act_q, rd_sch_older_i, rd_pop);
        {wr_act_f, wr_act_s} = arg_sel(sched_row_sel_i, wr_act_q, wr_sch_older_i, wr_pop);
        {rd_pre_f, rd_pre_s} = arg_oldest(rd_pre_q, rd_sch_older_i);
        {wr_pre_f, wr_pre_s} = arg_oldest(wr_pre_q, wr_sch_older_i);
    end

    // ---- write-batching drain state (SCHED_WR_WM hysteresis) ----
    localparam int OCCW = $clog2(NUM_ENTRIES + 1);
    logic [OCCW-1:0] w_wr_occ;
    always_comb begin
        w_wr_occ = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (wr_sch_valid_i[i]) w_wr_occ = w_wr_occ + OCCW'(1);
    end

    // Fair-alternation toggle for prio_sub == none: flips on every fired
    // demand op so neither direction can monopolize the pick. The flop
    // lives below the output stage (it needs w_fire_out); only the
    // declaration is here, where the pick logic reads it.
    logic r_dir_rr;

    logic r_wr_drain;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_drain <= 1'b0;
        end else if (sched_wr_high_wm_i == 8'd0) begin
            r_wr_drain <= 1'b0;                       // batching disabled
        end else if (8'(w_wr_occ) <= sched_wr_low_wm_i) begin
            r_wr_drain <= 1'b0;                       // drained down: stop
        end else if (8'(w_wr_occ) >= sched_wr_high_wm_i) begin
            r_wr_drain <= 1'b1;                       // backlog: start drain
        end
    )

    // Per-class "write goes first" decision: drain > prio_sub.
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
        w_c_act = rd_act_f || wr_act_f;
        w_c_pre = rd_pre_f || wr_pre_f;
        unique case (sched_access_pref_i)
            2'd2:    w_pick_class = w_c_act ? CL_ACT
                                  : w_c_col ? CL_COL
                                  : w_c_pre ? CL_PRE : CL_NONE;  // row_first
            2'd3:    w_pick_class = w_c_pre ? CL_PRE
                                  : w_c_col ? CL_COL
                                  : w_c_act ? CL_ACT : CL_NONE;  // precharge_first
            default: w_pick_class = w_c_col ? CL_COL
                                  : w_c_act ? CL_ACT
                                  : w_c_pre ? CL_PRE : CL_NONE;  // column_first
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
    // REF may fire only when NO bank can possibly have a row open. The
    // registered view (w_any_active) is 2-3 cycles stale, so it alone let a
    // REFab collide with a just-picked ACT (bug #2: ACT -> REF, no PRE -> the
    // following read of that row returns garbage). Also require: nothing
    // row-affecting in flight or inside its guard window, and any prior REF's
    // tRFC recovery elapsed (covers back-to-back drain REFs too). The guard
    // check costs at most 2 idle cycles after the last drain-PRE — which also
    // provides the PRE->REF tRP spacing.
    // !r_grant term: the grant->refresh_req-drop round trip is 2 cycles, so
    // without it the branch re-picks a SECOND REF while the first still sits
    // in the output register (rfc_busy loads a cycle too late to stop it)
    // and the refresh DOUBLE-ISSUES on the wire. For REFab that was a silent
    // tRFC-between-REFs violation; for REFpb it is fatal — every command
    // advances the DEVICE'S internal bank rotor, so a doubled REFpb
    // desynchronizes the controller's rotor mirror and the controller then
    // precharges the wrong bank ahead of each refresh (found via the DRAM
    // model's refpb_with_open_row + the zero-data reads that follow).
    assign w_ref_safe = !w_any_active && !w_inflight_preact
                      && (r_guard0 == '0) && (r_guard1 == '0)
                      && !w_rfc_busy && !r_grant;

    // REFpb safety: only the ROTOR bank must be closed (that is the whole
    // point of per-bank refresh — the other banks keep serving row hits).
    // The inflight/guard/rfc terms stay global: conservative, and the rank-
    // wide ACT block during the (shorter) tRFCpb recovery also spaces
    // consecutive REFpb commands by tRFCpb as JEDEC requires.
    logic w_refpb_safe;
    assign w_refpb_safe = !r_bank_row_active[RK0][refresh_bank_i]
                        && !w_inflight_preact
                        && (r_guard0 == '0) && (r_guard1 == '0)
                        && !w_rfc_busy && !r_grant;

    // ========================================================================
    // Priority pick (combinational). Produces the abstract command + the
    // side-effects (evt / commit / issue / grant), all gated on cmd accept.
    // ========================================================================
    dram_op_e        w_op;
    logic [BKW-1:0]  w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;
    logic            w_ap_out;
    logic            w_valid;
    logic            w_do_act, w_do_rd, w_do_wr, w_do_pre, w_grant;
    logic            w_wr_commit, w_rd_issue;
    logic [PTRW-1:0] w_commit_slot, w_issue_slot;

    always_comb begin
        w_op = OP_NOP; w_bank = '0; w_row = '0; w_col = '0; w_ap_out = 1'b0;
        w_valid = 1'b0;
        w_do_act = 1'b0; w_do_rd = 1'b0; w_do_wr = 1'b0; w_do_pre = 1'b0; w_grant = 1'b0;
        w_wr_commit = 1'b0; w_rd_issue = 1'b0; w_commit_slot = '0; w_issue_slot = '0;

        if (!init_done_i) begin
            // 1. INIT — forward the sequencer command verbatim.
            if (init_cmd_valid_i) begin
                w_valid = 1'b1; w_op = init_cmd_op_i;
                w_bank = init_cmd_bank_i; w_row = init_cmd_row_i;
            end
        end else if (refresh_req_i || refresh_drain_i) begin
            // 2. REFRESH — precharge active banks first, then REF + grant.
            // The REF itself only fires under w_ref_safe (no possibly-open row,
            // tRFC met); until then this branch idles rather than fall through
            // to column/ACT picks (a fall-through would starve the refresh).
            if (refresh_kind_i) begin
                // 2b. REFpb — close ONLY the device's rotor bank, then issue
                // the per-bank refresh; every other bank keeps its row.
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
        end else if (w_pick_class == CL_COL && rd_col_f
                     && !(w_col_wrf && wr_col_f)) begin
            // 3a. READ row-hit (read-priority). ap is per-bank when the
            // runtime page-policy engine is active.
            w_bank = f_bank(rd_sch_bank_i, rd_col_s); w_col = f_col(rd_sch_col_i, rd_col_s);
            w_valid = 1'b1; w_op = f_ap(w_bank) ? OP_RDA : OP_RD;
            w_ap_out = f_ap(w_bank); w_do_rd = 1'b1; w_rd_issue = 1'b1; w_issue_slot = rd_col_s;
        end else if (w_pick_class == CL_COL && wr_col_f) begin
            // 3b. WRITE row-hit.
            w_bank = f_bank(wr_sch_bank_i, wr_col_s); w_col = f_col(wr_sch_col_i, wr_col_s);
            w_valid = 1'b1; w_op = f_ap(w_bank) ? OP_WRA : OP_WR;
            w_ap_out = f_ap(w_bank); w_do_wr = 1'b1; w_wr_commit = 1'b1; w_commit_slot = wr_col_s;
        end else if (w_pick_class == CL_ACT && rd_act_f
                     && !(w_act_wrf && wr_act_f)) begin
            // 4a. ACTIVATE the oldest pending READ's idle bank (bank-parallel).
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = f_bank(rd_sch_bank_i, rd_act_s); w_row = f_row(rd_sch_row_i, rd_act_s);
            w_do_act = 1'b1;
        end else if (w_pick_class == CL_ACT && wr_act_f) begin
            // 4b. ACTIVATE the oldest pending WRITE's idle bank.
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = f_bank(wr_sch_bank_i, wr_act_s); w_row = f_row(wr_sch_row_i, wr_act_s);
            w_do_act = 1'b1;
        end else if (w_pick_class == CL_PRE && rd_pre_f
                     && !(w_pre_wrf && wr_pre_f)) begin
            // 5a. PRECHARGE a bank open on the wrong row for a pending read.
            w_valid = 1'b1; w_op = OP_PRE; w_bank = f_bank(rd_sch_bank_i, rd_pre_s);
            w_do_pre = 1'b1;
        end else if (w_pick_class == CL_PRE && wr_pre_f) begin
            // 5b. PRECHARGE a bank open on the wrong row for a pending write.
            w_valid = 1'b1; w_op = OP_PRE; w_bank = f_bank(wr_sch_bank_i, wr_pre_s);
            w_do_pre = 1'b1;
        end else if (timeout_pre_req_i
                     && r_bank_row_active[RK0][timeout_pre_bank_i]
                     && r_bank_pre_ready[RK0][timeout_pre_bank_i]
                     && !w_guarded[timeout_pre_bank_i]) begin
            // 6. TIMEOUT PRECHARGE (fixed_open / adapt_time): close an
            // idle-expired open row. Strictly lowest priority — any demand
            // column/ACT/conflict-PRE and the whole refresh path outrank it —
            // and gated identically to the conflict-PRE path (registered
            // row-active + pre_ready + the 2-cycle re-issue guard).
            w_valid = 1'b1; w_op = OP_PRE; w_bank = timeout_pre_bank_i;
            w_do_pre = 1'b1;
        end
    end

    // ---- output register: capture the pick, drain to the cmd FIFO ----------
    // Accept a new pick when the output stage is empty or draining this cycle;
    // otherwise hold the decision (backpressure from a full cmd FIFO).
    logic w_out_ready, w_fire_out;
    assign w_out_ready = !r_pick_valid || cmd_ready_i;   // may capture a new pick
    assign w_fire_out  = r_pick_valid && cmd_ready_i;     // registered cmd accepted

    // prio_sub == none fair-alternation toggle (declared above with the
    // pick logic that reads it).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dir_rr <= 1'b0;
        else if (w_fire_out && (r_do_rd || r_do_wr || r_do_act || r_do_pre))
            r_dir_rr <= ~r_dir_rr;
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pick_valid <= 1'b0;
            r_do_act <= 1'b0; r_do_rd <= 1'b0; r_do_wr <= 1'b0; r_do_pre <= 1'b0;
            r_grant  <= 1'b0; r_wr_commit <= 1'b0; r_rd_issue <= 1'b0;
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
    assign evt_act_o = w_fire_out && r_do_act;
    assign evt_rd_o  = w_fire_out && r_do_rd;
    assign evt_wr_o  = w_fire_out && r_do_wr;
    assign evt_pre_o = w_fire_out && r_do_pre;
    assign evt_ap_o  = r_ap_out;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = r_bank;
    assign evt_row_o  = r_row;

    // ---- CAM commit / issue / refresh grant (on accepted issue) ----
    assign wr_commit_valid_o = w_fire_out && r_wr_commit;
    assign wr_commit_slot_o  = r_commit_slot;
    assign rd_issue_valid_o  = w_fire_out && r_rd_issue;
    assign rd_issue_slot_o   = r_issue_slot;
    assign refresh_grant_o   = w_fire_out && r_grant;

    // ---- guard update: 2-cycle per-bank block after a FIRED ACT/PRE. The
    // in-flight ACT/PRE (w_inflight_preact, folded into w_guarded) protects the
    // bank while the decision is held/draining; r_guard0/1 then cover the 2
    // cycles after it fires, spanning the input-register + timer latency before
    // the bank reads busy. ----
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0 <= '0;
            r_guard1 <= '0;
            r_wrfire0 <= 1'b0; r_wrfire1 <= 1'b0;
            r_rdfire0 <= 1'b0; r_rdfire1 <= 1'b0;
            r_apguard0 <= '0;  r_apguard1 <= '0;
            r_preguard0 <= '0; r_preguard1 <= '0; r_preguard2 <= '0;
        end else begin
            r_guard1 <= r_guard0;
            r_guard0 <= '0;
            if (w_fire_out && (r_do_act || r_do_pre || r_do_rd || r_do_wr))
                r_guard0 <= (NUM_BANKS'(1) << r_bank);
            r_preguard2 <= r_preguard1;
            r_preguard1 <= r_preguard0;
            r_preguard0 <= (w_fire_out && r_do_pre)
                         ? (NUM_BANKS'(1) << r_bank) : '0;
            // direction-turnaround guard shift (see w_rd/wr_turn_block)
            r_wrfire1 <= r_wrfire0;
            r_wrfire0 <= w_fire_out && r_do_wr;
            r_rdfire1 <= r_rdfire0;
            r_rdfire0 <= w_fire_out && r_do_rd;
            // AP-column guard shift (see w_ap_col_guard)
            r_apguard1 <= r_apguard0;
            r_apguard0 <= '0;
            if (w_fire_out && (r_do_rd || r_do_wr) && r_ap_out)
                r_apguard0 <= (NUM_BANKS'(1) << r_bank);
        end
    )

    // ---- tRFC recovery counter: load on a FIRED REF, count down to 0 --------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rfc_cnt <= '0;
        end else if (w_fire_out && r_grant) begin
            // REFpb recovers in tRFCpb (< tRFCab); 0 falls back to tRFCab.
            r_rfc_cnt <= (r_op == OP_REFPB && t_rfc_pb_i != 8'd0)
                       ? {8'h0, t_rfc_pb_i} : t_rfc_i;
        end else if (w_rfc_busy) begin
            r_rfc_cnt <= r_rfc_cnt - 16'd1;
        end
    )

endmodule : pumice_cmd_arbiter
