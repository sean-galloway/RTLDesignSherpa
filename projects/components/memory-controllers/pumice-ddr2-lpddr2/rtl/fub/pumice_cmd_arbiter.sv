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
    // ap_mode_en selects the per-bank ap_close mask for auto-precharge;
    // timeout_pre_req names an idle-expired open bank to close as the
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

    // ========================================================================
    // Two-stage bank-partitioned scheduler (PUMICE-017 depth split). The single
    // deep pick cone is split by a per-bank candidate register:
    //   pumice_bank_cmd_picker x NUM_BANKS  (STAGE 1: per-bank classify+select)
    //   pumice_bank_sched_core              (STAGE 2: tournament + recheck +
    //                                        refresh/init override + output reg)
    // The GLOBAL overlays (order-mode keep masks with the cross-CAM head compare,
    // per-entry population, write-batching occupancy/drain, the fair-alternation
    // toggle) are computed ONCE here and fanned into every per-bank picker, which
    // resolves qos / pop / age / class / direction over its own entries and emits
    // a composite priority key the core arbitrates. To hold the pick cone under
    // 25 mux-levels the in_order head + runner-up and the per-bank population are
    // REGISTERED (both O(NUM_ENTRIES) scans); head-advance-on-issue stays a cheap
    // combinational mux off the registered head. Predictor tables remain a later
    // phase (still set aside under rtl/OLD/).
    // ------------------------------------------------------------------------
    localparam int BSPOPW = $clog2(NUM_ENTRIES + 1);
    localparam int BSKEYW = 8 + BSPOPW + PTRW;       // class+dir+qos+pop+age
    localparam int BSOCCW = $clog2(NUM_ENTRIES + 1);
    localparam logic [1:0] BSINORDER = 2'd1;
    localparam logic [1:0] BSAGETHR  = 2'd3;


    // Register the per-bank timer fan-in for the CORE's recheck/refresh. The
    // PICKERS read LIVE bank state (below) so a just-precharged bank's ACT is
    // presentable the next cycle -- the r_bs turn + the opt-2 stage otherwise add
    // a close-page rotation bubble. The core still gates the issue with this
    // registered view, so its guards / refresh see a stable copy.
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bs_act, r_bs_rdwr;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_bs_pre, r_bs_active;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bs_act <= '0; r_bs_rdwr <= '0; r_bs_pre <= '0; r_bs_active <= '0;
        end else begin
            r_bs_act    <= bank_act_ready_i;
            r_bs_rdwr   <= bank_rdwr_ready_i;
            r_bs_pre    <= bank_pre_ready_i;
            r_bs_active <= bank_row_active_i;
        end
    )

    // Per-bank candidate bus (picker -> core) and the core -> picker feedback.
    logic [NUM_BANKS-1:0]                w_cand_valid, w_cand_ap, w_cand_is_rd;
    dram_op_e                            w_cand_op [NUM_BANKS];
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] w_cand_row;
    logic [NUM_BANKS-1:0][COL_WIDTH-1:0] w_cand_col;
    logic [NUM_BANKS-1:0][PTRW-1:0]      w_cand_slot;
    logic [NUM_BANKS-1:0][BSKEYW-1:0]   w_cand_pri;
    logic [NUM_BANKS-1:0]                w_issued;
    dram_op_e                            w_issued_op;

    // ---- ORDER_MODE keep masks (in_order / age_threshold NARROW candidacy) --
    // Per-CAM head = valid entry with no older valid entry (older matrix). The
    // cross-CAM winner (in_order) is by head rel-age, tie -> read -- exactly the
    // flat w_rd_head_wins. Computed once; ANDed into the pickers' class masks.
    // A slot whose column is being ISSUED this cycle no longer counts for the
    // head (it retires next cycle). Advancing the head on the issue -- not a
    // cycle later when the CAM valid drops -- lets the NEXT in-order reference's
    // ACT enter the pipe a cycle sooner, holding the serial in_order + close-page
    // floor (the extra opt-2 stage otherwise stretches its per-access period). No
    // comb loop: the issue outputs come from the registered stage-B decision.
    // The per-CAM in_order head = oldest valid entry, an older-matrix scan that
    // is O(NUM_ENTRIES) deep. Left combinational and ANDed straight into the
    // pickers' class masks it was the DEEPEST arbiter path (~35 mux-levels, in
    // series with the whole picker classify+tournament -- PUMICE-017). So the
    // head AND the runner-up (2nd oldest) are computed from the RAW valid set
    // and REGISTERED; the scan is now reg-to-reg, off the picker cone. The
    // 1-cycle-fresh "advance on issue" survives as a cheap combinational mux:
    // when the head's column commits it retires, so the head becomes the
    // pre-computed runner-up. Streaming keeps the CAM populated, so the
    // runner-up is already registered before the head retires (no bubble).
    logic [NUM_ENTRIES-1:0] w_rd_head0, w_wr_head0;
    logic [NUM_ENTRIES-1:0] w_rd_next0, w_wr_next0;
    always_comb begin
        w_rd_head0 = '0; w_wr_head0 = '0;
        w_rd_next0 = '0; w_wr_next0 = '0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic older_rd = 1'b0;
            automatic logic older_wr = 1'b0;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if ((j != i) && rd_sch_valid_i[j]
                    && rd_sch_older_i[j*NUM_ENTRIES + i]) older_rd = 1'b1;
                if ((j != i) && wr_sch_valid_i[j]
                    && wr_sch_older_i[j*NUM_ENTRIES + i]) older_wr = 1'b1;
            end
            w_rd_head0[i] = rd_sch_valid_i[i] && !older_rd;
            w_wr_head0[i] = wr_sch_valid_i[i] && !older_wr;
        end
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic older_rd = 1'b0;
            automatic logic older_wr = 1'b0;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if ((j != i) && rd_sch_valid_i[j] && !w_rd_head0[j]
                    && rd_sch_older_i[j*NUM_ENTRIES + i]) older_rd = 1'b1;
                if ((j != i) && wr_sch_valid_i[j] && !w_wr_head0[j]
                    && wr_sch_older_i[j*NUM_ENTRIES + i]) older_wr = 1'b1;
            end
            w_rd_next0[i] = rd_sch_valid_i[i] && !w_rd_head0[i] && !older_rd;
            w_wr_next0[i] = wr_sch_valid_i[i] && !w_wr_head0[i] && !older_wr;
        end
    end
    logic [NUM_ENTRIES-1:0] r_rd_head0, r_wr_head0, r_rd_next0, r_wr_next0;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_head0 <= '0; r_wr_head0 <= '0;
            r_rd_next0 <= '0; r_wr_next0 <= '0;
        end else begin
            r_rd_head0 <= w_rd_head0; r_wr_head0 <= w_wr_head0;
            r_rd_next0 <= w_rd_next0; r_wr_next0 <= w_wr_next0;
        end
    )
    logic [NUM_ENTRIES-1:0] w_bs_rd_head, w_bs_wr_head;
    always_comb begin
        w_bs_rd_head = r_rd_head0;
        w_bs_wr_head = r_wr_head0;
        if (rd_issue_valid_o  && r_rd_head0[rd_issue_slot_o])
            w_bs_rd_head = r_rd_next0;
        if (wr_commit_valid_o && r_wr_head0[wr_commit_slot_o])
            w_bs_wr_head = r_wr_next0;
    end
    logic w_bs_rd_head_wins, w_bs_boost_any;
    assign w_bs_rd_head_wins = !(|wr_sch_valid_i)
                             || ((|rd_sch_valid_i)
                                 && (rd_sch_head_rel_i >= wr_sch_head_rel_i));
    assign w_bs_boost_any = (|rd_sch_age_exceed_i) || (|wr_sch_age_exceed_i);

    logic [NUM_ENTRIES-1:0] w_bs_rd_keep, w_bs_wr_keep;
    always_comb begin
        w_bs_rd_keep = '1; w_bs_wr_keep = '1;
        if (sched_order_mode_i == BSINORDER) begin
            if (w_bs_rd_head_wins) begin
                w_bs_rd_keep = w_bs_rd_head; w_bs_wr_keep = '0;
            end else begin
                w_bs_wr_keep = w_bs_wr_head; w_bs_rd_keep = '0;
            end
        end else if (sched_order_mode_i == BSAGETHR && w_bs_boost_any) begin
            w_bs_rd_keep = rd_sch_age_exceed_i;
            w_bs_wr_keep = wr_sch_age_exceed_i;
        end
    end

    // ---- per-entry pending population (SCHED_POLICY.row_sel / col_sel) ------
    logic [NUM_ENTRIES*BSPOPW-1:0] w_bs_rd_pop, w_bs_wr_pop;
    always_comb begin
        w_bs_rd_pop = '0; w_bs_wr_pop = '0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic [BSPOPW-1:0] rp = '0;
            automatic logic [BSPOPW-1:0] wp = '0;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if (rd_sch_valid_i[j]
                    && (rd_sch_bank_i[j*BKW +: BKW] == rd_sch_bank_i[i*BKW +: BKW])
                    && (rd_sch_row_i[j*ROW_WIDTH +: ROW_WIDTH]
                        == rd_sch_row_i[i*ROW_WIDTH +: ROW_WIDTH]))
                    rp = rp + BSPOPW'(1);
                if (wr_sch_valid_i[j]
                    && (wr_sch_bank_i[j*BKW +: BKW] == wr_sch_bank_i[i*BKW +: BKW])
                    && (wr_sch_row_i[j*ROW_WIDTH +: ROW_WIDTH]
                        == wr_sch_row_i[i*ROW_WIDTH +: ROW_WIDTH]))
                    wp = wp + BSPOPW'(1);
            end
            w_bs_rd_pop[i*BSPOPW +: BSPOPW] = rp;
            w_bs_wr_pop[i*BSPOPW +: BSPOPW] = wp;
        end
    end
    // Register the per-bank population before it reaches the pickers. It is a
    // per-row popcount (serial NUM_ENTRIES-deep accumulator) and, feeding the
    // tournament key, was the deepest arbiter cone once the head/occupancy were
    // pipelined. It is only a soft priority TIEBREAKER (favour the busier
    // open-row bank), so 1-cycle staleness is immaterial to correctness.
    logic [NUM_ENTRIES*BSPOPW-1:0] r_bs_rd_pop, r_bs_wr_pop;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bs_rd_pop <= '0; r_bs_wr_pop <= '0;
        end else begin
            r_bs_rd_pop <= w_bs_rd_pop; r_bs_wr_pop <= w_bs_wr_pop;
        end
    )

    // ---- write-batching drain hysteresis (SCHED_WR_WM), global -------------
    // Schedulable write occupancy. $countones so the synthesiser builds a
    // balanced popcount tree -- the hand-rolled serial `occ += valid[i]`
    // accumulator was a ~NUM_ENTRIES-deep adder chain and (via the instant
    // w_bs_drain below) the deepest arbiter cone after the head was registered.
    logic [BSOCCW-1:0] w_bs_wr_occ;
    assign w_bs_wr_occ = BSOCCW'($countones(wr_sch_valid_i));
    logic r_bs_wr_drain;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bs_wr_drain <= 1'b0;
        end else if (sched_wr_high_wm_i == 8'd0) begin
            r_bs_wr_drain <= 1'b0;
        end else if (8'(w_bs_wr_occ) <= sched_wr_low_wm_i) begin
            r_bs_wr_drain <= 1'b0;
        end else if (8'(w_bs_wr_occ) >= sched_wr_high_wm_i) begin
            r_bs_wr_drain <= 1'b1;
        end
    )
    // Combinational drain view fed to the (live-reading) pickers: engage the
    // instant occupancy crosses high_wm, without waiting for r_bs_wr_drain to
    // flop -- else the FIRST live pick would land before the drain registered
    // and a read would slip ahead of the batch. The flop still holds hysteresis.
    logic w_bs_drain;
    assign w_bs_drain = r_bs_wr_drain
                      || ((sched_wr_high_wm_i != 8'd0)
                          && (8'(w_bs_wr_occ) >= sched_wr_high_wm_i));

    // ---- fair-alternation toggle (prio_sub == none): flips per fired op -----
    logic r_bs_dir_rr;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_bs_dir_rr <= 1'b0;
        else if (|w_issued)         r_bs_dir_rr <= ~r_bs_dir_rr;
    )

    genvar gb;
    generate
        for (gb = 0; gb < NUM_BANKS; gb++) begin : g_bank_picker
            pumice_bank_cmd_picker #(
                .BANK_ID     (gb),
                .NUM_ENTRIES (NUM_ENTRIES),
                .ROW_WIDTH   (ROW_WIDTH),
                .COL_WIDTH   (COL_WIDTH),
                .BKW         (BKW),
                .PTRW        (PTRW),
                .POPW        (BSPOPW),
                .KEYW        (BSKEYW)
            ) u_picker (
                .aclk               (aclk),
                .aresetn            (aresetn),
                .page_policy_i      (page_policy_i),
                .ap_mode_en_i       (ap_mode_en_i),
                .ap_close_bit_i     (ap_close_i[gb]),
                .sched_access_pref_i(sched_access_pref_i),
                .sched_row_sel_i    (sched_row_sel_i),
                .sched_col_sel_i    (sched_col_sel_i),
                .sched_prio_sub_i   (sched_prio_sub_i),
                .sched_qos_en_i     (sched_qos_en_i),
                .wr_drain_i         (w_bs_drain),
                .dir_rr_i           (r_bs_dir_rr),
                .bank_act_ready_i   (bank_act_ready_i[RK0][gb]),   // LIVE (core uses r_bs)
                .bank_rdwr_ready_i  (bank_rdwr_ready_i[RK0][gb]),
                .bank_pre_ready_i   (bank_pre_ready_i[RK0][gb]),
                .bank_row_active_i  (bank_row_active_i[RK0][gb]),
                .bank_open_row_i    (bank_open_row_i[RK0][gb]),
                .rd_valid_i         (rd_sch_valid_i),
                .rd_bank_i          (rd_sch_bank_i),
                .rd_row_i           (rd_sch_row_i),
                .rd_col_i           (rd_sch_col_i),
                .rd_older_i         (rd_sch_older_i),
                .rd_issue_ready_i   (rd_issue_ready_i),
                .rd_keep_i          (w_bs_rd_keep),
                .rd_pop_i           (r_bs_rd_pop),
                .rd_qos_i           (rd_sch_qos_i),
                .rd_age_exceed_i    (rd_sch_age_exceed_i),
                .wr_valid_i         (wr_sch_valid_i),
                .wr_bank_i          (wr_sch_bank_i),
                .wr_row_i           (wr_sch_row_i),
                .wr_col_i           (wr_sch_col_i),
                .wr_older_i         (wr_sch_older_i),
                .wr_commit_ready_i  (wr_commit_ready_i),
                .wr_keep_i          (w_bs_wr_keep),
                .wr_pop_i           (r_bs_wr_pop),
                .wr_qos_i           (wr_sch_qos_i),
                .wr_age_exceed_i    (wr_sch_age_exceed_i),
                .issued_i           (w_issued[gb]),
                .issued_op_i        (w_issued_op),
                .cand_valid_o       (w_cand_valid[gb]),
                .cand_op_o          (w_cand_op[gb]),
                .cand_ap_o          (w_cand_ap[gb]),
                .cand_row_o         (w_cand_row[gb]),
                .cand_col_o         (w_cand_col[gb]),
                .cand_slot_o        (w_cand_slot[gb]),
                .cand_is_rd_o       (w_cand_is_rd[gb]),
                .cand_pri_o         (w_cand_pri[gb])
            );
        end
    endgenerate

    pumice_bank_sched_core #(
        .NUM_BANKS (NUM_BANKS),
        .ROW_WIDTH (ROW_WIDTH),
        .COL_WIDTH (COL_WIDTH),
        .BKW       (BKW),
        .PTRW      (PTRW),
        .KEYW      (BSKEYW),
        .RKW       (RKW)
    ) u_sched_core (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .cand_valid_i       (w_cand_valid),
        .cand_op_i          (w_cand_op),
        .cand_ap_i          (w_cand_ap),
        .cand_row_i         (w_cand_row),
        .cand_col_i         (w_cand_col),
        .cand_slot_i        (w_cand_slot),
        .cand_is_rd_i       (w_cand_is_rd),
        .cand_pri_i         (w_cand_pri),
        .bank_act_ready_i   (r_bs_act[RK0]),
        .bank_rdwr_ready_i  (r_bs_rdwr[RK0]),
        .bank_pre_ready_i   (r_bs_pre[RK0]),
        .bank_row_active_i  (r_bs_active[RK0]),
        .wr_commit_ready_i  (wr_commit_ready_i),
        .rd_issue_ready_i   (rd_issue_ready_i),
        .tfaw_ok_i          (tfaw_ok_i[RK0]),
        .trrd_ok_i          (trrd_ok_i[RK0]),
        .twtr_ok_i          (twtr_ok_i),
        .trtw_ok_i          (trtw_ok_i),
        .tccd_ok_i          (tccd_ok_i),
        .init_done_i        (init_done_i),
        .init_cmd_valid_i   (init_cmd_valid_i),
        .init_cmd_op_i      (init_cmd_op_i),
        .init_cmd_bank_i    (init_cmd_bank_i),
        .init_cmd_row_i     (init_cmd_row_i),
        .refresh_req_i      (refresh_req_i),
        .refresh_drain_i    (refresh_drain_i),
        .refresh_kind_i     (refresh_kind_i),
        .refresh_bank_i     (refresh_bank_i),
        .t_rfc_i            (t_rfc_i),
        .t_rfc_pb_i         (t_rfc_pb_i),
        .refresh_grant_o    (refresh_grant_o),
        .timeout_pre_req_i  (timeout_pre_req_i),
        .timeout_pre_bank_i (timeout_pre_bank_i),
        .cmd_ready_i        (cmd_ready_i),
        .cmd_valid_o        (cmd_valid_o),
        .cmd_op_o           (cmd_op_o),
        .cmd_rank_o         (cmd_rank_o),
        .cmd_bank_o         (cmd_bank_o),
        .cmd_row_o          (cmd_row_o),
        .cmd_col_o          (cmd_col_o),
        .cmd_ap_o           (cmd_ap_o),
        .evt_act_o          (evt_act_o),
        .evt_rd_o           (evt_rd_o),
        .evt_wr_o           (evt_wr_o),
        .evt_pre_o          (evt_pre_o),
        .evt_ap_o           (evt_ap_o),
        .evt_rank_o         (evt_rank_o),
        .evt_bank_o         (evt_bank_o),
        .evt_row_o          (evt_row_o),
        .wr_commit_valid_o  (wr_commit_valid_o),
        .wr_commit_slot_o   (wr_commit_slot_o),
        .rd_issue_valid_o   (rd_issue_valid_o),
        .rd_issue_slot_o    (rd_issue_slot_o),
        .issued_o           (w_issued),
        .issued_op_o        (w_issued_op)
    );

endmodule : pumice_cmd_arbiter
