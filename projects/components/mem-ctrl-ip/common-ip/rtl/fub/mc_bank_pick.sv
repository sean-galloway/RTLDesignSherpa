// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_pick
// Purpose: Per-bank pick core for the scheduler plane (mem-ctrl recovery
//          Phase 2, plan docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md
//          section 2.2). Consumes the storage plane's REGISTERED per-bank head
//          records ({head, 2nd} per direction and bank, mc_head_rec_t) and
//          the bank/global timers, and issues one DRAM command per cycle.
//
//   Three stages, every stage fed by flops only:
//
//     records, timers ──► DECODE (per pair)  ──► r_req/r_op[16]
//                         ARBITER (RR + dir)  ──► r_win {vld, pair, op}
//                         FIRE (live gate)    ──► cmd_* / evt_* / commit / issue
//
//   pair p = 2*bank + dir (dir 0 = read, 1 = write).
//
//   DECODE classifies each pair's candidate against the bank it owns:
//   row hit -> COL, open row + miss -> PRE, closed -> ACT, each gated by the
//   timer's advisory lookahead (safe_*_la, LA = this pipe's depth = 2) so a
//   request lands at the fire stage exactly when the live gate opens.
//
//   ARBITER: round-robin rotor over the request bits, with the aging flag as
//   a priority overlay, an ACT/PRE-vs-column alternation (after a row command
//   prefer columns, after a column prefer row commands, so one bank's ACT
//   stream interleaves with another's columns) and a direction register that
//   keeps columns in one direction until that direction runs dry or a batch
//   limit is hit. The request register lags a fire by one cycle, so the
//   winner's own pair is masked when its request cannot be the pair's next
//   command (after a row command, or a column that empties the pair). The
//   winner is a PAIR INDEX plus op class -- the payload is not in this loop.
//
//   FIRE is the JEDEC authority: it re-reads the LIVE safe_* bits for the
//   winner's bank, the live row image (the hit is re-checked against the
//   open row), the forward tCCD counter, the direction turnarounds and the
//   refresh / tRFC demand blocks. A winner whose timer is not yet open HOLDS
//   (nothing is dropped, nothing re-picks); a winner whose class no longer
//   applies (the row changed under it, or a demand block arrived) is DROPPED
//   and the decode re-presents the pair -- the decode runs every cycle, so a
//   drop costs no refill.
//
//   Two mechanisms make the dependent hops land on the JEDEC floor:
//
//   * Pop shadow. The record lags the backend by one cycle (contract), so in
//     the cycle after a column fires the record still shows the popped head.
//     The fire stage remembers {pair, slot} of the column it just fired; a
//     pair whose head still carries that slot is served from its 2nd record.
//     That is what sustains one column per cycle on a single bank -- and it
//     is why the fire stage re-checks the hit live: the entry it fires may
//     be two pops past the one the decode classified.
//
//   * Next-op hint. A fire tells the arbiter what the same pair wants next
//     (ACT -> COL, PRE -> ACT, last-of-row COL -> PRE) one cycle before the
//     decode can see the fire in the timers. The hint is only raised when the
//     hop's timer is within the pipe depth (t <= LA); longer hops are landed
//     by the lookahead decode itself, and a hop shorter than the pipe (t < LA)
//     loads the winner register directly so it fires next cycle. Without the
//     hint every hop pays one cycle of pipeline latency (gap 9 vs the floor
//     of 6 on col_major reads).
//
//   Maintenance, refresh (drain PREs then the all-idle grant, the tRFC and
//   refresh-episode demand blocks, the read-return window), init passthrough
//   and ZQ are lifted verbatim from the retired mc_bank_sched; they were
//   bought with the MC-003 debugging and are not redesigned here.
//
//   CLOSE_ON_DRAIN is exact: a column carries auto-precharge when no same-row
//   entry (schedulable or still filling) sits behind it in its bank.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_pick
    import mc_common_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int NUM_ENTRIES = 8,
    parameter bit HAS_ZQ      = 1'b0,
    parameter bit CLOSE_ON_DRAIN = 1'b1,
    parameter int MAINT_EXTRA_WIDTH = 1,
    // Pipeline depth decode -> fire; the bank timers' BANK_LA must equal it.
    parameter int LA          = 2,
    // Hold REF out of an open read-return window (the DFI aligner's modulo
    // framing has no resync; granite MC-003 2026-10-15). Off by default: a
    // continuous read stream would postpone refresh without bound (pumice
    // refresh_credit at the board geometry saw 2 REFs across a demand
    // stretch), and pumice's DFI plane has run REF into open windows under
    // the FRFCFS core since 2026-09 without a mis-framed beat.
    parameter bit REF_WAIT_RD_RETURN = 1'b0,

    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  page_policy_e              page_policy_i,

    // ---- runtime page policy (mc_page_policy): per-bank auto-precharge
    //      override and the background idle-timeout close request ----------
    input  logic                      ap_mode_en_i,
    input  logic [NUM_BANKS-1:0]      ap_close_i,
    input  logic                      timeout_pre_req_i,
    input  logic [BKW-1:0]            timeout_pre_bank_i,

    // ---- storage plane per-bank head records (registered contract) -------
    input  mc_head_rec_t [NUM_BANKS-1:0] wr_head_i,
    input  mc_head_rec_t [NUM_BANKS-1:0] wr_head2_i,
    input  mc_head_rec_t [NUM_BANKS-1:0] rd_head_i,
    input  mc_head_rec_t [NUM_BANKS-1:0] rd_head2_i,

    // ---- storage commit / issue handshake --------------------------------
    input  logic                      wr_commit_ready_i,
    output logic                      wr_commit_valid_o,
    output logic [PTRW-1:0]           wr_commit_slot_o,
    input  logic                      rd_issue_ready_i,
    output logic                      rd_issue_valid_o,
    output logic [PTRW-1:0]           rd_issue_slot_o,

    // ---- init passthrough ----
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    // ---- refresh ----
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    input  logic                      refresh_kind_i,
    input  logic [BKW-1:0]            refresh_bank_i,
    output logic                      refresh_grant_o,
    input  logic [15:0]               t_rfc_i,
    input  logic [7:0]                t_rfc_pb_i,

    // ---- read-return busy from DFI plane (keeps REF out of open return window)
    input  logic                      rd_ret_busy_i,

    // ---- ZQ (present when HAS_ZQ=1) ----
    input  logic                      zq_req_i,
    output logic                      zq_grant_o,
    input  logic [15:0]               t_zqcs_i,

    // ---- generic maintenance ----
    input  logic                      maint_req_i,
    output logic                      maint_grant_o,
    input  dram_op_e                  maint_op_i,
    input  logic [BKW-1:0]            maint_bank_i,
    input  logic [ROW_WIDTH-1:0]      maint_row_i,
    input  logic [COL_WIDTH-1:0]      maint_col_i,
    input  logic [MAINT_EXTRA_WIDTH-1:0] maint_extra_i,
    input  logic                      maint_busy_i,

    // ---- per-bank readiness: live (fire) and lookahead (decode) ----------
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_i,

    // ---- global readiness ----
    input  logic [NUM_RANKS-1:0]      tfaw_ok_i,
    input  logic [NUM_RANKS-1:0]      trrd_ok_i,
    input  logic                      twtr_ok_i,
    input  logic                      trtw_ok_i,
    // Raw tCCD for the forward column-spacing counter (same accounting as
    // the FRFCFS core's r_tccd_fwd; the flopped tccd_ok window carries a +1
    // lag a pick==fire core would eat as real spacing).
    input  logic [7:0]                t_ccd_i,
    // Hop timers, for hint eligibility only (hint iff t <= LA).
    input  logic [7:0]                t_rcd_i,
    input  logic [7:0]                t_rp_i,
    input  logic [7:0]                t_wr_i,
    input  logic [7:0]                t_rtp_i,

    // ---- policy: consecutive columns in one direction while the other
    //      direction has column requests (0 = unlimited) ----
    input  logic [7:0]                dir_batch_max_i,

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
    output logic                      cmd_ap_o,
    output logic [MAINT_EXTRA_WIDTH-1:0] cmd_extra_o,

    // ---- stall-cause attribution ----
    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stall_zq_o
);

    localparam int RK0   = 0;
    localparam int LA_SHORT = (LA > 0) ? LA - 1 : 0;   // a hop this short bypasses the arbiter register
    localparam int NPAIR = 2*NUM_BANKS;
    localparam int PAIRW = (NPAIR > 1) ? $clog2(NPAIR) : 1;

    // op classes carried through the pipe (not dram_op_e: AP is decided at fire)
    typedef enum logic [1:0] { CL_NONE = 2'd0, CL_ACT = 2'd1, CL_COL = 2'd2, CL_PRE = 2'd3 } cls_e;

    // ======================================================================
    // Stage 0: candidates and hits (combinational, flops in: records,
    // timer row image, the one-cycle pop shadow)
    // ======================================================================
    mc_head_rec_t [NPAIR-1:0] w_rec1, w_rec2, w_cand;
    logic         [NPAIR-1:0] w_use2, w_hit;

    logic             r_shadow_vld;
    logic [PAIRW-1:0] r_shadow_pair;
    logic [MC_HEAD_SLOT_W-1:0] r_shadow_slot;

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_rec1[2*b]   = rd_head_i [b];
            w_rec2[2*b]   = rd_head2_i[b];
            w_rec1[2*b+1] = wr_head_i [b];
            w_rec2[2*b+1] = wr_head2_i[b];
        end
        for (int p = 0; p < NPAIR; p++) begin
            automatic logic [BKW-1:0] pb = BKW'(p >> 1);   // the pair's bank
            // The record still shows the head this core popped last cycle:
            // serve the pair from its second record.
            w_use2[p] = r_shadow_vld && (r_shadow_pair == PAIRW'(p))
                     && w_rec1[p].vld && (w_rec1[p].slot == r_shadow_slot);
            w_cand[p] = w_use2[p] ? w_rec2[p] : w_rec1[p];
            w_hit [p] = w_cand[p].vld && bank_row_active_i[RK0][pb]
                     && (w_cand[p].row[ROW_WIDTH-1:0] == bank_open_row_i[RK0][pb]);
        end
    end

    // ======================================================================
    // tRFC / tZQCS recovery counters and the refresh demand blocks
    // (lifted from mc_bank_sched; see that history in MC-003)
    // ======================================================================
    logic [15:0] r_rfc_cnt, r_zqcs_cnt;
    logic        w_rfc_busy, w_zq_busy;
    assign w_rfc_busy = (r_rfc_cnt  != 16'd0);
    assign w_zq_busy  = (r_zqcs_cnt != 16'd0);

    // Refresh-episode demand block: while a refresh is requested or draining,
    // no demand op to the affected bank(s) may fire (REFab = all banks,
    // REFpb = the target). A column launched into the refresh window returns
    // data the aligner mis-captures; an ACT squeezed in ahead of the deferred
    // REF leaves the RTL row image open on a bank the device closed
    // (MC-003 2026-10-15 / 10-17).
    logic [NUM_BANKS-1:0] w_ref_dmd_block;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_ref_dmd_block[b] = (refresh_req_i || refresh_drain_i)
                              && (!refresh_kind_i || (BKW'(b) == refresh_bank_i));
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_rfc_cnt <= '0;
        else if (refresh_grant_o)
            r_rfc_cnt <= (cmd_op_o == OP_REFPB && t_rfc_pb_i != 8'd0)
                         ? {8'h0, t_rfc_pb_i} : t_rfc_i;
        else if (w_rfc_busy)             r_rfc_cnt <= r_rfc_cnt - 16'd1;
    )

    // tRFC window demand block: the granted refresh closes the bank(s) at the
    // DEVICE while the bank timers keep their row image (REF sends no
    // row-clear), so a demand column decoded against an "open" image would
    // fire into a refreshing bank (MC-003 2026-10-17 tREFI=100).
    logic r_rfc_ab;
    logic [BKW-1:0] r_rfc_bank;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rfc_ab    <= 1'b1;
            r_rfc_bank  <= '0;
        end else if (refresh_grant_o) begin
            r_rfc_ab   <= (cmd_op_o == OP_REF);
            r_rfc_bank <= refresh_bank_i;
        end
    )
    logic [NUM_BANKS-1:0] w_rfc_dmd_block;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_rfc_dmd_block[b] = w_rfc_busy
                              && (r_rfc_ab || (BKW'(b) == r_rfc_bank));
    end
    generate if (HAS_ZQ) begin : g_zq
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))  r_zqcs_cnt <= '0;
            else if (zq_grant_o)         r_zqcs_cnt <= t_zqcs_i;
            else if (w_zq_busy)          r_zqcs_cnt <= r_zqcs_cnt - 16'd1;
        )
    end else begin : g_no_zq
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))  r_zqcs_cnt <= '0;
        )
    end endgenerate

    // ======================================================================
    // Stage 1: per-pair decode -> registered request / class
    // ======================================================================
    logic [NPAIR-1:0] r_req, r_aged;
    cls_e             r_cls [NPAIR];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_req  <= '0;
            r_aged <= '0;
            for (int p = 0; p < NPAIR; p++) r_cls[p] <= CL_NONE;
        end else begin
            for (int p = 0; p < NPAIR; p++) begin
                automatic logic [BKW-1:0] pb = BKW'(p >> 1);   // the pair's bank
                automatic logic req    = 1'b0;
                automatic cls_e cls    = CL_NONE;
                automatic logic blocked = w_ref_dmd_block[pb] || w_rfc_dmd_block[pb];
                if (w_cand[p].vld && !blocked) begin
                    if (w_hit[p]) begin
                        // row hit: column when tRCD is within the pipe depth.
                        // Sink room (drain FIFO / return ring) is the
                        // ARBITER's check, one cycle before the fire, not
                        // this stage's: gating here too, two cycles ahead of
                        // the rate-matched commit predicate, halved the
                        // single-beat write stream (board geometry, 1 commit
                        // per 2 cycles).
                        if (bank_rdwr_ready_la_i[RK0][pb]) begin
                            req = 1'b1; cls = CL_COL;
                        end
                    end else if (bank_row_active_i[RK0][pb]) begin
                        // miss on an open row: close it, unless the other
                        // direction is still streaming hits on that row
                        // (aging lifts the courtesy: no starvation)
                        if (bank_pre_ready_la_i[RK0][pb]
                            && (!w_hit[p ^ 1] || w_cand[p].age_exceed)) begin
                            req = 1'b1; cls = CL_PRE;
                        end
                    end else begin
                        // closed bank: activate. The tRFC / maintenance
                        // blocks the fire stage drops on are checked here
                        // too, so a blocked ACT is not re-requested every
                        // cycle and dropped every cycle.
                        if (bank_act_ready_la_i[RK0][pb] && !w_rfc_busy && !maint_busy_i) begin
                            req = 1'b1; cls = CL_ACT;
                        end
                    end
                end
                r_req [p] <= req;
                r_cls [p] <= cls;
                r_aged[p] <= req && w_cand[p].age_exceed;
            end
        end
    )

    // ======================================================================
    // Stage 2: arbiter -> registered winner {vld, pair, class}
    // ======================================================================
    logic             r_win_vld;
    logic [PAIRW-1:0] r_win_pair;
    cls_e             r_win_cls;
    logic [PAIRW-1:0] r_rotor;
    logic             r_dir;            // 0 = reads, 1 = writes
    logic [7:0]       r_dir_batch;

    // next-op hint from the fire stage (one-cycle pulse)
    logic             r_hint_vld;
    logic [PAIRW-1:0] r_hint_pair;
    cls_e             r_hint_cls;

    logic [NPAIR-1:0] w_req_ok, w_req_col, w_req_col_dir, w_req_row, w_req_aged;
    logic [NPAIR-1:0] w_sel, w_sel_above, w_below_mask, w_hint_vec;
    logic             w_rd_col_any, w_wr_col_any;
    logic             w_hint_ok, w_hint_is_col, w_win_stale;
    logic             w_pick_vld;
    logic [PAIRW-1:0] w_pick_pair;
    cls_e             w_pick_cls;

    // Fire-stage facts the arbiter needs (declared here, driven in stage 3):
    // the held winner's candidate record and the class alternation bit.
    mc_head_rec_t     w_sel_cand;
    logic             r_last_was_row;     // last demand fire was ACT/PRE -> prefer columns now

    // Sink room is checked HERE, one cycle before the fire, and not at the
    // fire stage: the write CAM's commit_ready answers "will a commit decided
    // now be accepted next cycle" and is itself a function of this cycle's
    // commit_valid (mc_wr_data_cam, rate-matched commit), so gating the fire
    // on it is a combinational loop. A column that passed this check fires
    // unconditionally and the CAM accepts it by construction (only pops can
    // happen in between). The FRFCFS core makes the same split at its
    // pre-pick.
    //
    // The held winner's own pair is masked when its request cannot be the
    // pair's NEXT command: r_req lags the fire by a cycle (decode -> request
    // -> arbiter), so after a row command, or after a column that empties the
    // pair (behind_empty), the stale request would be re-picked and dropped at
    // the fire stage -- every other cycle wasted on a bank-rotating stream
    // (write ceiling at the board geometry: 50%). A column with more entries
    // behind it keeps its request: that is the one-column-per-cycle path.
    // (If the winner is held rather than fired, this cycle's pick is discarded
    // anyway, so the mask is never a loss.)
    assign w_win_stale = r_win_vld && ((r_win_cls != CL_COL) || w_sel_cand.behind_empty);
    always_comb begin
        for (int p = 0; p < NPAIR; p++) begin
            automatic logic sink_ok = (r_cls[p] != CL_COL)
                                   || (p[0] ? wr_commit_ready_i : rd_issue_ready_i);
            w_req_ok     [p] = r_req[p] && sink_ok
                            && !(w_win_stale && (r_win_pair == PAIRW'(p)));
            w_req_col    [p] = w_req_ok[p] && (r_cls[p] == CL_COL);
            w_req_col_dir[p] = w_req_col[p] && (p[0] == r_dir);
            w_req_row    [p] = w_req_ok[p] && (r_cls[p] != CL_COL);
            w_req_aged   [p] = w_req_ok[p] && r_aged[p];
        end
        w_rd_col_any = 1'b0; w_wr_col_any = 1'b0;
        for (int b = 0; b < NUM_BANKS; b++) begin
            if (w_req_col[2*b])   w_rd_col_any = 1'b1;
            if (w_req_col[2*b+1]) w_wr_col_any = 1'b1;
        end

        // the hint is a request of its own class (a column hint whose sink
        // has no room is dropped; the decode re-presents it)
        w_hint_is_col = (r_hint_cls == CL_COL);
        w_hint_ok     = r_hint_vld && (!w_hint_is_col
                                       || (r_hint_pair[0] ? wr_commit_ready_i : rd_issue_ready_i));
        w_hint_vec    = NPAIR'(1) << r_hint_pair;

        // Request set. Aged requests first (starvation relief). Then the two
        // classes ALTERNATE: after a row command prefer columns, after a
        // column prefer row commands -- with both classes pending this
        // interleaves one bank's ACT with another's column (A0 A1 C0 A2 C1
        // ...: the ACT stream runs at tRRD and the columns fill the gaps),
        // where a fixed priority either starves the columns behind a run of
        // ACTs or holds every ACT behind the column stream. With one class
        // pending the other falls through, so a single-bank stream is
        // untouched. Within a class the hint leads, then the current
        // direction's columns, then any.
        if (|w_req_aged)                       w_sel = w_req_aged;
        else if (r_last_was_row) begin
            if (w_hint_ok && w_hint_is_col)    w_sel = w_hint_vec;
            else if (|w_req_col_dir)           w_sel = w_req_col_dir;
            else if (|w_req_col)               w_sel = w_req_col;
            else if (w_hint_ok)                w_sel = w_hint_vec;
            else                               w_sel = w_req_row;
        end else begin
            if (w_hint_ok && !w_hint_is_col)   w_sel = w_hint_vec;
            else if (|w_req_row)               w_sel = w_req_row;
            else if (w_hint_ok)                w_sel = w_hint_vec;
            else if (|w_req_col_dir)           w_sel = w_req_col_dir;
            else                               w_sel = w_req_col;
        end

        // round-robin: lowest index at or above the rotor, else lowest overall
        for (int p = 0; p < NPAIR; p++) w_below_mask[p] = (PAIRW'(p) < r_rotor);
        w_sel_above = w_sel & ~w_below_mask;
        w_pick_vld  = |w_sel;
        w_pick_pair = '0;
        if (|w_sel_above) begin
            for (int p = NPAIR-1; p >= 0; p--) if (w_sel_above[p]) w_pick_pair = PAIRW'(p);
        end else begin
            for (int p = NPAIR-1; p >= 0; p--) if (w_sel[p])       w_pick_pair = PAIRW'(p);
        end
        w_pick_cls = (w_hint_ok && (w_sel == w_hint_vec)) ? r_hint_cls : r_cls[w_pick_pair];
    end

    // ======================================================================
    // Stage 3: fire -- the live JEDEC authority
    // ======================================================================
    // Registered image for the refresh override's drain scan (advisory; the
    // override's PRE re-checks the live pre gate).
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] r_row_act, r_pre_rdy;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_row_act <= '0; r_pre_rdy <= '0;
        end else begin
            r_row_act <= bank_row_active_i;
            r_pre_rdy <= bank_pre_ready_la_i;
        end
    )

    // ---- maintenance / refresh / init override (verbatim from mc_bank_sched)
    logic w_any_active, w_rfsh_pre_found;
    logic [BKW-1:0] w_rfsh_pre_bank;
    always_comb begin
        w_any_active     = |r_row_act[RK0];
        w_rfsh_pre_found = 1'b0;
        w_rfsh_pre_bank  = '0;
        for (int j = NUM_BANKS-1; j >= 0; j--)
            if (r_row_act[RK0][j] && r_pre_rdy[RK0][j]) begin
                w_rfsh_pre_found = 1'b1;
                w_rfsh_pre_bank  = BKW'(j);
            end
    end

    // Read-return window: never grant REF while a read is between this
    // scheduler and the aligner's last captured word (the aligner's modulo
    // framing has no resync; MC-003 2026-10-15).
    logic r_rd_pipe_busy;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))            r_rd_pipe_busy <= 1'b0;
        else if (rd_issue_valid_o)             r_rd_pipe_busy <= 1'b1;
        else if (!rd_ret_busy_i)               r_rd_pipe_busy <= 1'b0;
    )
    logic w_rdret_busy;
    assign w_rdret_busy = r_rd_pipe_busy || rd_ret_busy_i;

    // Demand-ACT fire history: the registered row image lags a fire by one
    // cycle, so a REF request in that window would grant with a bank open
    // at the device (MC-003 2026-10-17).
    logic           r_actfire0;
    logic [BKW-1:0] r_actfire0_bank;

    // All-idle gates on the LIVE activate-ready bits: a bank is ready for REF
    // (or any maintenance) exactly when it is ready for an ACT -- row closed
    // AND tRP since its PRE AND tRC since its ACT. The registered row image
    // alone met tRP only by the accident of two register stages (tRP = 2).
    // Pending demand does NOT block refresh (the override has priority and a
    // head that cannot fire would otherwise deadlock REFab).
    logic w_all_act_ready, w_rdret_gate;
    assign w_all_act_ready = &bank_act_ready_i[RK0];
    assign w_rdret_gate    = REF_WAIT_RD_RETURN && w_rdret_busy;
    logic w_ref_safe, w_refpb_safe, w_maint_safe;
    assign w_ref_safe   = w_all_act_ready && !r_actfire0
                       && !w_rfc_busy && !w_rdret_gate;
    assign w_refpb_safe = bank_act_ready_i[RK0][refresh_bank_i] && !w_rfc_busy && !w_rdret_gate
                       && !(r_actfire0 && (r_actfire0_bank == refresh_bank_i));
    assign w_maint_safe = w_all_act_ready && !w_rfc_busy && !w_zq_busy && !maint_busy_i;

    logic        w_ovr_vld;
    dram_op_e    w_ovr_op;
    logic [BKW-1:0] w_ovr_bank;
    logic [ROW_WIDTH-1:0] w_ovr_row;
    logic [COL_WIDTH-1:0] w_ovr_col;
    always_comb begin
        w_ovr_vld  = 1'b0;
        w_ovr_op   = OP_NOP;
        w_ovr_bank = '0;
        w_ovr_row  = '0;
        w_ovr_col  = '0;
        if (!init_done_i) begin
            if (init_cmd_valid_i) begin
                w_ovr_vld  = 1'b1;
                w_ovr_op   = init_cmd_op_i;
                w_ovr_bank = init_cmd_bank_i;
                w_ovr_row  = init_cmd_row_i;
            end
        end else if (refresh_req_i || refresh_drain_i) begin
            if (refresh_kind_i) begin
                if (r_row_act[RK0][refresh_bank_i]) begin
                    if (r_pre_rdy[RK0][refresh_bank_i]) begin
                        w_ovr_vld  = 1'b1;
                        w_ovr_op   = OP_PRE;
                        w_ovr_bank = refresh_bank_i;
                    end
                end else if (w_refpb_safe) begin
                    w_ovr_vld  = 1'b1;
                    w_ovr_op   = OP_REFPB;
                    w_ovr_bank = refresh_bank_i;
                end
            end else if (w_any_active) begin
                if (w_rfsh_pre_found) begin
                    w_ovr_vld  = 1'b1;
                    w_ovr_op   = OP_PRE;
                    w_ovr_bank = w_rfsh_pre_bank;
                end
            end else if (w_ref_safe) begin
                w_ovr_vld = 1'b1;
                w_ovr_op  = OP_REF;
            end
        end else if (HAS_ZQ && zq_req_i && w_maint_safe) begin
            w_ovr_vld = 1'b1;
            w_ovr_op  = OP_ZQCS;
        end else if (maint_req_i && w_maint_safe) begin
            w_ovr_vld  = 1'b1;
            w_ovr_op   = maint_op_i;
            w_ovr_bank = maint_bank_i;
            w_ovr_row  = maint_row_i;
            w_ovr_col  = maint_col_i;
        end
    end

    // ---- the winner's live view -----------------------------------------
    logic [BKW-1:0]  w_sel_bank;
    logic            w_sel_is_wr;
    logic            w_sel_hit, w_sel_row_act;
    logic            w_fis_col, w_fis_act, w_fis_pre;
    assign w_sel_bank    = BKW'(r_win_pair >> 1);
    assign w_sel_is_wr   = r_win_pair[0];
    assign w_sel_cand    = w_cand[r_win_pair];
    assign w_sel_hit     = w_hit [r_win_pair];
    assign w_sel_row_act = bank_row_active_i[RK0][w_sel_bank];
    assign w_fis_col     = (r_win_cls == CL_COL);
    assign w_fis_act     = (r_win_cls == CL_ACT);
    assign w_fis_pre     = (r_win_cls == CL_PRE);

    // direction turnarounds: 1-deep fire history + the global windows
    logic r_wrfire0, r_rdfire0;

    // FORWARD tCCD counter (see the t_ccd_i port note)
    logic [7:0] r_tccd_fwd;
    logic       w_tccd_fwd_ok, w_fire, w_dmd_fire, w_col_fire_now;
    assign w_tccd_fwd_ok  = (r_tccd_fwd == 8'd0);
    assign w_col_fire_now = w_dmd_fire && w_fis_col;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))  r_tccd_fwd <= 8'd0;
        else if (w_col_fire_now)
            r_tccd_fwd <= (t_ccd_i > 8'd1) ? (t_ccd_i - 8'd1) : 8'd0;
        else if (r_tccd_fwd != 8'd0) r_tccd_fwd <= r_tccd_fwd - 8'd1;
    )

    // class still applies (else DROP) / timers open (else HOLD)
    logic w_class_ok, w_timer_ok, w_blocked, w_dmd_ok, w_dmd_drop;
    always_comb begin
        w_class_ok = 1'b0;
        w_timer_ok = 1'b0;
        w_blocked  = w_ref_dmd_block[w_sel_bank] || w_rfc_dmd_block[w_sel_bank];
        if (w_fis_col) begin
            // no sink term here: see the arbiter-stage note (commit_ready is
            // a function of commit_valid; the decision a cycle earlier owns it)
            w_class_ok = w_sel_cand.vld && w_sel_hit;
            w_timer_ok = bank_rdwr_ready_i[RK0][w_sel_bank] && w_tccd_fwd_ok
                      && (w_sel_is_wr ? (trtw_ok_i && !r_rdfire0)
                                      : (twtr_ok_i && !r_wrfire0));
        end else if (w_fis_act) begin
            w_class_ok = w_sel_cand.vld && !w_sel_row_act && !w_rfc_busy && !maint_busy_i;
            w_timer_ok = bank_act_ready_i[RK0][w_sel_bank] && tfaw_ok_i[RK0] && trrd_ok_i[RK0];
        end else if (w_fis_pre) begin
            w_class_ok = w_sel_cand.vld && w_sel_row_act && !w_sel_hit;
            w_timer_ok = bank_pre_ready_i[RK0][w_sel_bank];
        end
        w_dmd_ok   = r_win_vld && w_class_ok && !w_blocked && w_timer_ok;
        w_dmd_drop = r_win_vld && (!w_class_ok || w_blocked);
    end

    logic w_ovr_safe;
    assign w_ovr_safe = (w_ovr_op == OP_PRE) ? bank_pre_ready_i[RK0][w_ovr_bank] : 1'b1;

    // Background idle-timeout close (mc_page_policy fixed_open): the lowest
    // priority command -- fires only when neither the override nor the demand
    // winner does, against the live row image and pre gate, never on the
    // bank the held winner is about to use.
    logic w_to_pre;
    assign w_to_pre = timeout_pre_req_i && !w_ovr_vld && !w_dmd_ok
                   && bank_row_active_i[RK0][timeout_pre_bank_i]
                   && bank_pre_ready_i[RK0][timeout_pre_bank_i]
                   && !w_ref_dmd_block[timeout_pre_bank_i] && !w_rfc_dmd_block[timeout_pre_bank_i]
                   && !(r_win_vld && (w_sel_bank == timeout_pre_bank_i));

    assign w_fire      = cmd_ready_i && (w_ovr_vld ? w_ovr_safe : (w_dmd_ok || w_to_pre));
    assign w_dmd_fire  = w_fire && !w_ovr_vld && w_dmd_ok;
    assign cmd_valid_o = w_fire;
    logic w_to_fire;
    assign w_to_fire   = w_fire && !w_ovr_vld && !w_dmd_ok;

    // ---- payload ----------------------------------------------------------
    // Auto-precharge: the runtime page policy owns it when enabled (static
    // open / close / fixed_open); otherwise the build policy, or the exact
    // close-on-drain term.
    logic w_sel_ap;
    assign w_sel_ap = ap_mode_en_i ? ap_close_i[w_sel_bank]
                    : ((page_policy_i == PAGE_POLICY_CLOSE)
                       || (CLOSE_ON_DRAIN && !w_sel_cand.behind_same_row));

    always_comb begin
        cmd_op_o    = OP_NOP;
        cmd_bank_o  = '0;
        cmd_row_o   = '0;
        cmd_col_o   = '0;
        cmd_ap_o    = 1'b0;
        cmd_extra_o = '0;
        if (w_ovr_vld) begin
            cmd_op_o    = w_ovr_op;
            cmd_bank_o  = w_ovr_bank;
            cmd_row_o   = w_ovr_row;
            cmd_col_o   = w_ovr_col;
            cmd_extra_o = maint_extra_i;
        end else if (!w_dmd_ok && w_to_pre) begin
            cmd_op_o    = OP_PRE;
            cmd_bank_o  = timeout_pre_bank_i;
        end else if (r_win_vld) begin
            cmd_bank_o = w_sel_bank;
            cmd_row_o  = w_sel_cand.row[ROW_WIDTH-1:0];
            cmd_col_o  = w_sel_cand.col[COL_WIDTH-1:0];
            if (w_fis_act) begin
                cmd_op_o = OP_ACT;
            end else if (w_fis_pre) begin
                cmd_op_o = OP_PRE;
            end else begin
                cmd_ap_o = w_sel_ap;
                cmd_op_o = w_sel_is_wr ? (w_sel_ap ? OP_WRA : OP_WR)
                                       : (w_sel_ap ? OP_RDA : OP_RD);
            end
        end
    end
    assign cmd_rank_o = RKW'(RK0);

    // ---- strobes: storage handshake, grants, timer events -------------------
    assign wr_commit_valid_o = w_dmd_fire && w_fis_col &&  w_sel_is_wr;
    assign wr_commit_slot_o  = PTRW'(w_sel_cand.slot);
    assign rd_issue_valid_o  = w_dmd_fire && w_fis_col && !w_sel_is_wr;
    assign rd_issue_slot_o   = PTRW'(w_sel_cand.slot);

    assign refresh_grant_o = w_fire && w_ovr_vld
                          && ((w_ovr_op == OP_REF) || (w_ovr_op == OP_REFPB));
    assign zq_grant_o      = w_fire && w_ovr_vld && (w_ovr_op == OP_ZQCS);
    assign maint_grant_o   = w_fire && w_ovr_vld && maint_req_i
                          && !refresh_req_i && !refresh_drain_i
                          && !(HAS_ZQ && zq_req_i);

    assign evt_act_o  = w_dmd_fire && w_fis_act;
    assign evt_rd_o   = w_dmd_fire && w_fis_col && !w_sel_is_wr;
    assign evt_wr_o   = w_dmd_fire && w_fis_col &&  w_sel_is_wr;
    assign evt_pre_o  = w_fire && (w_ovr_vld ? (w_ovr_op == OP_PRE) : (w_to_fire || w_fis_pre));
    assign evt_ap_o   = w_dmd_fire && w_fis_col && cmd_ap_o;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = cmd_bank_o;
    assign evt_row_o  = cmd_row_o;

    // ---- next-op hint: what this pair wants next, if its timer is within
    //      the pipe depth (otherwise the lookahead decode lands it) ---------
    // A hop whose timer is SHORTER than the pipe (t < LA, e.g. tRTP = 1 at
    // the LiteDRAM-equivalent profile) cannot land through the arbiter
    // register at all; it loads the winner register directly from the fire
    // stage (w_hint_direct) and fires next cycle. A hop with t == LA takes
    // the arbiter path and lands exactly; longer hops are the decode's.
    logic w_hint_vld, w_hint_direct;
    cls_e w_hint_cls;
    logic [7:0] w_hop_t;
    always_comb begin
        w_hint_vld = 1'b0;
        w_hint_cls = CL_NONE;
        w_hop_t    = 8'hFF;
        if (w_dmd_fire) begin
            if (w_fis_act) begin
                w_hop_t = t_rcd_i;
                if (w_hop_t <= 8'(LA)) begin w_hint_vld = 1'b1; w_hint_cls = CL_COL; end
            end else if (w_fis_pre) begin
                w_hop_t = t_rp_i;
                if (w_hop_t <= 8'(LA)) begin w_hint_vld = 1'b1; w_hint_cls = CL_ACT; end
            end else if (w_fis_col && !cmd_ap_o
                         && !w_sel_cand.behind_same_row && !w_sel_cand.behind_empty
                         && !w_hit[r_win_pair ^ 1]) begin
                w_hop_t = w_sel_is_wr ? t_wr_i : t_rtp_i;
                if (w_hop_t <= 8'(LA)) begin w_hint_vld = 1'b1; w_hint_cls = CL_PRE; end
            end
        end
        w_hint_direct = w_hint_vld && (LA > 0) && (w_hop_t <= 8'(LA_SHORT));
    end

    // ---- registered state: winner, rotor, direction, shadow, hint, history --
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_win_vld   <= 1'b0;
            r_win_pair  <= '0;
            r_win_cls   <= CL_NONE;
            r_rotor     <= '0;
            r_dir       <= 1'b0;
            r_dir_batch <= '0;
            r_shadow_vld  <= 1'b0;
            r_shadow_pair <= '0;
            r_shadow_slot <= '0;
            r_hint_vld  <= 1'b0;
            r_hint_pair <= '0;
            r_hint_cls  <= CL_NONE;
            r_last_was_row <= 1'b0;
            r_wrfire0   <= 1'b0;
            r_rdfire0   <= 1'b0;
            r_actfire0      <= 1'b0;
            r_actfire0_bank <= '0;
        end else begin
            // winner: take the arbiter's result unless holding a timer-blocked
            // one; a short-hop hint bypasses the arbiter register
            if (w_hint_direct) begin
                r_win_vld  <= 1'b1;
                r_win_pair <= r_win_pair;
                r_win_cls  <= w_hint_cls;
            end else if (!r_win_vld || w_dmd_fire || w_dmd_drop) begin
                r_win_vld  <= w_pick_vld;
                r_win_pair <= w_pick_pair;
                r_win_cls  <= w_pick_cls;
            end
            if (w_dmd_fire) r_last_was_row <= !w_fis_col;
            // rotor moves past a pair that fired or was dropped
            if (w_dmd_fire || w_dmd_drop)
                r_rotor <= r_win_pair + PAIRW'(1);

            // direction: stick until the current direction runs dry or the
            // batch limit is hit while the other direction has columns
            if (w_col_fire_now && (w_sel_is_wr != r_dir)) begin
                r_dir       <= w_sel_is_wr;
                r_dir_batch <= 8'd1;
            end else if ((r_dir ? !w_wr_col_any : !w_rd_col_any)
                         && (r_dir ? w_rd_col_any : w_wr_col_any)) begin
                r_dir       <= ~r_dir;
                r_dir_batch <= '0;
            end else if ((dir_batch_max_i != 8'd0) && (r_dir_batch >= dir_batch_max_i)
                         && (r_dir ? w_rd_col_any : w_wr_col_any)) begin
                r_dir       <= ~r_dir;
                r_dir_batch <= '0;
            end else if (w_col_fire_now && (r_dir_batch != 8'hFF)) begin
                r_dir_batch <= r_dir_batch + 8'd1;
            end

            // pop shadow (one cycle)
            r_shadow_vld  <= w_col_fire_now;
            r_shadow_pair <= r_win_pair;
            r_shadow_slot <= w_sel_cand.slot;

            // next-op hint (one cycle; a direct-loaded hint does not also arbitrate)
            r_hint_vld  <= w_hint_vld && !w_hint_direct;
            r_hint_pair <= r_win_pair;
            r_hint_cls  <= w_hint_cls;

            r_wrfire0 <= w_col_fire_now &&  w_sel_is_wr;
            r_rdfire0 <= w_col_fire_now && !w_sel_is_wr;
            r_actfire0      <= w_dmd_fire && w_fis_act;
            r_actfire0_bank <= w_sel_bank;
        end
    )

    // t_zqcs_i is consumed by the HAS_ZQ branch only; the winner's aging flag
    // acted in the decode (priority) and is not re-read here.
    wire _unused_pick = &{1'b0, t_zqcs_i, w_sel_cand.age_exceed};

    // ======================================================================
    // Stall-cause attribution (same buckets as the FRFCFS core)
    // ======================================================================
    logic w_any_pending;
    always_comb begin
        w_any_pending = 1'b0;
        for (int b = 0; b < NUM_BANKS; b++)
            if (wr_head_i[b].vld || rd_head_i[b].vld) w_any_pending = 1'b1;
    end
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            stall_bp_o <= '0; stall_refresh_o <= '0; stall_turnaround_o <= '0;
            stall_tccd_o <= '0; stall_actlimit_o <= '0; stall_banktimer_o <= '0;
            stall_noreq_o <= '0; stall_zq_o <= '0;
        end else if (!w_fire) begin
            if (refresh_req_i || refresh_drain_i)        stall_refresh_o    <= stall_refresh_o + 1;
            else if (!w_any_pending)                     stall_noreq_o      <= stall_noreq_o + 1;
            else if (!cmd_ready_i)                       stall_bp_o         <= stall_bp_o + 1;
            else if (!twtr_ok_i || !trtw_ok_i)           stall_turnaround_o <= stall_turnaround_o + 1;
            else if (!w_tccd_fwd_ok)                     stall_tccd_o       <= stall_tccd_o + 1;
            else if (!tfaw_ok_i[RK0] || !trrd_ok_i[RK0]) stall_actlimit_o   <= stall_actlimit_o + 1;
            else if (HAS_ZQ && w_zq_busy)                stall_zq_o         <= stall_zq_o + 1;
            else                                         stall_banktimer_o  <= stall_banktimer_o + 1;
        end
    )

endmodule : mc_bank_pick
