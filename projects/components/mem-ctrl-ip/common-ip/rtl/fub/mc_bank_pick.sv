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
//   search starts past the effective winner's pair (its own request is
//   stale in the fire cycle). The winner is a PAIR INDEX plus op class --
//   the payload is not in this loop, and nothing in the loop reads a
//   record. The write sink is one register-only predicate from the CAM (its
//   own accept condition), gated here and re-checked at fire.
//
//   FIRE is the JEDEC authority: it re-reads the LIVE safe_* bits for the
//   winner's bank, the live row-active bit, the forward tCCD counter, the
//   direction turnarounds and the refresh / tRFC demand blocks. A winner
//   that is waiting on a timer HOLDS: the pick register loads every cycle
//   from the arbiter (or the register-only speculation below), a second
//   register keeps last cycle's effective winner, and a registered
//   "waiting on a timer" bit selects between them in front of the fire
//   stage. The oldest requester fires first (no walk under tCCD), and
//   nothing in the fire cone reaches a register's load enable: the fire
//   cone ends in D inputs only (hold bit, rotor, shadow, hint, timers).
//   A winner whose class no longer applies, or that is demand-blocked, is
//   released and re-arbitrated; the decode re-presents it.
//
//   Two mechanisms make the dependent hops land on the JEDEC floor:
//
//   * Pop shadow. The record lags the backend by one cycle (contract), so in
//     the cycle after a column fires the record still shows the popped head.
//     The fire stage remembers the pair (one-hot) whose column it just fired;
//     that pair is served from its 2nd record for the cycle. That is what
//     sustains one column per cycle on a single bank -- and it is why the
//     fire stage re-checks the candidate's hit: the entry it fires may be
//     two pops past the one the decode classified. The hit itself rides in
//     the record (classified at the storage edge against the registered row
//     image, one cycle stale) and is ANDed with the live safe bits here.
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
    // 0 = no stall-cause counters (the eight 32-bit stall_*_o outputs read 0). They feed the
    //     STALL_* CSRs; an integration without those registers leaves them unconnected.
    parameter bit HAS_STALL_STATS = 1'b1,

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
    // ---- command payload by slot (2026-10-24) -----------------------------
    // The records name a slot; the row and column of the command come from
    // the backend's slot fields through ONE lookup per direction here, not
    // from every head record. Materialising row + col in 32 records was the
    // bulk of both storage backends on the board (report 5.11): the record's
    // own row/col fields are no longer read by this core.
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0] wr_slot_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0] wr_slot_col_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0] rd_slot_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0] rd_slot_col_i,

    // ---- storage commit / issue handshake --------------------------------
    // Write sink room, the CAM's own accept condition (registers only, no
    // commit_valid and no drain-pop term). Used twice: the arbiter gates write
    // column requests on it so a pick is never made into a full drain queue,
    // and the fire stage re-checks it so two write columns picked back to
    // back into one slot of room can never put a WR into the command FIFO
    // that the CAM refused (a DRAM write whose data never drains). An earlier
    // split "ready if the current winner commits now / if it does not" was
    // pessimistic whenever the held winner was a write column blocked by a
    // timer: it assumed that winner would commit, gated every other request,
    // and cost one cycle per burst on the write ceiling (fires every 5
    // cycles at tCCD 4).
    input  logic                      wr_commit_ready_now_i,
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
    // (no open-row input: the row hit rides in the record, classified at the
    //  storage edge against the timers' registered image)
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,

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
    output logic                      cmd_timeout_pre_o,   // the PRE is the policy's timeout close (BUG-030)
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
    logic         [NPAIR-1:0] w_hit;

    // One-hot: the pair whose column fired last cycle. Its record still shows
    // the popped head this cycle (the contract's one-cycle latency, pinned by
    // the records' fub test), so the pair is served from its second record.
    // No slot compare: that was 8 x 16 compares on the record's slot field
    // sitting at the head of the fire cone.
    logic [NPAIR-1:0] r_shadow;

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_rec1[2*b]   = rd_head_i [b];
            w_rec2[2*b]   = rd_head2_i[b];
            w_rec1[2*b+1] = wr_head_i [b];
            w_rec2[2*b+1] = wr_head2_i[b];
        end
        for (int p = 0; p < NPAIR; p++) begin
            w_cand[p] = r_shadow[p] ? w_rec2[p] : w_rec1[p];
            // The record's hit is classified at the storage edge against the
            // scheduler's REGISTERED row image, one cycle stale: a stale 1
            // after a PRE is blocked by the live safe_rdwr below (row_valid
            // is 0), a stale 0 after an ACT costs nothing while tRCD >= 2.
            w_hit [p] = w_cand[p].vld && w_cand[p].hit;
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
            r_req    <= '0;
            r_aged   <= '0;
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
                r_req   [p] <= req;
                r_cls   [p] <= cls;
                r_aged  [p] <= req && w_cand[p].age_exceed;
            end
        end
    )

    // ======================================================================
    // Stage 2: arbiter -> registered winner {vld, pair, class}
    // ======================================================================
    logic             r_pick_vld;       // the arbiter's (or the speculation's) pick, loaded EVERY cycle
    logic [PAIRW-1:0] r_pick_pair;
    cls_e             r_pick_cls;
    logic             r_held_vld;       // last cycle's effective winner
    logic [PAIRW-1:0] r_held_pair;
    cls_e             r_held_cls;
    logic             r_hold;           // it was waiting on a timer: serve it again
    // The EFFECTIVE winner the fire stage serves: the held one while it waits
    // on a timer, else the fresh pick. A 2:1 mux of registers by a registered
    // bit -- the hold of the Phase 2 core (oldest requester fires first, no
    // walk under tCCD) without the fire cone on any register's load path.
    logic             w_win_vld;
    logic [PAIRW-1:0] w_win_pair;
    cls_e             w_win_cls;
    assign w_win_vld  = r_hold ? r_held_vld  : r_pick_vld;
    assign w_win_pair = r_hold ? r_held_pair : r_pick_pair;
    assign w_win_cls  = r_hold ? r_held_cls  : r_pick_cls;
    logic [PAIRW-1:0] r_rotor;
    logic             r_dir;            // 0 = reads, 1 = writes
    logic [7:0]       r_dir_batch;

    // next-op hint from the fire stage (one-cycle pulse)
    logic             r_hint_vld;
    logic [PAIRW-1:0] r_hint_pair;
    cls_e             r_hint_cls;

    // Short-hop speculation (register-only): when the held winner is a column
    // whose candidate is the last of its row and the following PRE's timer is
    // shorter than the pipe (tRTP / tWR < LA), the NEXT winner is that PRE,
    // assumed on the column firing now. If the column did not fire, the PRE
    // fails its class check next cycle (the row still holds the hit) and
    // costs nothing. Likewise ACT -> COL and PRE -> ACT for tRCD / tRP < LA.
    // This replaces a bypass that loaded the winner register straight from
    // the fire decision, i.e. put the whole fire cone on r_win's load path.
    logic         w_spec_vld;
    cls_e         w_spec_cls;
    logic         w_win_bsr, w_win_bempty;   // the winner's CANDIDATE flags (record, or 2nd record under the pop shadow)
    logic         w_win_hit;                 // the candidate's recorded hit (storage-edge register, one cycle stale)
    logic         w_win_ap_policy;
    logic         w_other_req;               // some pair other than the winner is requesting

    logic [NPAIR-1:0] w_req_ok, w_req_col, w_req_col_dir, w_req_row, w_req_aged;
    logic [NPAIR-1:0] w_sel, w_sel_above, w_below_mask, w_hint_vec;
    logic [NPAIR-1:0] w_pick_final, w_pick_onehot;
    logic             w_rd_col_any, w_wr_col_any;
    logic             w_hint_ok, w_hint_is_col;
    logic             w_pick_vld;
    logic [PAIRW-1:0] w_pick_pair;
    cls_e             w_pick_cls;

    // Fire-stage facts the arbiter needs (declared here, driven in stage 3):
    // the held winner's candidate record and the class alternation bit.
    mc_head_rec_t     w_sel_cand;
    logic             r_last_was_row;     // last demand fire was ACT/PRE -> prefer columns now
    logic [PAIRW-1:0] w_rotor_eff;

    // Sink room is checked HERE, one cycle before the fire, and not at the
    // fire stage: the write CAM's commit_ready answers "will a commit decided
    // now be accepted next cycle" and is itself a function of this cycle's
    // commit_valid (mc_wr_data_cam, rate-matched commit), so gating the fire
    // on it is a combinational loop. A column that passed this check fires
    // unconditionally and the CAM accepts it by construction (only pops can
    // happen in between). The FRFCFS core makes the same split at its
    // pre-pick.
    //
    // The search starts past the EFFECTIVE winner's pair, and the rotor
    // follows a fire: r_req lags a fire by a cycle (decode -> request ->
    // arbiter), so in the fire cycle the winner's own request is stale --
    // after a row command, or a column that empties its pair, re-picking it
    // costs a dropped cycle (a bank-rotating single-entry write stream ran
    // at 50%, twice). Starting past it serves every other requester first;
    // with no other requester the search wraps to the same pair, which is
    // the one-column-per-cycle path (a stale re-pick then drops at the fire
    // stage at no cost: the hint or the refreshed request lands in the same
    // cycle). Because the effective winner HOLDS while it waits on a timer,
    // the search start is stable while it waits: the next pick is the same
    // pair every cycle, and the fire order is the request order. (A rotor
    // that moved past the fresh pick every cycle walked on under tCCD and
    // fired whichever pair it had reached: bank 0's second read before banks
    // 1-3's first, +20 cycles on the return ring. A rotor that only moved on
    // a fire re-picked the fired pair in the fire cycle, before anything
    // registered could mask it.)
    assign w_rotor_eff = w_win_vld ? (w_win_pair + PAIRW'(1)) : r_rotor;
    // the write sink's room, registers only (see the port note)
    logic w_wr_sink_ok;
    assign w_wr_sink_ok = wr_commit_ready_now_i;
    // The effective winner's OWN request is stale whenever it cannot be the
    // pair's next command: a row command (the pair wants a column or an ACT
    // next, which the hint / speculation carry), or a column with NO
    // SAME-ROW entry behind it (the next entry is a miss, or there is none:
    // a PRE or an ACT comes next, never this request again). The request
    // register describes a fired entry for TWO cycles -- the fire cycle (it
    // was decoded from the record the cycle before the pick) and the cycle
    // after (decoded from the record in the fire cycle, which still shows
    // the entry; the pop shadow re-aims the CANDIDATE that cycle, not the
    // request) -- so the pair is masked out of the pick for both:
    //
    //   cycle N   (fire): r_stale_pick / r_stale_win / r_stale_spec, from
    //             NEXT cycle's effective winner, which this cycle already
    //             knows (hold, speculation or the fresh pick). Keyed on the
    //             CANDIDATE's flag, read live through the pop shadow (w_cand
    //             / w_sel_cand), never the decode's one-cycle-old copy,
    //             which at a burst end still describes the previous entry.
    //             Without it the class alternation (after a column, prefer
    //             row commands) re-picked the pair whose ACT was firing that
    //             very cycle, and every row switch under interleaved traffic
    //             paid a bubble (col_ilv 418 vs 459 MB/s).
    //   cycle N+1: r_stale_fire, from the FIRE, keyed on the fired record's
    //             behind_empty. Without it a column that emptied its pair
    //             was re-picked the cycle after it fired (the arbiter saw
    //             its request, the fire stage saw an empty candidate),
    //             failed its class, and that free slot went to the page
    //             policy's idle-timeout close (tr_init 2 on this board),
    //             which closed another generator's open row: one ACT per
    //             eight columns with eight generators, 461 vs Phase 2's 567
    //             MB/s. Phase 2's trace shows the same timeout request
    //             asserted in 1 926 of 2 063 cycles and never served,
    //             because its slot-compared shadow left no free slot; all
    //             187 closes in the Phase 3 trace sit exactly two cycles
    //             after a column fire of the stale winner's pair. An empty
    //             pair has nothing legitimate to pick, so this cycle costs
    //             nothing; a mask keyed on "another row behind" instead
    //             cost the write PRE a cycle (col_major writes 291 vs 311),
    //             since the hint / speculation carry that case.
    //
    // A streaming column (same row behind) is never masked: the search past
    // the winner wraps to it when it is alone, the one-column-per-cycle
    // path. Every source is REGISTERED: computed live from the effective-
    // winner mux and a 4-to-16 decode the mask sat at the root of the
    // arbiter cone (14 levels to the pick register). The three cycle-N
    // sources are registered SEPARATELY (the fresh pick as the one-hot the
    // arbiter already isolates, never the encoded index; the held / the
    // speculated winner from registers) and resolved next cycle by the
    // registered hold and speculation bits: a mux of registers at the root,
    // and no fire-cone select on any load path (the N+1 mask's D input is
    // the same column-fire term the pop shadow loads from).
    logic [NPAIR-1:0] r_stale_pick, r_stale_win, r_stale_spec, r_stale_fire;
    logic             r_spec_taken;
    logic [NPAIR-1:0] w_self_stale;
    assign w_self_stale = (r_hold ? r_stale_win : (r_spec_taken ? r_stale_spec : r_stale_pick))
                        | r_stale_fire;
    logic [NPAIR-1:0] w_stale_if;               // per pair: its request would be stale after a fire
    always_comb begin
        for (int p = 0; p < NPAIR; p++) w_stale_if[p] = (r_cls[p] != CL_COL) || !w_cand[p].behind_same_row;
    end
    always_comb begin
        for (int p = 0; p < NPAIR; p++) begin
            automatic logic sink_ok = (r_cls[p] != CL_COL)
                                   || (p[0] ? w_wr_sink_ok : rd_issue_ready_i);
            w_req_ok     [p] = r_req[p] && sink_ok && !w_self_stale[p];
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
                                       || (r_hint_pair[0] ? w_wr_sink_ok : rd_issue_ready_i));
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

        // round-robin: lowest index at or above the (effective) rotor, else lowest overall
        for (int p = 0; p < NPAIR; p++) w_below_mask[p] = (PAIRW'(p) < w_rotor_eff);
        w_sel_above = w_sel & ~w_below_mask;
        w_pick_vld  = |w_sel;
        w_pick_pair = '0;
        if (|w_sel_above) begin
            for (int p = NPAIR-1; p >= 0; p--) if (w_sel_above[p]) w_pick_pair = PAIRW'(p);
        end else begin
            for (int p = NPAIR-1; p >= 0; p--) if (w_sel[p])       w_pick_pair = PAIRW'(p);
        end
        w_pick_cls = (w_hint_ok && (w_sel == w_hint_vec)) ? r_hint_cls : r_cls[w_pick_pair];
        // the same pick as a one-hot (lowest set bit of the searched vector):
        // a carry chain in parallel with the encoder, for the stale mask
        w_pick_final  = (|w_sel_above) ? w_sel_above : w_sel;
        w_pick_onehot = w_pick_final & (~w_pick_final + NPAIR'(1));

        // ---- short-hop speculation on the held winner (registers only) ----
        // the candidate's flags, not the head record's: in a one-column-per-
        // cycle stream every column after the first fires from the 2nd record
        // (pop shadow), and the head's behind_same_row is 1 by definition --
        // reading it here killed the speculation exactly where it matters
        w_win_bsr       = w_sel_cand.behind_same_row;
        w_win_bempty    = w_sel_cand.behind_empty;
        w_win_hit       = w_sel_cand.hit;
        w_other_req     = |(w_req_ok & ~(NPAIR'(1) << w_win_pair));
        w_win_ap_policy = ap_mode_en_i ? ap_close_i[BKW'(w_win_pair >> 1)]
                        : ((page_policy_i == PAGE_POLICY_CLOSE)
                           || (CLOSE_ON_DRAIN && !w_win_bsr));
        // Only when the current winner CAN be accepted now as far as the
        // registered facts go (sink room): a column blocked by a full return
        // ring or drain queue must not be followed by a speculated PRE, which
        // would fail its class check and cost the pair a cycle each time.
        w_spec_vld = 1'b0;
        w_spec_cls = CL_NONE;
        if ((LA > 0) && w_win_vld
            && ((w_win_cls != CL_COL) || (w_win_pair[0] ? w_wr_sink_ok : rd_issue_ready_i))) begin
            if ((w_win_cls == CL_ACT) && (t_rcd_i <= 8'(LA_SHORT))) begin
                w_spec_vld = 1'b1; w_spec_cls = CL_COL;
            end else if ((w_win_cls == CL_PRE) && (t_rp_i <= 8'(LA_SHORT))) begin
                w_spec_vld = 1'b1; w_spec_cls = CL_ACT;
            end else if ((w_win_cls == CL_COL) && !w_win_ap_policy
                         && !w_win_bsr && !w_win_bempty
                         && !w_hit[w_win_pair ^ 1]
                         && ((w_win_pair[0] ? t_wr_i : t_rtp_i) <= 8'(LA_SHORT))) begin
                w_spec_vld = 1'b1; w_spec_cls = CL_PRE;
            end else if ((w_win_cls == CL_COL) && w_win_bsr && w_win_hit
                         && !w_win_ap_policy
                         && (t_ccd_i <= 8'(LA_SHORT)) && !w_other_req) begin
                // COL -> COL on the same row, same pair, when nobody else is
                // asking: covers the cycle in which the record's hit is still
                // stale after the ACT (decode cannot request yet) and the
                // steady one-column-per-cycle stream. With other requesters
                // the arbiter interleaves them instead (no starvation).
                // The candidate's own RECORDED hit is required: behind_same_row
                // says the entry behind the candidate shares ITS row, so after
                // the last column of a row the next entry (a miss) carries
                // behind_same_row = 1 for the row after it, and a speculation
                // keyed on that flag alone re-loaded a column for the pair
                // every cycle while the decode's PRE never won (a 351k-cycle
                // write hang on col_major).
                w_spec_vld = 1'b1; w_spec_cls = CL_COL;
            end
        end
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
    assign w_sel_bank    = BKW'(w_win_pair >> 1);
    assign w_sel_is_wr   = w_win_pair[0];
    logic [PTRW-1:0] w_sel_slot;
    assign w_sel_slot    = PTRW'(w_sel_cand.slot);
    assign w_sel_cand    = w_cand[w_win_pair];
    assign w_sel_hit     = w_hit [w_win_pair];
    assign w_sel_row_act = bank_row_active_i[RK0][w_sel_bank];
    assign w_fis_col     = (w_win_cls == CL_COL);
    assign w_fis_act     = (w_win_cls == CL_ACT);
    assign w_fis_pre     = (w_win_cls == CL_PRE);

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

    // class still applies and timers open -> fire; otherwise the winner is
    // simply re-arbitrated next cycle (no hold: the winner register loads
    // every cycle, so no fire-cone term sits on its load path)
    logic w_class_ok, w_timer_ok, w_blocked, w_dmd_ok;
    always_comb begin
        w_class_ok = 1'b0;
        w_timer_ok = 1'b0;
        w_blocked  = w_ref_dmd_block[w_sel_bank] || w_rfc_dmd_block[w_sel_bank];
        if (w_fis_col) begin
            // the write sink re-check: registers only (see the port note)
            w_class_ok = w_sel_cand.vld && w_sel_hit
                      && (!w_sel_is_wr || wr_commit_ready_now_i);
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
        w_dmd_ok   = w_win_vld && w_class_ok && !w_blocked && w_timer_ok;
    end
    // The winner's bank timer, as the lookahead sees it (registers only):
    // bounds the hold to a timer that opens within the pipe depth. A bank
    // gated longer than that (the contract bench's gate, a per-bank refresh)
    // releases the winner so the next requester fires instead; the decode
    // re-presents it when its lookahead opens.
    logic w_win_la_ok;
    always_comb begin
        w_win_la_ok = 1'b0;
        if (w_fis_col)      w_win_la_ok = bank_rdwr_ready_la_i[RK0][w_sel_bank];
        else if (w_fis_act) w_win_la_ok = bank_act_ready_la_i [RK0][w_sel_bank];
        else if (w_fis_pre) w_win_la_ok = bank_pre_ready_la_i [RK0][w_sel_bank];
    end
    // hold: the effective winner was a valid, applicable, unblocked request
    // whose bank opens within the pipe depth and that did not fire (tCCD /
    // turnaround / cmd_ready closed, or the override took the slot) -- serve
    // it again next cycle. A winner whose class no longer applies, that is
    // demand-blocked, or whose bank is gated beyond the lookahead is released
    // and the decode re-presents it.
    logic             w_hold_next;
    assign w_hold_next = w_win_vld && w_class_ok && !w_blocked && w_win_la_ok && !w_dmd_fire;

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
                   && !(w_win_vld && (w_sel_bank == timeout_pre_bank_i));

    assign w_fire      = cmd_ready_i && (w_ovr_vld ? w_ovr_safe : (w_dmd_ok || w_to_pre));
    assign w_dmd_fire  = w_fire && !w_ovr_vld && w_dmd_ok;
    assign cmd_valid_o = w_fire;
    logic w_to_fire;
    assign w_to_fire   = w_fire && !w_ovr_vld && !w_dmd_ok;
    assign cmd_timeout_pre_o = w_to_fire;

    // ---- payload ----------------------------------------------------------
    // the backend's flat slot fields as arrays (wires only; see the index note below)
    logic [ROW_WIDTH-1:0] w_wr_slot_row [NUM_ENTRIES], w_rd_slot_row [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] w_wr_slot_col [NUM_ENTRIES], w_rd_slot_col [NUM_ENTRIES];
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_wr_slot_row[i] = wr_slot_row_i[i*ROW_WIDTH +: ROW_WIDTH];
            w_rd_slot_row[i] = rd_slot_row_i[i*ROW_WIDTH +: ROW_WIDTH];
            w_wr_slot_col[i] = wr_slot_col_i[i*COL_WIDTH +: COL_WIDTH];
            w_rd_slot_col[i] = rd_slot_col_i[i*COL_WIDTH +: COL_WIDTH];
        end
    end
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
        end else if (w_win_vld) begin
            cmd_bank_o = w_sel_bank;
            // Array index, not a variable part-select on the flat vector: the
            // part-select synthesizes as a barrel shifter over the whole
            // N x ROW_WIDTH bus (1 538 of this block's 5 407 ASAP7 cells,
            // pumice TASK-056); the array index is an N:1 mux per bit.
            cmd_row_o  = w_sel_is_wr ? w_wr_slot_row[w_sel_slot] : w_rd_slot_row[w_sel_slot];
            cmd_col_o  = w_sel_is_wr ? w_wr_slot_col[w_sel_slot] : w_rd_slot_col[w_sel_slot];
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

    // A grant is a REF the refresh controller asked for. The init sequence's
    // refreshes pass through the same override (DDR2 init issues two), and
    // the controller banks any grant with no backlog as a PULL-IN credit;
    // two init-time credits silently consumed the first two tREFI ticks
    // after init on every run (pumice ISSUE-022: exactly 2 tREFI soft
    // violations per BANK_PICK run, none on FRFCFS, whose grant is a
    // registered request-side pulse) and left refresh_credit's strict arm
    // one REF short once the core got faster.
    assign refresh_grant_o = w_fire && w_ovr_vld && init_done_i
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
    // register at all; the arbiter speculates it from the held winner
    // (w_spec_*). A hop with t == LA takes the hint path and lands exactly;
    // longer hops are the decode's.
    logic w_hint_vld;
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
                         && !w_hit[w_win_pair ^ 1]) begin
                w_hop_t = w_sel_is_wr ? t_wr_i : t_rtp_i;
                if (w_hop_t <= 8'(LA)) begin w_hint_vld = 1'b1; w_hint_cls = CL_PRE; end
            end
        end
        // hops shorter than the pipe are the arbiter's speculation, not a hint
        w_hint_vld = w_hint_vld && !((LA > 0) && (w_hop_t <= 8'(LA_SHORT)));
    end

    // ---- registered state: winner, rotor, direction, shadow, hint, history --
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pick_vld  <= 1'b0;
            r_pick_pair <= '0;
            r_pick_cls  <= CL_NONE;
            r_held_vld  <= 1'b0;
            r_held_pair <= '0;
            r_held_cls  <= CL_NONE;
            r_hold      <= 1'b0;
            r_rotor     <= '0;
            r_dir       <= 1'b0;
            r_dir_batch <= '0;
            r_shadow    <= '0;
            r_stale_pick  <= '0;
            r_stale_win   <= '0;
            r_stale_spec  <= '0;
            r_stale_fire  <= '0;
            r_spec_taken  <= 1'b0;
            r_hint_vld  <= 1'b0;
            r_hint_pair <= '0;
            r_hint_cls  <= CL_NONE;
            r_last_was_row <= 1'b0;
            r_wrfire0   <= 1'b0;
            r_rdfire0   <= 1'b0;
            r_actfire0      <= 1'b0;
            r_actfire0_bank <= '0;
        end else begin
            // pick: loads EVERY cycle from the arbiter (or the short-hop
            // speculation on the effective winner); no fire-cone term on
            // its load path
            if (w_spec_vld) begin
                r_pick_vld  <= 1'b1;
                r_pick_pair <= w_win_pair;
                r_pick_cls  <= w_spec_cls;
            end else begin
                r_pick_vld  <= w_pick_vld;
                r_pick_pair <= w_pick_pair;
                r_pick_cls  <= w_pick_cls;
            end
            r_hold      <= w_hold_next;
            r_held_vld  <= w_win_vld;
            r_held_pair <= w_win_pair;
            r_held_cls  <= w_win_cls;
            // next cycle's effective winner is known now: hold, speculation
            // or the fresh pick -- register each source's stale mask; the
            // registered hold / speculation bits resolve them next cycle
            r_spec_taken  <= w_spec_vld;
            r_stale_win   <= (w_win_vld && ((w_win_cls != CL_COL) || !w_sel_cand.behind_same_row))
                           ? (NPAIR'(1) << w_win_pair) : '0;
            r_stale_spec  <= ((w_spec_cls != CL_COL) || !w_sel_cand.behind_same_row) ? (NPAIR'(1) << w_win_pair) : '0;
            r_stale_pick  <= w_pick_onehot & w_stale_if;
            // the cycle after a column fire that emptied its pair (see above)
            r_stale_fire  <= (w_col_fire_now && w_sel_cand.behind_empty) ? (NPAIR'(1) << w_win_pair) : '0;
            if (w_dmd_fire) r_last_was_row <= !w_fis_col;
            // rotor: past the fired pair; unchanged while the winner waits
            if (w_dmd_fire) r_rotor <= w_win_pair + PAIRW'(1);

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

            // pop shadow (one cycle, one-hot)
            r_shadow <= w_col_fire_now ? (NPAIR'(1) << w_win_pair) : '0;

            // next-op hint (one cycle)
            r_hint_vld  <= w_hint_vld;
            r_hint_pair <= w_win_pair;
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
    generate if (HAS_STALL_STATS) begin : g_stall_stats
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
    end else begin : g_no_stall_stats
        assign stall_bp_o = '0; assign stall_refresh_o = '0; assign stall_turnaround_o = '0;
        assign stall_tccd_o = '0; assign stall_actlimit_o = '0; assign stall_banktimer_o = '0;
        assign stall_noreq_o = '0; assign stall_zq_o = '0;
        wire _unused_ss = &{1'b0, w_any_pending};
    end endgenerate

endmodule : mc_bank_pick
