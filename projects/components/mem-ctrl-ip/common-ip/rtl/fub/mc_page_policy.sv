// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// mc_page_policy — runtime page-policy engine + page/command telemetry.
//
// TASK-001 Axis 2. Watches the arbiter's ISSUED command stream (the same
// valid&&ready stream the cmd-history checker audits) plus the registered
// per-bank row state, and produces two things:
//
//   1. The auto-precharge decision, per bank (`ap_close_o` + `ap_mode_en_o`).
//      With POLICY_MODE==0 the arbiter keeps the legacy flat w_ap
//      (page_policy_i == CLOSE; the retired HYBRID encoding maps to OPEN);
//      any nonzero mode takes over:
//        1 static_open   ap=0 everywhere
//        2 static_close  ap=1 everywhere
//        3 fixed_open    ap=0; rows close by IDLE TIMEOUT instead
//        4 hybrid        auto-precharge on a known conflict (a different-
//                        row entry already queued behind the column in its
//                        bank) always; on a drained queue only where the
//                        bank's history allows it (drain_close_ok_o);
//                        otherwise the idle timeout closes the row
//                        (ap_conflict_only_o; 2026-10-30)
//        5              RETIRED 2026-09-27 (was adapt_access); 4 was
//                        adapt_time until then.
//        6,7            RETIRED 2026-09-26 (were rbl_static / rbl_dyn) --
//                        measured inert or harmful on silicon, see TASK-011.
//                        A write to 4..7 falls through to the build default.
//
//   ONE close mechanism per mode now: auto-precharge (mode 2) or the
//   background idle timeout (mode 3). There is no predictor in this block any
//   more -- pumice_row_pred_table was deleted with mode 5.
//
//   2. A background precharge REQUEST (`timeout_pre_req_o` / bank) for a row
//      whose idle timer expired. The ARBITER issues the actual PRE as its
//      lowest-priority pick, so demand traffic, refresh drain and JEDEC
//      timing (pre_ready, the 2-cycle guard) all still gate it — this block
//      never touches the wire.
//
// Telemetry (always on, mode-independent, feeds the *_STATS CSRs):
//   page_hit    every column op issued (columns only issue on row hits here)
//   page_miss   ACT to a bank whose previous close was a WRONG-ROW PRE
//   page_empty  ACT to a bank that was simply closed (no conflict)
//   act/pre/ref command-class counters
//

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_page_policy
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    // close-on-drain arms on a bank whose rows are SHORT-LIVED: a row that
    // served at most this many columns before the bank moved to another row
    // (one 64 B burst at the board geometry; eight at the 64-bit default).
    // A row that streamed longer than this is a stream, and its successor
    // stays open until the timer or a conflict closes it.
    parameter int DRAIN_ARM_MAX_COLS = 8,
    // 0 = no idle-timeout close: the per-bank idle timers and the timeout PRE request are
    // compiled out; fixed_open then closes rows only on drain (drain_close_ok_o), which is
    // what the engine does anyway at tr_init 0, the shipping default (pumice TASK-059).
    parameter bit HAS_TIMEOUT_CLOSE  = 1'b1,
    // 0 = the stat_* telemetry counters read 0 (a top that wires no *_STATS CSRs).
    parameter bit HAS_TELEMETRY      = 1'b1,
    // 1 = the mistake predictor and the telemetry see the issued command one
    // cycle late, through a register. The idle timers' re-warm and the close
    // request keep the live stream (the request's live veto is what keeps a
    // bank from being asked to close in the cycle after its own command). With
    // the bank-pick core the command's row is an 8:1 slot lookup at the end of
    // the fire cone, and the predictor's row compare into r_keep_open was the
    // second-worst 100 MHz path on the board (15 LUTs, 7.5 ns of wire; granite
    // TASK-003 census 2026-10-27, -0.706 ns). The predictor's verdict is the
    // same: it reads the registered row image, which the delayed command sees
    // in the same relative state (an ACT's bank is closed in the image both
    // when it fires and a cycle later). The telemetry counts the same events a
    // cycle later. Default 0: the FR-FCFS core and pumice are unchanged.
    parameter bit PRED_CMD_REG       = 1'b0,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // ---- mode-select CSR fields (SCHED/PAGE_* registers) -------------------
    input  logic [2:0]                 policy_mode_i,     // PAGE_POLICY_CFG.policy_mode
    input  logic [7:0]                 tr_init_i,         // PAGE_TIMEOUT_CFG.tr_init

    // ---- issued command stream (arbiter output, single-issue) --------------
    input  logic                       cmd_valid_i,       // cmd_valid && cmd_ready
    input  dram_op_e                   cmd_op_i,
    input  logic [BKW-1:0]             cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]       cmd_row_i,
    // the column on cmd_op_i carries auto-precharge (both cores' cmd_ap_o):
    // a close by prediction, so the predictor treats it like a timeout close
    input  logic                       cmd_ap_i,
    input  logic                       pre_is_timeout_i,  // the PRE on cmd_op_i is this block's timeout close (from the core)

    // ---- registered per-bank row state (same bus the arbiter registers) ----
    input  logic [NUM_BANKS-1:0]       bank_row_active_i,
    input  logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,

    // ---- decisions to the arbiter ------------------------------------------
    output logic                       ap_mode_en_o,      // 1 = ap_close_o overrides legacy w_ap
    output logic [NUM_BANKS-1:0]       ap_close_o,        // per-bank: close after this column op
    // mode 4 (hybrid): the pick's close-on-drain auto-precharge applies only
    // when a different-row entry is queued behind the column (not on an
    // empty queue, which the idle timeout closes instead)
    output logic                       ap_conflict_only_o,
    output logic                       timeout_pre_req_o, // background close request
    output logic [BKW-1:0]             timeout_pre_bank_o,
    // per bank: the scheduler MAY close the row on its last visible column
    // (close-on-drain). Armed by evidence -- the bank's last ACT opened a
    // DIFFERENT row than the one before it AND that previous row served at
    // most DRAIN_ARM_MAX_COLS columns, i.e. the rows on this bank are short-
    // lived (col_major, bank-interleaved row walks) -- and disarmed the
    // moment an ACT reopens the row that was just closed (the close, however
    // it happened, was a mistake). A row that streamed long before the bank
    // moved on is a stream; its successor is kept open (the 8-bank page-hit
    // windows of the paging sweep change rows every window and must not pay
    // a close per bank per window). Off outside the timer mode: pure open
    // page. pumice TASK-044: the arbiter's "last visible demand" rule alone
    // closed rows a just-in-time AXI stream still needed (BUG-027, milder).
    output logic [NUM_BANKS-1:0]       drain_close_ok_o,

    // ---- telemetry (to the *_STATS CSRs; free-running, cleared on reset) ---
    output logic [31:0]                stat_page_hit_o,
    output logic [31:0]                stat_page_miss_o,
    output logic [31:0]                stat_page_empty_o,
    output logic [31:0]                stat_act_o,
    output logic [31:0]                stat_pre_o,
    output logic [31:0]                stat_ref_o,

    // TASK-012. REF_STATS_REF free-runs: refresh is autonomous, so a
    // host-bracketed delta counts every microsecond between two UART reads,
    // not the workload. Measured on the board: a 186 us window carried a raw
    // delta of 61446 -- 479 ms implied, a 2584x overstatement, and near
    // identical across every config because it was timing the HOST.
    //
    // This counts only refreshes that fired WITH WORK PENDING, which is both
    // contamination-free (the CAMs are empty while the host is idle, so those
    // refreshes are not counted) and the number axis 3 actually wants: a
    // refresh during idle costs the workload nothing, one during traffic costs
    // bandwidth. No host arming, no window register, no write trigger -- so
    // nothing here can be fired by RegisterMap.walk().
    input  logic                       demand_i,          // any CAM entry schedulable
    // per bank: a queued column wants this bank's currently open row. Treated
    // as activity by the idle timer and as a veto on the close request: a row
    // with a burst waiting for it is not idle, whatever the command stream
    // looked like (pumice BUG-0XX: four interleaved threads lost 45% to
    // timeout closes of rows their next burst needed).
    input  logic [NUM_BANKS-1:0]       open_row_demand_i,
    // Per-bank ROW HITS (pumice BUG-020). Free-running like every other stat
    // here, so the host subtracts two reads for a window.
    //
    // A hit is a column op to a bank that did NOT need an activation. This is
    // counted from the issued stream directly rather than derived as
    // `col_ops - ACT`: that derivation is unsound under a background-close mode,
    // because a row can be opened, hit by the timeout precharge before its
    // column command issues, and reopened -- two ACTs, one column op, and a
    // NEGATIVE hit count (pumice ISSUE-014, measured 49 ACTs for 48 column ops).
    output logic [31:0]                stat_row_hit_o [NUM_BANKS],

    output logic [31:0]                stat_ref_busy_o
);

    localparam logic [2:0] MODE_DEFAULT      = 3'd0;
    localparam logic [2:0] MODE_STATIC_OPEN  = 3'd1;
    localparam logic [2:0] MODE_STATIC_CLOSE = 3'd2;
    localparam logic [2:0] MODE_FIXED_OPEN   = 3'd3;
    // 4 drain_timeout (2026-10-30, owner: "the one untried variant: try
    // this"): BOTH close mechanisms at once. ap_mode_en_o stays 0, so the
    // pick keeps its legacy auto-precharge rule -- CLOSE_ON_DRAIN, a column
    // carries AP when no same-row entry sits behind it in its bank, the
    // LiteDRAM lookahead close -- and the idle timeout below also runs, so a
    // row left open by a column that HAD a same-row follower (which then
    // did not come in time) is closed in the background after tr_init idle
    // cycles instead of waiting for the next conflict. fixed_open (3) turns
    // the drain AP off; static_open (1) has neither. Reuses the number
    // adapt_time held until 2026-09-27. MEASURED on the board the same
    // day (granite 75 MHz, every / windows / half_threads / concurrent,
    // tr_init 1, 2 and 4): bit-identical to mode 0 on every cell. With the
    // drain AP on, the only row ever left open is one with a same-row
    // follower behind it, and that follower closes it when it fires; the
    // timeout never finds an idle open row that matters. Kept because it
    // is cheap, tested (test_granite_core_page_mode) and answers the
    // question; TASK-003 log 2026-10-30 has the table.
    //
    // REDEFINED the same evening as the HYBRID (owner: "limit the bad from
    // not closing pages, but keep most of the good"). The drain AP lumps two
    // cases together: a column whose bank has a DIFFERENT row queued behind
    // it (a known conflict -- closing now is free and is the open-page win
    // on bank-hop / interleave walks), and a column whose queue simply ran
    // dry (closing then re-activates the same row if a late same-row access
    // arrives -- the fixed_open win on multi-thread and concurrent walks).
    // Mode 4 keeps the AP for the first case always (ap_conflict_only_o, the
    // pick reads its candidate's behind_empty). The second case cannot be
    // told apart at the column: whether the bank's NEXT access is the same
    // row (a late follower -- close loses) or another row (a bank-hop walk
    // -- close wins) is not queued yet. MEASURED on the proxy with the
    // queue-only rule: mode 4 == fixed_open on every family, losing the
    // interleave walk (col_ilv 455 vs drain AP 508). So the drained-queue
    // close is gated by this bank's HISTORY, drain_close_ok_o below (armed
    // when rows here are short-lived and followed by a different row,
    // vetoed by r_keep_open once a close re-opened the same row) -- the
    // evidence the FR-FCFS arbiter's close-on-drain already uses.
    localparam logic [2:0] MODE_DRAIN_TIMEOUT = 3'd4;
    // 4 (adapt_time) and 5 (adapt_access) RETIRED 2026-09-27, by Sean:
    // "remove the adaptive modes as showing no benefit".
    //
    // Mode 4 was MEASURED to be redundant: moving only tr_min moved the result
    // and it landed exactly on the corresponding fixed point every time
    // (tr_min 2 -> 436.8 MB/s == fixed_open TR=2; 8 -> 338.5 == TR=8; 16 ->
    // 327.7 == TR=16). The mistake counter is dominated by the held-too-long
    // case, so TR decayed monotonically to the floor and stayed there --
    // adapt_time WAS fixed_open(tr_min) wearing another name, and mode 3 is
    // already its close path. Its r_mc was also a single GLOBAL counter driving
    // all eight r_tr[b] from one decision, so policy_scope=0's "per-bank TR"
    // could not diverge and was a fiction.
    //
    // Mode 5 was NOT disproven -- it was unproven and mis-plumbed, and is
    // removed as a DECISION rather than a measurement. It drove close_pred_o
    // into ap_close_o, i.e. auto-precharge, which measured 4.9x the activations
    // of a background precharge on identical traffic (160,006 vs 32,400 ACT)
    // and double the read latency. AP commits at the column op, before it is
    // known whether more requests to that row are coming, so on a controller
    // whose value is FR-FCFS reordering to batch same-row columns it fights the
    // reordering that justifies the design. Even a perfect predictor driving AP
    // is bounded by a mechanism that loses; re-plumbing it onto the background
    // precharge was the alternative and was not taken.
    //
    // 6 (rbl_static) and 7 (rbl_dyn) RETIRED 2026-09-26. Measured on silicon
    // at txn_scale=1000 on a workload built specifically to suit them
    // ([[TASK-011]]): mode 6 lost 26% of bandwidth (195.2 -> 144.2 MB/s) by
    // paying +22,827 ACTs to save precharges that never materialised, and
    // mode 7's hill-climb drove its threshold to "never close early", making
    // it bit-identical to plain open page (32,223 vs 32,224 ACTs). The
    // mechanism demonstrably worked -- thrash% fell 100% -> 57.8% -- and still
    // did not pay. A write to policy_mode 6/7 now falls through to the build
    // default, which is what mode 7 measured as anyway.

    logic w_mode_on, w_timeout_on;
    assign w_mode_on    = (policy_mode_i == MODE_STATIC_OPEN)
                       || (policy_mode_i == MODE_STATIC_CLOSE)
                       || (policy_mode_i == MODE_FIXED_OPEN);
    assign w_timeout_on = (policy_mode_i == MODE_FIXED_OPEN)
                       || (policy_mode_i == MODE_DRAIN_TIMEOUT);

    // ---- auto-precharge decision -------------------------------------------
    // ONE producer now: static_close. The predictor path (mode 5) and its
    // pumice_row_pred_table instance are gone with the adaptive modes.
    assign ap_mode_en_o = w_mode_on;
    assign ap_close_o   = (policy_mode_i == MODE_STATIC_CLOSE) ? {NUM_BANKS{1'b1}}
                                                               : '0;
    assign ap_conflict_only_o = (policy_mode_i == MODE_DRAIN_TIMEOUT);



    // ---- the issued stream as the PREDICTOR and the TELEMETRY see it ------
    // (live, or one cycle late with PRED_CMD_REG; the idle timers and the
    // close request below read cmd_valid_i / cmd_bank_i directly)
    logic                 w_pc_valid;
    dram_op_e             w_pc_op;
    logic [BKW-1:0]       w_pc_bank;
    logic [ROW_WIDTH-1:0] w_pc_row;
    logic                 w_pc_ap, w_pc_to, w_pc_demand;
    generate if (PRED_CMD_REG) begin : g_pred_cmd_reg
        logic                 r_pc_valid;
        dram_op_e             r_pc_op;
        logic [BKW-1:0]       r_pc_bank;
        logic [ROW_WIDTH-1:0] r_pc_row;
        logic                 r_pc_ap, r_pc_to, r_pc_demand;
        `ALWAYS_FF_RST(aclk, aresetn, begin
            if (`RST_ASSERTED(aresetn)) begin
                r_pc_valid  <= 1'b0;
                r_pc_op     <= OP_NOP;
                r_pc_bank   <= '0;
                r_pc_row    <= '0;
                r_pc_ap     <= 1'b0;
                r_pc_to     <= 1'b0;
                r_pc_demand <= 1'b0;
            end else begin
                r_pc_valid  <= cmd_valid_i;
                r_pc_op     <= cmd_op_i;
                r_pc_bank   <= cmd_bank_i;
                r_pc_row    <= cmd_row_i;
                r_pc_ap     <= cmd_ap_i;
                r_pc_to     <= pre_is_timeout_i;
                r_pc_demand <= demand_i;
            end
        end)
        assign w_pc_valid  = r_pc_valid;
        assign w_pc_op     = r_pc_op;
        assign w_pc_bank   = r_pc_bank;
        assign w_pc_row    = r_pc_row;
        assign w_pc_ap     = r_pc_ap;
        assign w_pc_to     = r_pc_to;
        assign w_pc_demand = r_pc_demand;
    end else begin : g_pred_cmd_live
        assign w_pc_valid  = cmd_valid_i;
        assign w_pc_op     = cmd_op_i;
        assign w_pc_bank   = cmd_bank_i;
        assign w_pc_row    = cmd_row_i;
        assign w_pc_ap     = cmd_ap_i;
        assign w_pc_to     = pre_is_timeout_i;
        assign w_pc_demand = demand_i;
    end endgenerate

    // ---- issued-stream decodes (predictor / telemetry view) ----------------
    logic w_is_col, w_is_act, w_is_pre, w_is_ref;
    assign w_is_col = w_pc_valid && is_column_op(w_pc_op);
    assign w_is_act = w_pc_valid && (w_pc_op == OP_ACT);
    assign w_is_pre = w_pc_valid && ((w_pc_op == OP_PRE) || (w_pc_op == OP_PREA));
    assign w_is_ref = w_pc_valid && is_refresh_op(w_pc_op);

    // ---- per-bank idle timers (fixed_open / adapt_time) --------------------
    // A bank's timer arms while its row is open and RELOADS on any command to
    // that bank (column keeps the row "warm", ACT starts fresh). At zero the
    // close request raises and holds until the row actually closes (PRE from
    // any path, or refresh). tr==0 disables that bank's timeout entirely
    // (matches "0 = build default" on the CSR field).
    logic [NUM_BANKS-1:0][7:0] r_tr;        // per-bank timeout register (adapt)
    logic [NUM_BANKS-1:0][7:0] r_idle;      // countdown
    logic [NUM_BANKS-1:0]      r_expired;   // sticky until the row closes

    // Effective TR for a bank. With adapt_time retired there is exactly one
    // source: the programmed tr_init. The per-bank r_tr[] registers, the global
    // vs per-bank policy_scope select and the mistake taxonomy that drove them
    // are all gone -- see the mode-retirement note above for why.
    function automatic logic [7:0] f_tr (input int b);
        return tr_init_i;
    endfunction

    // Was this cycle's PRE a TIMEOUT close or a conflict close? Needed by the
    // TELEMETRY below (a timeout close must not mark its bank, so the next ACT
    // classifies as page_empty rather than page_miss), not by any adaptive
    // logic -- it merely used to be declared inside the adapt block, and
    // deleting that block took it with it.
    //
    // The arbiter cannot tell us which branch fired, so we infer: a PRE to a
    // bank whose r_expired is set is a timeout close; any other PRE is a
    // conflict close. Refresh-drain PREs land on active banks whose timers may
    // also have expired -- counting those as timeout closes is harmless, the
    // row was idle-expired either way.
    // Which branch fired is the CORE's knowledge, exported on the command
    // (cmd_timeout_pre_o). Inferring it here from r_expired was ambiguous
    // whenever a demand conflict hit an expired bank -- after a streaming
    // family every bank is expired AND marked keep-open, so a row walk's
    // conflict PREs read as timeout closes and the mark was never cleared
    // (col_ilv 306 -> 254 MB/s in the full-family run, BUG-030).
    logic w_pre_was_timeout, w_is_apcol;
    assign w_pre_was_timeout = w_is_pre && w_pc_to;
    assign w_is_apcol        = w_pc_valid && w_pc_ap;   // RDA / WRA: a predicted close too

    // ---- mistake predictor (pumice BUG-030) ---------------------------------
    // A timeout close whose row the very next ACT to that bank reopens was a
    // mistake: the row was not idle, the stream merely had not reached the
    // bank again yet. One such mistake marks the bank KEEP-OPEN and the idle
    // timer stops naming it, until a CONFLICT precharge (a real row change)
    // clears the mark. No fixed tr_init serves every thread count: four
    // interleaved generators revisit a bank every ~24 cycles, eight every
    // ~70, a single bank-interleaved row walk (col_ilv) every ~120 with a
    // NEW row each time -- the early close is worth 308 / 350 vs 238 / 260
    // there and costs 45% on the streams. The predictor keeps both: a
    // stream pays one reopen per bank, a row walk never trips it (its
    // reopens are different rows). The window cannot help here: with four
    // or more generators in 16 entries, a bank's next burst is usually not
    // admitted when its last column fires, so open_row_demand_i is blind.
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] r_last_row;    // last open row seen per bank
    logic [NUM_BANKS-1:0]                r_to_closed;   // this bank's last close was a timeout close
    logic [NUM_BANKS-1:0]                r_keep_open;   // predictor verdict
    logic [NUM_BANKS-1:0]                r_drain_arm;   // rows on this bank are changing: close on drain
    logic [NUM_BANKS-1:0]                r_last_vld;    // r_last_row holds a row this bank really opened
    localparam int COLCW = $clog2(DRAIN_ARM_MAX_COLS + 2);
    logic [NUM_BANKS-1:0][COLCW-1:0]     r_row_cols;    // columns served by the open row (saturating)
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_last_row  <= '0;
            r_last_vld  <= '0;
            r_to_closed <= '0;
            r_keep_open <= '0;
            r_drain_arm <= '0;
            r_row_cols  <= '0;
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                // track the open row while it is open: the image drops before
                // this block sees the PRE that closed it
                if (bank_row_active_i[b]) begin
                    r_last_row[b] <= bank_open_row_i[b];
                    r_last_vld[b] <= 1'b1;
                end
                // Evidence is gathered only in the timer mode. A close-page
                // mode leaves every row "short" (static_close: one column per
                // ACT) and a mode switch moves to a new region, so the first
                // ACTs after switching into fixed_open would arm on history
                // that says nothing about this mode's traffic (the board-
                // geometry paging sweep lost 17 % of its 8-bank window to one
                // auto-precharge per bank, 2026-10-23).
                if (!w_timeout_on) begin
                    r_last_vld[b]  <= 1'b0;
                    r_drain_arm[b] <= 1'b0;
                    r_row_cols[b]  <= '0;
                end
                if (w_is_pre && (int'(w_pc_bank) == b)) begin
                    r_to_closed[b] <= w_pre_was_timeout;
                    if (!w_pre_was_timeout) r_keep_open[b] <= 1'b0;   // a real row change
                end
                if (w_is_apcol && (int'(w_pc_bank) == b))
                    r_to_closed[b] <= 1'b1;                           // auto-precharge: a predicted close
                if (w_is_act && (int'(w_pc_bank) == b) && r_to_closed[b]
                    && (w_pc_row == r_last_row[b]))
                    r_keep_open[b] <= 1'b1;                           // we closed a row we needed
                // drain-close evidence: an ACT to a different row than the
                // last one, after a SHORT-lived row, arms it; an ACT reopening
                // the last row disarms it. The bank's first ACT is no evidence
                // either way (the reset value of r_last_row is not a row this
                // bank opened). Column count restarts with every ACT.
                // TASK-045, second evidence path: the last close of this bank
                // was a DEMAND precharge (not the timer, not an auto-precharge:
                // !r_to_closed) and the ACT opens a different row -- the bank
                // was closed because another row was wanted, so its rows
                // alternate under demand and the explicit PRE slot would have
                // been an AP for free. Eight streaming generators drift on the
                // W channel and meet in a bank one row apart; with only the
                // short-row path the 256-column rows never armed, and the
                // FR-FCFS core paid an explicit PRE per switch (758 per 16 384
                // columns: 539 vs the per-bank core's 557 MB/s).
                if (w_is_act && (int'(w_pc_bank) == b)) begin
                    r_drain_arm[b] <= r_last_vld[b] && (w_pc_row != r_last_row[b])
                                      && ((r_row_cols[b] <= COLCW'(DRAIN_ARM_MAX_COLS))
                                          || !r_to_closed[b]);
                    r_row_cols[b]  <= '0;
                end else if (w_is_col && (int'(w_pc_bank) == b)
                             && (r_row_cols[b] != {COLCW{1'b1}}))
                    r_row_cols[b]  <= r_row_cols[b] + COLCW'(1);
                if (!w_timeout_on) r_keep_open[b] <= 1'b0;
            end
        end
    end)

    // drain-close permission: registered so the arbiter's pre-pick cone sees
    // a flop (it muxes this by the selected column's bank)
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) drain_close_ok_o <= '0;
        else                        drain_close_ok_o <= {NUM_BANKS{w_timeout_on}} & r_drain_arm & ~r_keep_open;
    )

    generate if (HAS_TIMEOUT_CLOSE) begin : g_timeout
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_idle              <= '0;
            r_expired           <= '0;
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (!w_timeout_on || !bank_row_active_i[b]) begin
                    // Row closed (or engine off): clear.
                    r_idle[b]    <= '0;
                    r_expired[b] <= r_expired[b] && bank_row_active_i[b];
                end else if ((cmd_valid_i && (int'(cmd_bank_i) == b)) || open_row_demand_i[b]) begin
                    // Any command to the bank re-warms the row -- and so does
                    // a queued column for the open row: idle means nobody
                    // wants the row, not merely that nobody has reached it.
                    r_idle[b]    <= f_tr(b);
                    r_expired[b] <= 1'b0;
                end else if (r_idle[b] != 0) begin
                    r_idle[b] <= r_idle[b] - 8'h1;
                    if (r_idle[b] == 8'h1 && f_tr(b) != 0)
                        r_expired[b] <= 1'b1;
                end
            end
        end
    end)

    // ---- background close request ------------------------------------------
    // Lowest-priority: pick the lowest-numbered expired open bank. The arbiter
    // gates on pre_ready/guards; we just name the bank.
    always_comb begin
        timeout_pre_req_o  = 1'b0;
        timeout_pre_bank_o = '0;
        if (w_timeout_on) begin
            for (int b = NUM_BANKS - 1; b >= 0; b--) begin
                // live veto as well: the re-warm above lands a cycle later;
                // and never a bank the predictor marked keep-open
                if (r_expired[b] && bank_row_active_i[b] && !open_row_demand_i[b]
                    && !r_keep_open[b]) begin
                    timeout_pre_req_o  = 1'b1;
                    timeout_pre_bank_o = BKW'(b);
                end
            end
        end
    end

    // ---- telemetry ----------------------------------------------------------
    // Miss vs empty: a wrong-row (conflict) PRE marks its bank; the next ACT
    // to a marked bank is a MISS, to an unmarked bank an EMPTY. Timeout and
    // refresh closes deliberately do NOT mark: the reopen cost after them is
    // the page-empty class.
    end else begin : g_no_timeout
        assign r_idle    = '0;
        assign r_expired = '0;
        assign timeout_pre_req_o  = 1'b0;
        assign timeout_pre_bank_o = '0;
        wire _unused_to = &{1'b0, tr_init_i};
    end endgenerate

    generate if (HAS_TELEMETRY) begin : g_telemetry
    logic [NUM_BANKS-1:0] r_conflict_mark;
    // An activation issued for bank b that has not yet seen its column op.
    logic [NUM_BANKS-1:0] r_act_pending;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_conflict_mark   <= '0;
            stat_page_hit_o   <= 32'h0;
            stat_page_miss_o  <= 32'h0;
            stat_page_empty_o <= 32'h0;
            stat_act_o        <= 32'h0;
            stat_pre_o        <= 32'h0;
            stat_ref_o        <= 32'h0;
            stat_ref_busy_o   <= 32'h0;
            r_act_pending     <= '0;
            for (int b = 0; b < NUM_BANKS; b++) stat_row_hit_o[b] <= 32'h0;
        end else begin
            if (w_is_pre && !w_pre_was_timeout)
                r_conflict_mark[w_pc_bank] <= 1'b1;

            if (w_is_col) stat_page_hit_o <= stat_page_hit_o + 32'h1;

            // Per-bank row hits. `r_act_pending[b]` means "an activation for
            // bank b is still waiting for the column op it was issued for".
            // Set by any ACT to b; cleared by the first column op to b, which
            // is that activation's own access and therefore NOT a hit. A column
            // op arriving with the flag clear found the row already open.
            //
            // The re-activation case (open -> timeout close -> reopen, with no
            // column op in between) simply sets the flag twice, which is why
            // this counts correctly where col_ops - ACT does not.
            if (w_is_act) r_act_pending[w_pc_bank] <= 1'b1;
            if (w_is_col) begin
                if (r_act_pending[w_pc_bank])
                    r_act_pending[w_pc_bank] <= 1'b0;
                else
                    stat_row_hit_o[w_pc_bank] <= stat_row_hit_o[w_pc_bank] + 32'h1;
            end
            if (w_is_act) begin
                stat_act_o <= stat_act_o + 32'h1;
                if (r_conflict_mark[w_pc_bank]) begin
                    stat_page_miss_o <= stat_page_miss_o + 32'h1;
                    r_conflict_mark[w_pc_bank] <= 1'b0;
                end else begin
                    stat_page_empty_o <= stat_page_empty_o + 32'h1;
                end
            end
            if (w_is_pre) stat_pre_o <= stat_pre_o + 32'h1;
            if (w_is_ref) begin
                stat_ref_o <= stat_ref_o + 32'h1;
                // Sampled at the REF's own issue cycle, so it reflects demand
                // at the moment the refresh took the command slot.
                if (w_pc_demand) stat_ref_busy_o <= stat_ref_busy_o + 32'h1;
            end
        end
    end)

    end else begin : g_no_telemetry
        assign stat_page_hit_o   = '0;
        assign stat_page_miss_o  = '0;
        assign stat_page_empty_o = '0;
        assign stat_act_o        = '0;
        assign stat_pre_o        = '0;
        assign stat_ref_o        = '0;
        assign stat_ref_busy_o   = '0;
        assign stat_row_hit_o    = '{default: '0};
        wire _unused_tele = &{1'b0, demand_i};
    end endgenerate

endmodule : mc_page_policy
