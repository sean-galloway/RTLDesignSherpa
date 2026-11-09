// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_timer
// Purpose: One DRAM bank's JEDEC "safe" timing tracker. NO state machine — just
//          a set of preset/decrement countdown timers plus a trivial row-open
//          register. The scheduler (the single command
//          issuer) drives one set_* strobe per issued command; each timer loads
//          its config value on its trigger, free-runs decrement (saturate at 0),
//          and its constraint is "safe" when the count is 0. The per-command
//          `safe_*` outputs are a COMBINATIONAL AND of the relevant timers — a
//          single register stage (the counter), so `safe_*` reflects the just-
//          issued command one cycle later with no multi-stage FSM lag (which was
//          the root of the refresh-vs-ACT / column-vs-PRE hazards).
//
// Timers (loaded on the event, count down, saturate at 0):
//   rcd_cnt    tRCD  ACT -> RD/WR            gates safe_rd / safe_wr
//   ras_cnt    tRAS  ACT -> PRE (min)        gates safe_pre
//   rc_cnt     tRC   ACT -> ACT (same bank)  gates safe_act
//   rp_cnt     tRP   PRE -> ACT              gates safe_act
//   preblk_cnt tRTP (RD) / tWR (WR)          gates safe_pre ONLY
//
// Row state (minimal, NOT an FSM): row_valid + open_row, set on ACT, cleared on
// explicit PRE or when an auto-precharge (RDA/WRA) completes. Auto-precharge is a
// single r_ap_pending bit: once its preblk + tRAS timers clear, the row closes
// internally and tRP is loaded — no scheduler PRE, no extra states.
//
// OPEN-PAGE: RD/WR keep the row open (only preblk + the auto-PRE flag load), so
// column commands stream to an open row at tCCD rate (tCCD/tWTR/tRTW turnaround
// are enforced globally in the shared timers, ANDed by the arbiter).
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_timer
    import mc_common_pkg::*;
#(
    parameter int ROW_WIDTH = 14,
    parameter int TW        = 8,      // timer width
    parameter int LA        = 0,      // advisory lookahead depth, cycles
    // Extrapolate the auto-precharge self-close into safe_act_la_o (see the
    // LOOKAHEAD block). Off keeps the original conservative la for the FRFCFS
    // research core; the per-bank pick core turns it on so an RDA/WRA row
    // switch requests its ACT exactly tRP after the internal close.
    parameter bit LA_AP     = 1'b0,
    // 1 = the COUNTERS load one cycle after the strobe, from a register in
    // this module, at (t - 2) instead of (t - 1). The strobe is the end of
    // the scheduler's fire cone, and the counter loads were its widest set
    // of endpoints on the board (granite at 100 MHz, 2026-10-28: 59 of the
    // 89 paths within 0.3 ns of failing ended in these five counters). With
    // the lag the fire cone drives one register stage here and nothing
    // behind it; the row image (row_valid, open_row, the AP bit) stays on
    // the live strobe, so every row-state reader sees the command when it
    // always did. The readiness outputs stay EXACT: in the one cycle between
    // the strobe and the load the pending load is folded into every counter
    // read (the "effective" view below), so safe_* and the lookahead twins
    // read what the live load would have given them. 0 = the live load.
    parameter bit SET_LAG   = 1'b0,
    // 1 = the zero-detect / "within LA" compares (and the auto-precharge
    // lookahead sums) are REGISTERED from the counters' next values, so a
    // readiness output is one LUT from flops (memory-controllers MC-011,
    // 2026-11-08; see the flags block). Cycle-exact either way; with
    // SET_LAG = 1 every D input is register-only. 0 = the live compares.
    parameter bit ZF_REG    = 1'b0
) (
    input  logic                 clk,
    input  logic                 rst_n,

    // JEDEC timing config, PRE-DERIVED by the parent (mc_bank_timers) from the
    // CSRs once for all banks (memory-controllers MC-007, ISSUE-001 row 6,
    // 2026-11-07). Until then each of the eight timers redid the same
    // subtractions and compares on the live CSR every cycle: the counter
    // loads f_ld(t, LD) = max(t - LD, 0), the auto-precharge reload
    // f_ld(t_rp, 1), the "t <= 1" and "t <= LA + 1" effective-view flags and
    // the f_ld(t, 1) waits. The parent registers them; the CSRs are static
    // during traffic, so the one-cycle lag at programming time is invisible.
    // The formal harness computes the same values from its free timings.
    input  logic [TW-1:0]        ld_rcd_i,   // f_ld(t_rcd, LD)
    input  logic [TW-1:0]        ld_ras_i,   // f_ld(t_ras, LD)
    input  logic [TW-1:0]        ld_rc_i,    // f_ld(t_rc,  LD)
    input  logic [TW-1:0]        ld_rp_i,    // f_ld(t_rp,  LD)   explicit PRE
    input  logic [TW-1:0]        ld_rp1_i,   // f_ld(t_rp,  1)    auto-precharge self-close
    input  logic [TW-1:0]        ld_rtp_i,   // f_ld(t_rtp, LD)   RD -> earliest PRE
    input  logic [TW-1:0]        ld_wr_i,    // f_ld(t_wr,  LD)   WR -> earliest PRE (incl WL+BL/2)
    input  logic [TW-1:0]        t_rp_i,     // tRP itself (the lookahead sum)
    input  logic                 rtp_le1_i,  // t_rtp <= 1
    input  logic                 wr_le1_i,   // t_wr  <= 1
    input  logic                 rcd_la_i,   // t_rcd <= LA + 1
    input  logic                 ras_la_i,   // t_ras <= LA + 1
    input  logic                 rc_la_i,    // t_rc  <= LA + 1
    input  logic                 rp_la_i,    // t_rp  <= LA + 1
    input  logic                 rtp_la_i,   // t_rtp <= LA + 1
    input  logic                 wr_la_i,    // t_wr  <= LA + 1
    input  logic [TW-1:0]        rtp_w1_i,   // f_ld(t_rtp, 1)
    input  logic [TW-1:0]        wr_w1_i,    // f_ld(t_wr,  1)
    input  logic [TW-1:0]        ras_w1_i,   // f_ld(t_ras, 1)

    // preset strobes from the scheduler (this bank only; parent gates by bank)
    input  logic                 set_act_i,
    input  logic                 set_rd_i,
    input  logic                 set_wr_i,
    input  logic                 set_pre_i,
    input  logic                 set_ap_i,  // auto-precharge qualifier on RD/WR
    input  logic [ROW_WIDTH-1:0] row_i,     // ACT row

    // per-command "safe" (combinational — single register stage behind)
    output logic                 safe_act_o,
    output logic                 safe_rd_o,
    output logic                 safe_wr_o,
    output logic                 safe_pre_o,

    // ADVISORY "will be safe LA cycles from now" (see the block at the bottom).
    // NOT a permission to issue -- the scheduler re-checks the live safe_*
    // above at its final stage. LA=0 makes each of these identical to its
    // safe_*_o twin.
    output logic                 safe_act_la_o,
    output logic                 safe_rdwr_la_o,
    output logic                 safe_pre_la_o,

    // row tracking
    output logic                 row_valid_o,
    output logic [ROW_WIDTH-1:0] open_row_o,
    output bank_state_e          state_o,

    // observability
    output logic                 obs_rcd_nz_o,
    output logic                 obs_preblk_nz_o,
    output logic                 obs_ras_nz_o,
    output logic                 obs_ap_pending_o
);

    logic [TW-1:0]        r_rcd, r_ras, r_rc, r_rp, r_preblk;
    logic                 r_row_valid;
    logic [ROW_WIDTH-1:0] r_open_row;
    logic                 r_ap_pending;

    // ---- load strobes: live, or one register late (SET_LAG) --------------
    logic w_ld_act, w_ld_rd, w_ld_wr, w_ld_pre;
    generate if (SET_LAG) begin : g_set_lag
        logic r_set_act, r_set_rd, r_set_wr, r_set_pre;
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_set_act <= 1'b0; r_set_rd <= 1'b0; r_set_wr <= 1'b0; r_set_pre <= 1'b0;
            end else begin
                r_set_act <= set_act_i; r_set_rd <= set_rd_i; r_set_wr <= set_wr_i; r_set_pre <= set_pre_i;
            end
        )
        assign w_ld_act = r_set_act;
        assign w_ld_rd  = r_set_rd;
        assign w_ld_wr  = r_set_wr;
        assign w_ld_pre = r_set_pre;
    end else begin : g_set_live
        assign w_ld_act = set_act_i;
        assign w_ld_rd  = set_rd_i;
        assign w_ld_wr  = set_wr_i;
        assign w_ld_pre = set_pre_i;
    end endgenerate

    // Load value: the command fired D cycles before the load is visible, so
    // the counter loads (t - D), saturating at 0, and "safe at count == 0"
    // lands exactly at C + t. D = 1 live (the t-1 load of MC-003 2026-10-17,
    // owner-approved with the BL8 control measured), 2 with SET_LAG. The
    // auto-precharge self-close below is internal and always loads at D = 1.
    localparam int LD = SET_LAG ? 2 : 1;
    function automatic logic [TW-1:0] f_ld(input logic [TW-1:0] t, input int d);
        return (t <= TW'(d)) ? '0 : (t - TW'(d));
    endfunction

    // ---- the EFFECTIVE counters: the pending load folded in --------------
    // With SET_LAG, the cycle in which w_ld_* is high is the cycle after the
    // command: the counter still holds its pre-command value while the
    // constraint it is about to load is in force. Every reader below goes
    // through these, never through r_* directly, so the outputs are what
    // the live load would give them. Live (SET_LAG = 0) the w_pend_* terms
    // are constant 0 and everything folds back to the plain counter reads.
    //   rcd / ras / rc (ACT) and rp (PRE): a 0- or 1-cycle tRCD / tRAS / tRC
    //   / tRP is no DRAM timing, so "zero" is simply masked by the pending
    //   load (keeps the zero-detect one LUT); such a value would read one
    //   cycle conservative.
    //   preblk (RD / WR): tRTP IS one cycle at the board clock, so this one
    //   is exact -- a pending RD reads zero iff t_rtp <= 1.
    logic w_pend_act, w_pend_rd, w_pend_wr, w_pend_pre;
    assign w_pend_act = SET_LAG && w_ld_act;
    assign w_pend_rd  = SET_LAG && w_ld_rd;
    assign w_pend_wr  = SET_LAG && w_ld_wr;
    assign w_pend_pre = SET_LAG && w_ld_pre;

    // ---- next counter values, computed once -------------------------------
    // tRCD / tRAS / tRC: reload on ACT, else count down (saturate at 0).
    // Load (t - LD), saturating -- see f_ld: "safe at count == 0" lands
    // exactly at C + t, JEDEC-exact, the same semantics the tCCD forward
    // counter uses (mc_bank_sched r_tccd_fwd). Loading t would enforce t+1
    // (one cycle conservative per transition, which is what made the
    // col_major bubble 9 against a 6-cycle floor; MC-003 2026-10-17).
    // tRP: reload on the auto-PRE fire (live, D = 1) or the explicit PRE
    // strobe, else count down. The self-close is the later of the two when
    // both land in one cycle, so it wins (conservative).
    // preblk: reload on RD (tRTP) / WR (tWR), else count down.
    logic w_rcd_z, w_ras_z, w_rc_z, w_rp_z, w_preblk_z;   // "count is zero", effective
    logic w_ap_fire;
    logic [TW-1:0] w_rcd_nxt, w_ras_nxt, w_rc_nxt, w_rp_nxt, w_preblk_nxt;
    function automatic logic [TW-1:0] f_dec(input logic [TW-1:0] c);
        return (c != '0) ? (c - 1'b1) : '0;
    endfunction
    assign w_rcd_nxt    = w_ld_act  ? ld_rcd_i : f_dec(r_rcd);
    assign w_ras_nxt    = w_ld_act  ? ld_ras_i : f_dec(r_ras);
    assign w_rc_nxt     = w_ld_act  ? ld_rc_i  : f_dec(r_rc);
    assign w_rp_nxt     = w_ap_fire ? ld_rp1_i : w_ld_pre ? ld_rp_i : f_dec(r_rp);
    assign w_preblk_nxt = w_ld_rd   ? ld_rtp_i : w_ld_wr  ? ld_wr_i : f_dec(r_preblk);

    // ---- the zero-detect and "within LA" flags ---------------------------
    // ZF_REG = 0: compares on the live counters (the original form).
    // ZF_REG = 1 (memory-controllers MC-011, 2026-11-08): the same compares
    // on NEXT cycle's counter values, registered, so each readiness output
    // is one LUT from flops instead of an 8-bit zero-detect, a mux and an
    // AND in series. Cycle-exact: a flag registered from w_*_nxt at cycle N
    // reads at N+1 what the live compare on r_* reads at N+1. The D inputs
    // are register-only when SET_LAG = 1 (the strobes are the lagged
    // registers), which is why the parent ties ZF_REG to EVT_REG: the
    // granite 100 MHz census had 3 LUTs and 2.5 ns of wire between a bank
    // counter and the pick's fire stage on every failing fire-cone path.
    // Equivalence to the live form is proved against a golden copy in
    // formal/mc_common/mc_bank_timer (task `equiv`).
    logic w_rcd_z0, w_ras_z0, w_rc_z0, w_rp_z0, w_preblk_z0;   // count == 0
    logic w_rcd_la0, w_ras_la0, w_rc_la0, w_rp_la0, w_preblk_la0;   // count <= LA
    generate if (ZF_REG) begin : g_zf_reg
        logic r_rcd_z0, r_ras_z0, r_rc_z0, r_rp_z0, r_preblk_z0;
        logic r_rcd_la0, r_ras_la0, r_rc_la0, r_rp_la0, r_preblk_la0;
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_rcd_z0 <= 1'b1; r_ras_z0 <= 1'b1; r_rc_z0 <= 1'b1; r_rp_z0 <= 1'b1; r_preblk_z0 <= 1'b1;
                r_rcd_la0 <= 1'b1; r_ras_la0 <= 1'b1; r_rc_la0 <= 1'b1; r_rp_la0 <= 1'b1; r_preblk_la0 <= 1'b1;
            end else begin
                r_rcd_z0    <= (w_rcd_nxt    == '0);
                r_ras_z0    <= (w_ras_nxt    == '0);
                r_rc_z0     <= (w_rc_nxt     == '0);
                r_rp_z0     <= (w_rp_nxt     == '0);
                r_preblk_z0 <= (w_preblk_nxt == '0);
                r_rcd_la0    <= (w_rcd_nxt    <= TW'(LA));
                r_ras_la0    <= (w_ras_nxt    <= TW'(LA));
                r_rc_la0     <= (w_rc_nxt     <= TW'(LA));
                r_rp_la0     <= (w_rp_nxt     <= TW'(LA));
                r_preblk_la0 <= (w_preblk_nxt <= TW'(LA));
            end
        )
        assign w_rcd_z0 = r_rcd_z0;  assign w_ras_z0 = r_ras_z0;  assign w_rc_z0 = r_rc_z0;
        assign w_rp_z0  = r_rp_z0;   assign w_preblk_z0 = r_preblk_z0;
        assign w_rcd_la0 = r_rcd_la0;  assign w_ras_la0 = r_ras_la0;  assign w_rc_la0 = r_rc_la0;
        assign w_rp_la0  = r_rp_la0;   assign w_preblk_la0 = r_preblk_la0;
    end else begin : g_zf_live
        assign w_rcd_z0    = (r_rcd    == '0);
        assign w_ras_z0    = (r_ras    == '0);
        assign w_rc_z0     = (r_rc     == '0);
        assign w_rp_z0     = (r_rp     == '0);
        assign w_preblk_z0 = (r_preblk == '0);
        assign w_rcd_la0    = (r_rcd    <= TW'(LA));
        assign w_ras_la0    = (r_ras    <= TW'(LA));
        assign w_rc_la0     = (r_rc     <= TW'(LA));
        assign w_rp_la0     = (r_rp     <= TW'(LA));
        assign w_preblk_la0 = (r_preblk <= TW'(LA));
    end endgenerate

    assign w_rcd_z    = w_rcd_z0 && !w_pend_act;
    assign w_ras_z    = w_ras_z0 && !w_pend_act;
    assign w_rc_z     = w_rc_z0  && !w_pend_act;
    assign w_rp_z     = w_rp_z0  && !w_pend_pre;
    assign w_preblk_z = w_pend_rd ? rtp_le1_i
                      : w_pend_wr ? wr_le1_i
                      :             w_preblk_z0;

    // auto-precharge fires once the read/write recovery (preblk) AND tRAS elapse.
    assign w_ap_fire = r_ap_pending && w_preblk_z && w_ras_z;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rcd <= '0; r_ras <= '0; r_rc <= '0; r_rp <= '0; r_preblk <= '0;
            r_row_valid <= 1'b0; r_open_row <= '0; r_ap_pending <= 1'b0;
        end else begin
            r_rcd    <= w_rcd_nxt;
            r_ras    <= w_ras_nxt;
            r_rc     <= w_rc_nxt;
            r_rp     <= w_rp_nxt;
            r_preblk <= w_preblk_nxt;

            // row-open + auto-precharge bit (ACT > explicit PRE > auto-PRE).
            // Always on the LIVE strobe, SET_LAG or not: the row image is
            // what the scheduler's decode and the page policy read, and it
            // sees the command exactly when it always did.
            if (set_act_i) begin
                r_row_valid  <= 1'b1;
                r_open_row   <= row_i;
                r_ap_pending <= 1'b0;
            end else if (set_pre_i) begin
                r_row_valid  <= 1'b0;
                r_ap_pending <= 1'b0;
            end else if (w_ap_fire) begin
                r_row_valid  <= 1'b0;
                r_ap_pending <= 1'b0;
            end else if (set_rd_i || set_wr_i) begin
                r_ap_pending <= set_ap_i;
            end
        end
    )

    // ---- combinational "safe" (single register stage = the timers) ----------
    // ACT: bank precharged (row closed), tRP since PRE, tRC since last ACT.
    assign safe_act_o = !r_row_valid && w_rp_z && w_rc_z;
    // RD/WR: row open, tRCD met, not auto-precharging.
    assign safe_rd_o  = r_row_valid && w_rcd_z && !r_ap_pending;
    assign safe_wr_o  = safe_rd_o;
    // PRE: row open, tRAS + tRTP/tWR met, not auto-precharging.
    assign safe_pre_o = r_row_valid && w_ras_z && w_preblk_z && !r_ap_pending;

    // ---- LOOKAHEAD: "will be safe in LA cycles" (ADVISORY ONLY) -----------
    // Every constraint above is a saturating down-counter that decrements once
    // per cycle, so `r_X <= LA` is EXACTLY "r_X reaches 0 within LA cycles" --
    // provided nothing reloads it in between. A reload can only come from a
    // command the SCHEDULER issues, which is why these are advisory: the
    // scheduler re-checks the live safe_* at its final stage before anything
    // leaves, so a lookahead that guessed wrong costs one dropped pick (a
    // bubble), never a JEDEC violation. That is the whole contract here.
    //
    // The row-state terms are NOT counters and are deliberately NOT
    // extrapolated:
    //   - r_row_valid is set by an ACT and cleared by a PRE that the scheduler
    //     itself issues; predicting it would mean predicting the scheduler
    //     from inside the timer.
    //   - the auto-precharge self-close IS autonomous, but it RELOADS tRP when
    //     it fires, so `r_rp <= LA` is WRONG for an AP-pending bank -- the true
    //     condition is max(preblk,ras) + t_rp <= LA. With LA_AP=0 that term is
    //     left out and an AP-pending bank reads not-safe (conservative).
    //     With LA_AP=1 it is included EXACTLY: the close fires in the cycle
    //     max(preblk,ras) reaches 0 (call it X), r_rp is loaded t_rp-1 at the
    //     end of X and reaches 0 at X+t_rp, so "ACT safe within LA cycles"
    //     is max(preblk,ras) + t_rp <= LA (and tRC, which keeps counting
    //     through the close, must itself be within LA).
    // Both omissions are conservative: they can only UNDER-report safety.
    //
    // LA=0 collapses every term to its safe_*_o twin, so the plumbing can be
    // landed and gated as a provable no-op before the depth is turned up
    // (with SET_LAG the twin is the exact form of the masked terms above:
    // a pending 1-cycle tRCD / tRP reads "within 0" here and not-safe there).
    //
    // A PENDING load (SET_LAG, the cycle after the command) reaches zero at
    // C + t, which is t - 1 cycles from now: "within LA" is t <= LA + 1,
    // and the self-close wait is t - 1. Live these terms are the plain reads.
    logic w_rcd_la, w_ras_la, w_rc_la, w_rp_la, w_preblk_la;
    assign w_rcd_la    = w_pend_act ? rcd_la_i : w_rcd_la0;
    assign w_ras_la    = w_pend_act ? ras_la_i : w_ras_la0;
    assign w_rc_la     = w_pend_act ? rc_la_i  : w_rc_la0;
    assign w_rp_la     = w_pend_pre ? rp_la_i  : w_rp_la0;
    assign w_preblk_la = w_pend_rd  ? rtp_la_i
                       : w_pend_wr  ? wr_la_i
                       :              w_preblk_la0;
    // The self-close extrapolation, max(preblk, ras) + t_rp <= LA, is read
    // under r_ap_pending only. A pending ACT never coexists with it (the
    // live ACT strobe clears r_ap_pending in the cycle that sets the lagged
    // strobe), so the tRAS wait is the counter's own; the pending RD / WR
    // waits are the CSR-derived (t - 1) values. ZF_REG registers the three
    // sums on the next counter values, like the flags above.
    function automatic logic f_ap_le(input logic [TW-1:0] pw, input logic [TW-1:0] rw);
        logic [TW:0]   ap_wait;
        logic [TW+1:0] ap_in;
        ap_wait = (pw > rw) ? {1'b0, pw} : {1'b0, rw};
        ap_in   = {1'b0, ap_wait} + {2'b00, t_rp_i};
        return (ap_in <= (TW+2)'(LA));
    endfunction
    logic w_ap_le_cnt, w_ap_le_rd, w_ap_le_wr;   // the sum within LA: counters' own / pending RD / pending WR
    generate if (ZF_REG) begin : g_ap_reg
        logic r_ap_le_cnt, r_ap_le_rd, r_ap_le_wr;
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_ap_le_cnt <= 1'b0; r_ap_le_rd <= 1'b0; r_ap_le_wr <= 1'b0;
            end else begin
                r_ap_le_cnt <= f_ap_le(w_preblk_nxt, w_ras_nxt);
                r_ap_le_rd  <= f_ap_le(rtp_w1_i,     w_ras_nxt);
                r_ap_le_wr  <= f_ap_le(wr_w1_i,      w_ras_nxt);
            end
        )
        assign w_ap_le_cnt = r_ap_le_cnt;
        assign w_ap_le_rd  = r_ap_le_rd;
        assign w_ap_le_wr  = r_ap_le_wr;
        wire _unused_ap_reg = &{1'b0, ras_w1_i};   // the pending-ACT wait is dead under r_ap_pending
    end else begin : g_ap_live
        logic [TW-1:0] w_ras_wait;
        assign w_ras_wait  = w_pend_act ? ras_w1_i : r_ras;
        assign w_ap_le_cnt = f_ap_le(r_preblk, w_ras_wait);
        assign w_ap_le_rd  = f_ap_le(rtp_w1_i, w_ras_wait);
        assign w_ap_le_wr  = f_ap_le(wr_w1_i,  w_ras_wait);
    end endgenerate
    logic w_ap_act_la;
    assign w_ap_act_la = LA_AP && r_row_valid && r_ap_pending
                      && (w_pend_rd ? w_ap_le_rd : w_pend_wr ? w_ap_le_wr : w_ap_le_cnt)
                      && w_rc_la;
    assign safe_act_la_o  = (!r_row_valid && w_rp_la && w_rc_la)
                         || w_ap_act_la;
    assign safe_rdwr_la_o = r_row_valid  && w_rcd_la && !r_ap_pending;
    assign safe_pre_la_o  = r_row_valid  && w_ras_la && w_preblk_la && !r_ap_pending;

    assign row_valid_o = r_row_valid;
    assign open_row_o  = r_open_row;

    // derived state (observability only; no downstream logic depends on it)
    always_comb begin
        if (r_row_valid) state_o = (r_rcd != '0) ? BANK_ACTIVATING : BANK_ACTIVE;
        else             state_o = (r_rp  != '0) ? BANK_PRECHARGING : BANK_IDLE;
    end

    assign obs_rcd_nz_o     = (r_rcd    != '0);
    assign obs_preblk_nz_o  = (r_preblk != '0);
    assign obs_ras_nz_o     = (r_ras    != '0);
    assign obs_ap_pending_o = r_ap_pending;

endmodule : mc_bank_timer
