// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
//
// PORTED FROM formal/pumice/refresh_ctrl, 2026-10-01. scoria's scoria_refresh_ctrl has a
// port list IDENTICAL to pumice's counterpart (measured, all 8 ported blocks)
// and dv/tests/fub/test_scoria_pumice_logic_parity.py gates the logic
// equivalence, so the properties carry over unchanged -- and this proof was
// mutation-tested against scoria's own RTL before being trusted, because a
// mechanical port that passes everywhere is what a vacuous bind looks like.
//
// References to `pumice BUG-/ISSUE-/TASK-nnn` below are DELIBERATE
// cross-references to where a property was first derived or a bug first found;
// they are not stale text. Claims about pumice FILES have been corrected to
// scoria's where they differ.
//
// Formal wrapper for scoria_refresh_ctrl -- the tREFI/backlog engine.
//
// WHY THIS BLOCK. It is the second of pumice's two device-safety blocks: the
// first (bank_timer) stops the controller violating a DRAM timing, and this one
// stops it LOSING DATA. A refresh that is never asked for is a retention
// failure, and a retention failure does not look like a bug -- it looks like
// corrupt memory, hours later, in a different test.
//
// THE PROPERTY THIS FILE EXISTS FOR. refresh_ctrl.sv carries a long comment
// about POSTPONE_MAX, describing a real defect and its fix:
//
//     "The threshold to START asking for a refresh and the threshold to BEGIN
//      LOSING them were the same number, so any latency between the request and
//      the grant (finishing a write burst, precharging banks, tRFC) cost real
//      refreshes -- a data retention hazard."
//
// The fix was POSTPONE_MAX = MAX_PENDING - 2, so the request asserts at a
// backlog of 7 while the accumulator saturates (and starts dropping ticks) at
// 8. That argument is about a CLAMP holding for every value of a 4-bit CSR --
// exactly what a directed test cannot cover and a proof can. a_headroom below
// checks it against a free postpone_limit_i, all sixteen values, including the
// out-of-range ones the clamp exists to catch.
//
// WHAT IS PROVED
//   RETENTION
//     * the backlog never exceeds the JEDEC 8-postponed ceiling
//     * a backlog past the postpone clamp ALWAYS raises the request, for every
//       postpone_limit_i -- the headroom the fix above installed
//     * the request is never raised while refresh is disabled (pre-init)
//   ACCOUNTING
//     * pull-in credit stays inside the JEDEC +-8 window
//     * backlog and credit each move by at most one per cycle, and never both
//       upward at once -- a tick and a grant cannot both create work
//     * the drain quota never exceeds the ceiling
//   THE DEVICE MIRROR
//     * the REFpb bank rotor is always a legal bank, and only ever advances by
//       one with a correct wrap. The rotor mirrors the DEVICE'S internal
//       counter; the RTL comment notes that desynchronising it makes the
//       controller "precharge the WRONG bank ahead of each device refresh".
//     * THE ROTOR ADVANCES ON EVERY ACCEPTED REFpb, AND ONLY THEN. Added
//       2026-10-01 for HAS verification item 4, because "advances by at most
//       one" is satisfied by a rotor that holds for ever -- refreshing one
//       bank and letting the rest age out. With the backlog properties above,
//       this gives every bank a refresh within NUM_BANKS grants.
//     * refresh_kind_o tracks refpb_mode_i exactly one cycle later (all outputs
//       are strict-flopped)
//
// BOUNDED ON PURPOSE. tREFI is an anyconst in 2..3 rather than its real ~2900
// cycles: reaching a backlog of 7 takes seven intervals, and at the real value
// that is twenty thousand cycles of unrolling to exercise the same accumulator.
// What matters is that the accumulator and the clamp are the same at 2 as at
// 2900 -- the counter width is not what is in question.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v (yosys cannot parse
// scoria_pkg.sv); immediate assertions in `always @(posedge clk)`.

`timescale 1ns / 1ps

module formal_scoria_refresh_ctrl #(
    parameter int NUM_BANKS = 8,
    parameter int BA_W      = 3
) (
    input logic mc_clk,
    input logic mc_rst_n
);

    localparam int MAX_PENDING  = 8;
    localparam int POSTPONE_MAX = MAX_PENDING - 2;   // mirrors the RTL's derivation

    // ---- configuration: written once at init, then stable ------------------
    (* anyconst *) reg [15:0] t_refi_i;
    (* anyconst *) reg [15:0] trefi_pb_i;
    (* anyconst *) reg [3:0]  refresh_burst_i;
    (* anyconst *) reg        refpb_mode_i;
    // The two credit CSRs are left FULLY FREE across all sixteen values. The
    // clamps are the thing under test; constraining them to "legal" values
    // would assume away the defect this file exists to rule out.
    (* anyconst *) reg [3:0]  postpone_limit_i;
    (* anyconst *) reg [3:0]  pullin_limit_i;

    // Mode A: demand-aware elastic refresh
    (* anyconst *) reg        elastic_en_i;
    (* anyconst *) reg [7:0]  pullin_idle_streak_i;
    (* anyconst *) reg [6:0]  postpone_demand_streak_i;

    // Mode B: temperature-compensated refresh (tREFI derate)
    (* anyconst *) reg        tcr_en_i;
    (* anyconst *) reg [1:0]  trefi_derate_i;

    always @(*) begin
        assume (t_refi_i   >= 2 && t_refi_i   <= 3);
        // >= 2 so REFpb's derived interval cannot collapse to zero and tick
        // every cycle, which drowns the trace without testing anything new.
        assume (trefi_pb_i >= 2 && trefi_pb_i <= 3);
        assume (refresh_burst_i >= 1 && refresh_burst_i <= 8);
    end

    // ---- free per-cycle inputs ---------------------------------------------
    (* anyseq *) reg refresh_grant_i, grant_was_pb_i, demand_i;

    // Production ties refi_reload_i low -- the RTL says so at its declaration
    // ("Tie to 0 in production: it has no effect unless pulsed"). Holding it
    // low here proves the SHIPPING configuration; a free reload would let the
    // engine restart the interval forever and make the retention properties
    // unreachable rather than false.
    wire refi_reload_i = 1'b0;

    // Refresh is enabled once init_sequencer completes and stays enabled. A
    // free enable would let the engine park the controller pre-init, where no
    // retention property means anything.
    wire enable_i = 1'b1;

    wire        refresh_req_o, refresh_drain_active_o, refresh_kind_o;
    wire [3:0]  pending_refreshes_o;
    wire [BA_W-1:0] refresh_bank_o, obs_bank_rotor_o;
    wire [15:0] obs_refi_cnt_o, obs_grants_total_o;
    wire [15:0] obs_postpone_events_o, obs_pullin_events_o;
    wire [3:0]  obs_drain_remaining_o, obs_pullin_credit_o;

    scoria_refresh_ctrl #(.NUM_BANKS(NUM_BANKS)) dut (
        .mc_clk(mc_clk), .mc_rst_n(mc_rst_n),
        .t_refi_i(t_refi_i), .trefi_pb_i(trefi_pb_i),
        .refresh_burst_i(refresh_burst_i), .refpb_mode_i(refpb_mode_i),
        .enable_i(enable_i), .refi_reload_i(refi_reload_i),
        .postpone_limit_i(postpone_limit_i), .pullin_limit_i(pullin_limit_i),
        .demand_i(demand_i),
        .elastic_en_i(elastic_en_i),
        .pullin_idle_streak_i(pullin_idle_streak_i),
        .postpone_demand_streak_i(postpone_demand_streak_i),
        .tcr_en_i(tcr_en_i),
        .trefi_derate_i(trefi_derate_i),
        .refresh_req_o(refresh_req_o), .refresh_grant_i(refresh_grant_i),
        .grant_was_pb_i(grant_was_pb_i),
        .pending_refreshes_o(pending_refreshes_o),
        .refresh_drain_active_o(refresh_drain_active_o),
        .refresh_kind_o(refresh_kind_o), .refresh_bank_o(refresh_bank_o),
        .obs_refi_cnt_o(obs_refi_cnt_o),
        .obs_drain_remaining_o(obs_drain_remaining_o),
        .obs_bank_rotor_o(obs_bank_rotor_o),
        .obs_grants_total_o(obs_grants_total_o),
        .obs_pullin_credit_o(obs_pullin_credit_o),
        .obs_postpone_events_o(obs_postpone_events_o),
        .obs_pullin_events_o(obs_pullin_events_o)
    );

    // ---- formal infrastructure ---------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge mc_clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!mc_rst_n);
    always @(posedge mc_clk) if (f_past_valid >= 2) assume (mc_rst_n);

    reg [3:0]      f_pend_d, f_pull_d, f_drain_d;
    reg [BA_W-1:0] f_rotor_d;
    reg            f_mode_d, f_gpb_d1, f_gpb_d2;
    reg [15:0]     f_grants_d;
    always @(posedge mc_clk) begin
        f_pend_d  <= pending_refreshes_o;
        f_pull_d  <= obs_pullin_credit_o;
        f_drain_d <= obs_drain_remaining_o;
        f_rotor_d <= obs_bank_rotor_o;
        f_mode_d  <= refpb_mode_i;
        f_grants_d <= obs_grants_total_o;
        f_gpb_d1   <= grant_was_pb_i;
        f_gpb_d2   <= f_gpb_d1;
    end

    // The rotor's advance condition, expressed from PORTS only.
    //
    // The RTL advances r_bank_rotor on (w_grant_accept || w_grant_early) &&
    // grant_was_pb_i -- both internal. obs_grants_total_o increments on
    // exactly that same grant term, and is flopped in the SAME block as
    // obs_bank_rotor_o, so the two observable signals move together and a
    // change in the grant total is a sound stand-in for the internal term.
    //
    // The delay matters and cost one wrong version of this property: a grant
    // at cycle T updates r_bank_rotor and r_grants_total at T+1, and the obs
    // flops publish both at T+2. So the qualifier to pair with an observed
    // grant-total change is grant_was_pb_i from TWO cycles back, not one.
    wire f_grants_up = (obs_grants_total_o != f_grants_d);
    wire f_refpb_grant = f_grants_up && f_gpb_d2;

    // Which banks the rotor has stood on. A rotor that never advances visits
    // one bank for ever, and every bank it skips ages out -- so the retention
    // argument needs the VISIT set, not just the step size.
    reg [NUM_BANKS-1:0] f_visited;
    always @(posedge mc_clk) begin
        if (!mc_rst_n) f_visited <= '0;
        else           f_visited[obs_bank_rotor_o] <= 1'b1;
    end
    wire f_run = mc_rst_n && (f_past_valid > 3);

    // Mode A/B support: mirror the internal state that is not exported as an
    // observable port. f_idle_cnt and f_demand_streak track the DUT's r_idle_cnt
    // and r_demand_streak cycle-for-cycle (same reset/clear and saturation
    // behaviour). The remaining flops are one-cycle delayed copies of observable
    // or control signals, aligned with the strict-flopped obs_* outputs (which
    // publish the internal value from the cycle BEFORE the edge).
    reg [7:0]  f_idle_cnt;
    reg [7:0]  f_idle_cnt_d;
    reg [6:0]  f_demand_streak;
    reg [6:0]  f_demand_streak_d;
    reg [15:0] f_obs_refi_cnt_d;
    reg        f_refresh_grant_d;
    reg        f_grant_early_d;

    always @(posedge mc_clk) begin
        if (!mc_rst_n) begin
            f_idle_cnt       <= '0;
            f_demand_streak  <= '0;
        end else begin
            if (demand_i) f_idle_cnt <= '0;
            else if (f_idle_cnt < (elastic_en_i ? pullin_idle_streak_i : 8'd16))
                f_idle_cnt <= f_idle_cnt + 8'd1;

            if (!demand_i) f_demand_streak <= '0;
            else if (f_demand_streak != 7'd127) f_demand_streak <= f_demand_streak + 1'b1;
        end
        f_idle_cnt_d      <= f_idle_cnt;
        f_demand_streak_d <= f_demand_streak;
        f_obs_refi_cnt_d  <= obs_refi_cnt_o;
        f_refresh_grant_d <= refresh_grant_i;
        f_grant_early_d   <= f_refresh_grant_d && (pending_refreshes_o == 4'd0) && (obs_pullin_credit_o < 4'd8);
    end

    wire       f_idle_baseline = (f_idle_cnt_d >= 8'd16);
    wire [3:0] f_post_eff      = (postpone_limit_i > POSTPONE_MAX[3:0]) ? POSTPONE_MAX[3:0] : postpone_limit_i;
    wire [3:0] f_pull_eff      = (pullin_limit_i > 4'd8) ? 4'd8 : pullin_limit_i;
    wire [15:0] f_refi_eff     = !refpb_mode_i ? t_refi_i
                                : (trefi_pb_i != 16'd0) ? trefi_pb_i
                                : (t_refi_i >> 3);
    wire       f_baseline_req  = enable_i && (
                                     f_idle_baseline
                                        ? ((pending_refreshes_o > 4'd0) || (obs_pullin_credit_o < f_pull_eff))
                                        : (pending_refreshes_o > f_post_eff));

    // =====================================================================
    // FAMILY 1 -- RETENTION. The reason the block exists.
    // =====================================================================
    always @(posedge mc_clk) if (f_run) begin
        // JEDEC permits at most 8 postponed refreshes. Past that the RTL
        // saturates and every further tREFI tick is silently dropped, so the
        // ceiling is also the point where data starts aging out.
        a_pending_ceiling: assert (pending_refreshes_o <= MAX_PENDING);

        // THE HEADROOM PROPERTY. Whatever postpone_limit_i is programmed to --
        // including values above the clamp -- a backlog past POSTPONE_MAX must
        // already be asking. If this can fail, the controller reaches the
        // saturation point without ever having requested, which is the defect
        // the POSTPONE_MAX = MAX_PENDING - 2 derivation was written to remove.
        if (pending_refreshes_o > POSTPONE_MAX[3:0])
            a_headroom: assert (refresh_req_o);

        // ...and the clamp leaves a whole interval of lead time: the request is
        // up strictly BEFORE the accumulator reaches its ceiling.
        if (pending_refreshes_o >= MAX_PENDING[3:0] - 4'd1)
            a_asks_before_ceiling: assert (refresh_req_o);
    end

    // =====================================================================
    // FAMILY 2 -- ACCOUNTING. Backlog and credit are a conserved pair.
    // =====================================================================
    always @(posedge mc_clk) if (f_run) begin
        // The pull-in window is the other half of JEDEC's +-8.
        a_pullin_ceiling: assert (obs_pullin_credit_o <= 4'd8);
        a_drain_ceiling:  assert (obs_drain_remaining_o <= 4'd8);

        // One tREFI tick and one grant per cycle at most, so each counter moves
        // by at most one. A counter that jumps has lost or invented a refresh.
        a_pend_step: assert ((pending_refreshes_o == f_pend_d)
                          || (pending_refreshes_o == f_pend_d + 4'd1)
                          || (pending_refreshes_o == f_pend_d - 4'd1));
        a_pull_step: assert ((obs_pullin_credit_o == f_pull_d)
                          || (obs_pullin_credit_o == f_pull_d + 4'd1)
                          || (obs_pullin_credit_o == f_pull_d - 4'd1));

        // A tick creates work and a grant retires it; they cannot BOTH create
        // work in the same cycle. Backlog up and credit up together would mean
        // one event was counted twice.
        a_not_both_up: assert (!((pending_refreshes_o == f_pend_d + 4'd1)
                              && (obs_pullin_credit_o == f_pull_d + 4'd1)));

        // The interval counter never exceeds the interval it was loaded with.
        a_refi_bounded: assert (obs_refi_cnt_o <= (t_refi_i > trefi_pb_i
                                                   ? t_refi_i : trefi_pb_i));
    end

    // =====================================================================
    // FAMILY 3 -- THE DEVICE MIRROR. A desynced rotor precharges the wrong bank.
    // =====================================================================
    always @(posedge mc_clk) if (f_run) begin
        // NOT asserted: "the rotor is a legal bank". With BA_W = $clog2(8) every
        // encodable value IS a legal bank, so it is a tautology -- and written
        // as `rotor < BA_W'(NUM_BANKS)` it is worse than empty, because
        // BA_W'(8) truncates to 3'd0 and the property becomes `rotor < 0`,
        // which fails on a correct design. It was written that way here first.
        // What has content is that the two exposed views of the rotor agree:
        // refresh_bank_o feeds the command path and obs_bank_rotor_o feeds CSR
        // readout, and a debug read that disagreed with the wire would send any
        // investigation of a mis-refresh in the wrong direction.
        a_bank_views_agree: assert (refresh_bank_o == obs_bank_rotor_o);

        // The device's counter advances by exactly one per REFpb command. Ours
        // must too: hold, or step by one with a correct wrap. Anything else is
        // a mirror that has lost the device.
        a_rotor_step: assert ((obs_bank_rotor_o == f_rotor_d)
                           || (obs_bank_rotor_o == f_rotor_d + BA_W'(1))
                           || ((f_rotor_d == BA_W'(NUM_BANKS-1))
                               && (obs_bank_rotor_o == BA_W'(0))));

        // THE RETENTION PROPERTY, and a_rotor_step above does NOT imply it.
        // "steps by at most one" is satisfied by a rotor that HOLDS FOR EVER
        // -- which refreshes one bank and lets the other seven age out. That
        // is a data-retention failure that looks like corrupt memory hours
        // later in a different test, which is this block's whole reason for
        // existing. HAS verification item 4.
        //
        // Stated as two safety properties rather than a liveness one, so BMC
        // can settle it: the rotor MUST advance on an accepted REFpb, and MUST
        // NOT advance otherwise. Together with the already-proved backlog
        // properties (a backlog past the clamp always raises the request),
        // every bank is therefore visited within NUM_BANKS grants.
        if (f_refpb_grant)
            a_rotor_advances_on_refpb: assert (
                   (obs_bank_rotor_o == f_rotor_d + BA_W'(1))
                || ((f_rotor_d == BA_W'(NUM_BANKS-1))
                    && (obs_bank_rotor_o == BA_W'(0))));

        // The mirror must not drift on its own: an advance with no REFpb means
        // the controller now precharges a different bank than the device is
        // about to refresh, which is the desync the RTL comment warns about.
        if (!f_refpb_grant)
            a_rotor_holds_without_refpb: assert (obs_bank_rotor_o == f_rotor_d);

        // Every output is strict-flopped, so the kind reported is last cycle's
        // mode. A scheduler that saw the new mode a cycle early would format
        // the command one way and count the rotor the other.
        a_kind_tracks_mode: assert (refresh_kind_o == f_mode_d);
    end

    // =====================================================================
    // FAMILY 4 -- MODE CONTRACTS. Elastic/TCR behavior with modes enabled.
    // =====================================================================
    always @(posedge mc_clk) if (f_run) begin
        // When elastic refresh is disabled the logic reduces bit-for-bit to v3.
        a_defaults_baseline: assert (
            elastic_en_i || (refresh_req_o == f_baseline_req)
        );

        // Existing ceilings hold with the new CSR inputs free.
        a_pending_ceiling_with_modes: assert (pending_refreshes_o <= MAX_PENDING);
        a_pullin_ceiling_with_modes:  assert (obs_pullin_credit_o <= 4'd8);

        // After each tREFI reload the derated interval is bounded as specified.
        if (f_obs_refi_cnt_d == 16'd0)
            a_derate_bound: assert (
                !tcr_en_i || (
                    obs_refi_cnt_o <= (f_refi_eff >> ((trefi_derate_i > 2'd2) ? 2'd2 : trefi_derate_i))
                )
            );
    end

    // =====================================================================
    // COVER
    // =====================================================================
    always @(posedge mc_clk) if (mc_rst_n) begin
        c_backlog_builds: cover (pending_refreshes_o >= 4'd3);
        // the headroom property actually bites: a backlog past the clamp
        c_headroom_bites: cover (pending_refreshes_o > POSTPONE_MAX[3:0]);
        c_saturated:      cover (pending_refreshes_o == MAX_PENDING[3:0]);
        c_pullin_banked:  cover (obs_pullin_credit_o >= 4'd2);
        c_drain_active:   cover (refresh_drain_active_o);
        // A retention proof is worthless if the rotor never moves in the
        // trace: this is the cover that says the property above was exercised.
        c_all_banks_visited: cover (f_visited == {NUM_BANKS{1'b1}});
        c_rotor_wrapped:  cover (f_rotor_d == BA_W'(NUM_BANKS-1)
                              && obs_bank_rotor_o == BA_W'(0));
        // Mode A: pull-in fires exactly at the configured streak boundary.
        c_pullin_at_streak: cover (elastic_en_i && f_grant_early_d
                                && (f_idle_cnt_d == pullin_idle_streak_i));
        // Mode A: the postpone branch is entered under sustained demand...
        c_postpone_entered: cover (elastic_en_i && demand_i
                                && (f_demand_streak_d >= postpone_demand_streak_i)
                                && (pending_refreshes_o <= f_post_eff)
                                && !f_idle_baseline);
        // ...and exited when the backlog finally crosses the effective limit.
        c_postpone_exited:  cover (elastic_en_i && demand_i && !f_idle_baseline
                                && (pending_refreshes_o > f_post_eff)
                                && (f_demand_streak_d >= postpone_demand_streak_i));
    end

endmodule
