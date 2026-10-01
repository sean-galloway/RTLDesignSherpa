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
    wire [3:0]  obs_drain_remaining_o, obs_pullin_credit_o;

    scoria_refresh_ctrl #(.NUM_BANKS(NUM_BANKS)) dut (
        .mc_clk(mc_clk), .mc_rst_n(mc_rst_n),
        .t_refi_i(t_refi_i), .trefi_pb_i(trefi_pb_i),
        .refresh_burst_i(refresh_burst_i), .refpb_mode_i(refpb_mode_i),
        .enable_i(enable_i), .refi_reload_i(refi_reload_i),
        .postpone_limit_i(postpone_limit_i), .pullin_limit_i(pullin_limit_i),
        .demand_i(demand_i),
        .refresh_req_o(refresh_req_o), .refresh_grant_i(refresh_grant_i),
        .grant_was_pb_i(grant_was_pb_i),
        .pending_refreshes_o(pending_refreshes_o),
        .refresh_drain_active_o(refresh_drain_active_o),
        .refresh_kind_o(refresh_kind_o), .refresh_bank_o(refresh_bank_o),
        .obs_refi_cnt_o(obs_refi_cnt_o),
        .obs_drain_remaining_o(obs_drain_remaining_o),
        .obs_bank_rotor_o(obs_bank_rotor_o),
        .obs_grants_total_o(obs_grants_total_o),
        .obs_pullin_credit_o(obs_pullin_credit_o)
    );

    // ---- formal infrastructure ---------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge mc_clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!mc_rst_n);
    always @(posedge mc_clk) if (f_past_valid >= 2) assume (mc_rst_n);

    reg [3:0]      f_pend_d, f_pull_d, f_drain_d;
    reg [BA_W-1:0] f_rotor_d;
    reg            f_mode_d;
    always @(posedge mc_clk) begin
        f_pend_d  <= pending_refreshes_o;
        f_pull_d  <= obs_pullin_credit_o;
        f_drain_d <= obs_drain_remaining_o;
        f_rotor_d <= obs_bank_rotor_o;
        f_mode_d  <= refpb_mode_i;
    end
    wire f_run = mc_rst_n && (f_past_valid > 3);

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

        // Every output is strict-flopped, so the kind reported is last cycle's
        // mode. A scheduler that saw the new mode a cycle early would format
        // the command one way and count the rotor the other.
        a_kind_tracks_mode: assert (refresh_kind_o == f_mode_d);
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
        c_rotor_wrapped:  cover (f_rotor_d == BA_W'(NUM_BANKS-1)
                              && obs_bank_rotor_o == BA_W'(0));
    end

endmodule
