// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_refresh_ctrl
// Purpose: refresh_ctrl
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_refresh_ctrl per andesite HAS ch02 (MODIFIED -- the
// andesite FGR delta is marked ANDESITE FGR DELTA: factor-divided tREFI
// reload, per-density tRFC select; reload-only scaling carried from the
// Mode B posture).
//
// Author: sean galloway
// Created: 2026-10-04 (carried)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_refresh_ctrl
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int NUM_BANKS = 8,
    parameter int BA_W      = $clog2(NUM_BANKS)
)(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  logic [15:0] t_refi_i,         // refresh interval (MC cycles)
    input  logic [15:0] trefi_pb_i,       // REFpb interval; 0 = derive tREFI/8
    input  logic [3:0]  refresh_burst_i,  // 1..8 drain count per req cycle
    input  logic        refpb_mode_i,     // 0 = REFab, 1 = REFpb (LPDDR2)
    input  logic        enable_i,
    // DV/bring-up knob: pulse to reload the tREFI countdown IMMEDIATELY with
    // the current t_refi_i. The counter otherwise only reloads on EXPIRY, so
    // writing a new t_refi_i does not take effect until the already-armed
    // interval finishes -- which means a test that parks tREFI still eats one
    // stale refresh, and a test that shortens it waits out the old long one.
    // That cost three separate debugging rounds (refresh_credit, the write
    // ceiling, and the drain_burst gate check). Tie to 0 in production: it
    // has no effect unless pulsed, so the default build is bit-identical.
    input  logic        refi_reload_i,

    // REF_CTRL credits (0 = strict / off)
    input  logic [3:0]  postpone_limit_i, // defer under demand, max 7 effective
    input  logic [3:0]  pullin_limit_i,   // run ahead on idle, max 8
    input  logic        demand_i,         // scheduler has read/write work

    // Mode A: demand-aware elastic refresh
    input  logic        elastic_en_i,              // 0 = v3 behaviour
    input  logic [7:0]  pullin_idle_streak_i,      // idle cycles before pull-in
    input  logic [6:0]  postpone_demand_streak_i,  // demand cycles before postpone

    // Mode B: temperature-compensated refresh (tREFI derate)
    input  logic        tcr_en_i,                  // 0 = 1x interval (today)
    input  logic [1:0]  trefi_derate_i,            // 0=1x, 1=2x, 2=4x; 3 clamps to 2

    // ANDESITE FGR DELTA: DDR4 fine-granularity refresh (JESD79-4 MR3
    // image). 0=1x, 1=2x, 2=4x; an illegal encoding clamps to the 1x row
    // per the kmap FGR select table -- deliberately NOT the Mode B 3->2
    // clamp above. Factor 1x is bit-identical to the inherited base.
    input  logic [1:0]  fgr_factor_i,
    // tRFC per density: the recovery owner (arbiter) consumes
    // refresh_trfc_o; the per-refresh busy window is tRFC(fgr).
    input  logic [15:0] t_rfc_1x_i,
    input  logic [15:0] t_rfc_2x_i,
    input  logic [15:0] t_rfc_4x_i,

    output logic        refresh_req_o,
    input  logic        refresh_grant_i,
    // 1 = the granted command on the wire THIS cycle is OP_REFPB. The rotor
    // mirrors the DEVICE'S internal counter, which advances per REFpb
    // COMMAND — keying off refpb_mode_i instead desynchronizes the mirror
    // at every mode boundary (a grant decided as REFab but counted as pb,
    // or vice versa), after which the controller precharges the WRONG bank
    // ahead of each device refresh.
    input  logic        grant_was_pb_i,
    output logic [3:0]  pending_refreshes_o,

    // D: drain + REFpb
    output logic        refresh_drain_active_o,
    output logic        refresh_kind_o,        // 0=REFab, 1=REFpb
    output logic [BA_W-1:0] refresh_bank_o,    // valid in REFpb mode

    // ANDESITE FGR DELTA: tRFC_active = tRFC(fgr), selected from the
    // per-density CSRs. Wired to the arbiter's recovery input by the
    // scheduler macro (the macro rewiring lands with the integration task).
    output logic [15:0] refresh_trfc_o,

    // obs_* (future CSR readout)
    output logic [15:0] obs_refi_cnt_o,
    output logic [3:0]  obs_drain_remaining_o,
    output logic [BA_W-1:0] obs_bank_rotor_o,
    output logic [15:0] obs_grants_total_o,
    output logic [3:0]  obs_pullin_credit_o,
    output logic [15:0] obs_postpone_events_o,
    output logic [15:0] obs_pullin_events_o
);

    //=========================================================================
    // tREFI counter — counts down from t_refi_i. When it reaches 0,
    // accumulate one pending refresh and reload.
    //=========================================================================
    logic [15:0] r_refi_cnt;
    logic [3:0]  r_pending;
    logic [6:0]  r_demand_streak;    // Mode A: consecutive cycles of demand_i
    logic [15:0] r_postpone_events;  // Mode A: telemetry histogram bin
    logic [15:0] r_pullin_events;    // Mode A: telemetry histogram bin

    // JEDEC max postponed refreshes = 8.
    localparam logic [3:0] MAX_PENDING = 4'd8;

    logic w_refi_expired;
    assign w_refi_expired = (r_refi_cnt == 16'd0);

    // Effective interval: REFpb refreshes one bank at a time, so it ticks at
    // tREFIpb (~tREFI/8 per JESD209-2; REF_TIMING_PB.trefi_pb overrides,
    // 0 = derive).  Mode B then derates the reload value 1x/2x/4x.
    logic [15:0] w_refi_eff;
    assign w_refi_eff = !refpb_mode_i        ? t_refi_i
                      : (trefi_pb_i != 16'd0) ? trefi_pb_i
                                              : (t_refi_i >> 3);

    // Mode B: temperature-compensated refresh shift.  Disabled => shift 0
    // (bit-identical to v4); illegal value 3 clamps to 2.  Applied only to
    // the reload value -- the running counter is not rescaled mid-interval.
    logic [1:0]  w_derate_shift;
    logic [15:0] w_refi_eff_derated;
    assign w_derate_shift = (!tcr_en_i) ? 2'd0
                          : (trefi_derate_i > 2'd2) ? 2'd2
                                                    : trefi_derate_i;

    // ANDESITE FGR DELTA: factor shift, composed BEFORE the Mode B derate
    // (tREFI_effective = tREFI / fgr_factor per the MAS 06 fence; both
    // stages divide by a power of two, so the order is immaterial, but the
    // fence's order is kept).  Reload-only: like the derate, this touches
    // the reload value, never the running counter -- a factor change
    // mid-interval takes effect on the next reload.  The credit window
    // ceiling (+-8) is unchanged; measured in time it scales with the
    // interval because expiries arrive fgr_factor times as often.
    logic [1:0]  w_fgr_shift;
    logic [15:0] w_refi_eff_fgr;
    assign w_fgr_shift = (fgr_factor_i > 2'd2) ? 2'd0 : fgr_factor_i;
    assign w_refi_eff_fgr = w_refi_eff >> w_fgr_shift;

    assign w_refi_eff_derated = w_refi_eff_fgr >> w_derate_shift;

    // ANDESITE FGR DELTA: tRFC_active = tRFC(fgr) -- a pure mux; recovery is
    // per-command in the consumer, so the select may follow the factor
    // combinationally.
    assign refresh_trfc_o = (w_fgr_shift == 2'd2) ? t_rfc_4x_i
                           : (w_fgr_shift == 2'd1) ? t_rfc_2x_i
                                                   : t_rfc_1x_i;

    // Credit limits, clamped: postpone <= 7 so the pending accumulator
    // (saturating at 8) can always exceed it and FORCE the refresh; pull-in
    // <= 8 per the JEDEC +-8 window.
    // POSTPONE_MAX is derived from MAX_PENDING, not written as a literal, so
    // the two cannot drift apart. It must leave HEADROOM, not merely allow the
    // accumulator to exceed it:
    //
    //   The busy-side request is `r_pending > w_post_eff`. With the old clamp of
    //   7 that first asserted at pending == 8 == MAX_PENDING -- the exact value
    //   at which `else if (pend_n < MAX_PENDING)` stops incrementing and every
    //   further tREFI tick is SILENTLY DROPPED. The threshold to START asking
    //   for a refresh and the threshold to BEGIN LOSING them were the same
    //   number, so any latency between the request and the grant (finishing a
    //   write burst, precharging banks, tRFC) cost real refreshes -- a data
    //   retention hazard, not just a scheduling delay.
    //
    //   Only `refresh_credit` was exposed: it is the sole config that programs
    //   postpone (8, clamped to 7). Every other config leaves postpone = 0
    //   (strict), where the request asserts at pending > 0 and the headroom is
    //   the full JEDEC window.
    //
    //   MAX_PENDING - 2 makes the request assert at pending == MAX_PENDING - 1,
    //   i.e. one whole tREFI (7.8 us at this tREFI) of lead time to drain a
    //   burst and issue the REF before the JEDEC 8-postponed ceiling. JEDEC
    //   permits 8 postponed refreshes, so saturating AT 8 is correct; asking
    //   only once you are already there is not.
    localparam logic [3:0] POSTPONE_MAX = MAX_PENDING - 4'd2;
    logic [3:0] w_post_eff, w_pull_eff;
    assign w_post_eff = (postpone_limit_i > POSTPONE_MAX) ? POSTPONE_MAX
                                                          : postpone_limit_i;
    assign w_pull_eff = (pullin_limit_i  > 4'd8) ? 4'd8 : pullin_limit_i;

    // Pull-in credit: refreshes already performed AHEAD of their tREFI tick.
    logic [3:0] r_pullin;

    logic w_grant_accept;   // grant against the pending backlog
    logic w_grant_early;    // grant with no backlog = a pull-in refresh
    assign w_grant_accept = refresh_grant_i && (r_pending > 4'd0);
    assign w_grant_early  = refresh_grant_i && (r_pending == 4'd0)
                          && (r_pullin < 4'd8);

    //=========================================================================
    // Idle confirmation: demand_i is CAM occupancy and blinks off for a few
    // cycles between bursts; treating those micro-gaps as idle would release
    // postponed refreshes (and trigger pull-ins) mid-stream. Only a sustained
    // gap counts as idle. Mode A makes the threshold sweepable; disabled, it
    // falls back to the inherited 16-cycle confirmation.
    //=========================================================================
    logic [7:0] r_idle_cnt;
    logic       w_idle;
    assign w_idle = (r_idle_cnt >= (elastic_en_i ? pullin_idle_streak_i : 8'd16));

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_idle_cnt <= '0;
        end else if (demand_i) begin
            r_idle_cnt <= '0;
        end else if (!w_idle) begin
            r_idle_cnt <= r_idle_cnt + 1'b1;
        end
    end)

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_refi_cnt       <= 16'd0;
            r_pending        <= 4'd0;
            r_pullin         <= 4'd0;
            r_demand_streak  <= 7'd0;
            r_postpone_events <= 16'd0;
            r_pullin_events   <= 16'd0;
        end else begin
            // tREFI countdown — only ticks when enabled (init done).
            if (!enable_i || refi_reload_i) begin
                r_refi_cnt <= w_refi_eff_derated;
            end else if (w_refi_expired) begin
                r_refi_cnt <= w_refi_eff_derated;
            end else begin
                r_refi_cnt <= r_refi_cnt - 16'd1;
            end

            // Mode A: sustained-demand streak. Reset on any idle cycle; saturate
            // at 127 so the comparison stays stable against the 7-bit CSR.
            if (!demand_i) begin
                r_demand_streak <= 7'd0;
            end else if (r_demand_streak != 7'd127) begin
                r_demand_streak <= r_demand_streak + 7'd1;
            end

            // Pending backlog + pull-in credit, one next-state evaluation:
            // - a tREFI tick consumes a banked credit if one exists, else
            //   adds a pending refresh (saturate at 8 = retention hazard);
            // - a grant retires a pending refresh if any, else banks a credit.
            begin
                automatic logic [3:0] pend_n = r_pending;
                automatic logic [3:0] pull_n = r_pullin;
                automatic logic       pend_tick = 1'b0;
                if (enable_i && w_refi_expired) begin
                    if (pull_n > 4'd0) begin
                        pull_n = pull_n - 4'd1;
                    end else if (pend_n < MAX_PENDING) begin
                        pend_n = pend_n + 4'd1;
                        pend_tick = 1'b1;
                    end
                    // else: saturate (data retention violation looming)
                end
                if (refresh_grant_i) begin
                    if (pend_n > 4'd0)      pend_n = pend_n - 4'd1;
                    else if (pull_n < 4'd8) pull_n = pull_n + 4'd1;
                end
                r_pending <= pend_n;
                r_pullin  <= pull_n;

                // Mode A telemetry: count refreshes withheld by the sustained-
                // demand postpone branch. A tick that adds pending while we are
                // not idle, the demand streak has crossed the threshold, and the
                // pre-tick backlog still does not exceed the effective postpone
                // limit is being actively postponed.  The pre-tick comparison
                // captures the final threshold-crossing expiry (the tick that
                // pushes pending from the limit to limit+1).
                if (pend_tick && elastic_en_i && !w_idle
                    && (r_demand_streak >= postpone_demand_streak_i)
                    && (r_pending <= w_post_eff)
                    && (r_postpone_events != 16'hFFFF)) begin
                    r_postpone_events <= r_postpone_events + 16'd1;
                end

                // Mode A telemetry: count pull-in grants (saturate, do not wrap).
                if (w_grant_early && (r_pullin_events != 16'hFFFF)) begin
                    r_pullin_events <= r_pullin_events + 16'd1;
                end
            end
        end
    end)

    //=========================================================================
    // D: drain quota. Whenever the quota counter reaches 0 and there's
    // pending work, load min(refresh_burst_i, r_pending). Each grant
    // decrements. Drain is "active" while remaining > 0 AND pending > 0
    // (scheduler should keep granting REF back-to-back during this window).
    //=========================================================================
    logic [3:0] r_burst_remaining;

    // Clamp the load value to actual pending so we don't overcount.
    logic [3:0] w_drain_load;
    assign w_drain_load = (refresh_burst_i > r_pending) ? r_pending
                                                        : refresh_burst_i;

    // Gated on the registered request: a postponed backlog (req withheld)
    // must not open the drain window, or the arbiter's drain preemption
    // would defeat the postpone credit entirely.
    logic w_drain_active;
    assign w_drain_active = (r_burst_remaining > 4'd0) && (r_pending > 4'd0)
                          && refresh_req_o;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_burst_remaining <= 4'd0;
        end else begin
            if (w_grant_accept && r_burst_remaining > 4'd0) begin
                r_burst_remaining <= r_burst_remaining - 4'd1;
            end else if (r_burst_remaining == 4'd0 && r_pending > 4'd0) begin
                // (Re)load quota once previous burst has been fully drained.
                r_burst_remaining <= (w_drain_load == 4'd0)
                                     ? 4'd1 : w_drain_load;
            end
        end
    end)

    //=========================================================================
    // REFpb bank rotor — increments on each grant when REFpb mode is
    // selected. Wraps 0..NUM_BANKS-1. In REFab mode, stays at 0.
    //=========================================================================
    logic [BA_W-1:0] r_bank_rotor;
    logic [15:0]     r_grants_total;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_bank_rotor   <= '0;
            r_grants_total <= 16'd0;
        end else if (w_grant_accept || w_grant_early) begin
            r_grants_total <= r_grants_total + 16'd1;
            // The rotor mirrors the DEVICE'S internal REFpb bank counter
            // (JESD209-2 6.6 — the command carries no bank address). It
            // advances exactly when a REFpb COMMAND is granted onto the
            // wire (grant_was_pb_i) and HOLDS through REFab mode: the
            // device's counter persists across mode changes, and clearing
            // ours would desynchronize the mirror.
            if (grant_was_pb_i) begin
                if (r_bank_rotor == BA_W'(NUM_BANKS-1)) begin
                    r_bank_rotor <= '0;
                end else begin
                    r_bank_rotor <= r_bank_rotor + BA_W'(1);
                end
            end
        end
    end)

    // Request: while demand persists the backlog must EXCEED the postpone
    // limit (0 = strict = request the moment anything is pending); once idle
    // is confirmed any backlog requests immediately, and with pull-in credit
    // available the request runs AHEAD of the backlog entirely. Mode A adds
    // a demand-streak gate: sporadic demand keeps strict behaviour; sustained
    // demand engages the postpone limit. When elastic_en_i is low the equation
    // reduces bit-for-bit to v3.
    logic w_req;
    assign w_req = enable_i
                 && (w_idle ? ((r_pending > 4'd0) || (r_pullin < w_pull_eff))
                            : (elastic_en_i && (r_demand_streak < postpone_demand_streak_i)
                                 ? (r_pending > 4'd0)          // sporadic demand: strict
                                 : (r_pending > w_post_eff)));  // sustained demand: postpone

    // Strict-flop outputs.
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            refresh_req_o           <= 1'b0;
            pending_refreshes_o     <= 4'd0;
            refresh_drain_active_o  <= 1'b0;
            refresh_kind_o          <= 1'b0;
            refresh_bank_o          <= '0;
            obs_refi_cnt_o          <= 16'd0;
            obs_drain_remaining_o   <= 4'd0;
            obs_bank_rotor_o        <= '0;
            obs_grants_total_o      <= 16'd0;
            obs_pullin_credit_o     <= 4'd0;
            obs_postpone_events_o   <= 16'd0;
            obs_pullin_events_o     <= 16'd0;
        end else begin
            refresh_req_o           <= w_req;
            pending_refreshes_o     <= r_pending;
            refresh_drain_active_o  <= w_drain_active;
            refresh_kind_o          <= refpb_mode_i;
            refresh_bank_o          <= r_bank_rotor;
            obs_refi_cnt_o          <= r_refi_cnt;
            obs_drain_remaining_o   <= r_burst_remaining;
            obs_bank_rotor_o        <= r_bank_rotor;
            obs_grants_total_o      <= r_grants_total;
            obs_pullin_credit_o     <= r_pullin;
            obs_postpone_events_o   <= r_postpone_events;
            obs_pullin_events_o     <= r_pullin_events;
        end
    end)

endmodule : andesite_refresh_ctrl
