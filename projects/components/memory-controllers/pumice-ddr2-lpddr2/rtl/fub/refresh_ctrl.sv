// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: refresh_ctrl
// Purpose: Track tREFI between mandatory refresh commands. When the
//          interval expires, raise `refresh_req_o` to the scheduler.
//          The scheduler arbitrates and pulses `refresh_grant_i` once
//          it has issued REF on the DFI bus.
//
//          JEDEC allows up to 8 postponed refreshes. We use an 8-deep
//          accumulator: each tREFI tick increments by 1; each grant
//          decrements by 1. `refresh_req_o` stays high while the
//          accumulator is non-zero.
//
//          `enable_i` is driven by init_sequencer: refresh is gated
//          off until init completes.
//
// v2 (D): drain mode + REFpb framework
//   * refresh_burst_i (1..8) now drives a drain counter. When req
//     asserts, the controller loads r_burst_remaining = refresh_burst_i
//     and raises refresh_drain_active_o. Each grant decrements the
//     remaining. While drain_active is high, the scheduler should
//     keep granting REF back-to-back without yielding to W/R.
//   * refpb_mode_i selects REFab (0) vs REFpb (1, LPDDR2). In REFpb
//     mode, refresh_bank_o rotates 0..NUM_BANKS-1 across grants; in
//     REFab mode it stays 0.
//   * refresh_kind_o is the registered REFab/REFpb selector for the
//     scheduler / dfi_cmd_formatter.
//   * obs_* outputs harvest internal state for future CSR readout.
//
// v3 (PUMICE-006 Axis 3): JEDEC +-8 credits (REF_CTRL.postpone/pullin).
//   * postpone_limit_i: while demand_i is high, the request is WITHHELD until
//     the pending backlog exceeds the limit (clamped to 7 so the JEDEC
//     8-postponed ceiling can always force). 0 = strict = the old behaviour
//     (request the moment anything is pending).
//   * pullin_limit_i: while idle (no demand, no backlog) refreshes run AHEAD
//     of tREFI, banking up to the limit (clamped to 8) as credit; each later
//     tREFI tick consumes a credit instead of adding a pending refresh, so a
//     demand burst that follows sees a refresh-free window. 0 = never.
//   * demand_i: scheduler-level "any read/write waiting" — the postpone
//     gate and the pull-in idle detector both key off it.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module refresh_ctrl
    import pumice_pkg::*;
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

    // obs_* (future CSR readout)
    output logic [15:0] obs_refi_cnt_o,
    output logic [3:0]  obs_drain_remaining_o,
    output logic [BA_W-1:0] obs_bank_rotor_o,
    output logic [15:0] obs_grants_total_o,
    output logic [3:0]  obs_pullin_credit_o
);

    //=========================================================================
    // tREFI counter — counts down from t_refi_i. When it reaches 0,
    // accumulate one pending refresh and reload.
    //=========================================================================
    logic [15:0] r_refi_cnt;
    logic [3:0]  r_pending;

    // JEDEC max postponed refreshes = 8.
    localparam logic [3:0] MAX_PENDING = 4'd8;

    logic w_refi_expired;
    assign w_refi_expired = (r_refi_cnt == 16'd0);

    // Effective interval: REFpb refreshes one bank at a time, so it ticks at
    // tREFIpb (~tREFI/8 per JESD209-2; REF_TIMING_PB.trefi_pb overrides,
    // 0 = derive).
    logic [15:0] w_refi_eff;
    assign w_refi_eff = !refpb_mode_i        ? t_refi_i
                      : (trefi_pb_i != 16'd0) ? trefi_pb_i
                                              : (t_refi_i >> 3);

    // Credit limits, clamped: postpone <= 7 so the pending accumulator
    // (saturating at 8) can always exceed it and FORCE the refresh; pull-in
    // <= 8 per the JEDEC +-8 window.
    logic [3:0] w_post_eff, w_pull_eff;
    assign w_post_eff = (postpone_limit_i > 4'd7) ? 4'd7 : postpone_limit_i;
    assign w_pull_eff = (pullin_limit_i  > 4'd8) ? 4'd8 : pullin_limit_i;

    // Pull-in credit: refreshes already performed AHEAD of their tREFI tick.
    logic [3:0] r_pullin;

    logic w_grant_accept;   // grant against the pending backlog
    logic w_grant_early;    // grant with no backlog = a pull-in refresh
    assign w_grant_accept = refresh_grant_i && (r_pending > 4'd0);
    assign w_grant_early  = refresh_grant_i && (r_pending == 4'd0)
                          && (r_pullin < 4'd8);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_refi_cnt <= 16'd0;
            r_pending  <= 4'd0;
            r_pullin   <= 4'd0;
        end else begin
            // tREFI countdown — only ticks when enabled (init done).
            if (!enable_i || refi_reload_i) begin
                r_refi_cnt <= w_refi_eff;
            end else if (w_refi_expired) begin
                r_refi_cnt <= w_refi_eff;
            end else begin
                r_refi_cnt <= r_refi_cnt - 16'd1;
            end

            // Pending backlog + pull-in credit, one next-state evaluation:
            // - a tREFI tick consumes a banked credit if one exists, else
            //   adds a pending refresh (saturate at 8 = retention hazard);
            // - a grant retires a pending refresh if any, else banks a credit.
            begin
                automatic logic [3:0] pend_n = r_pending;
                automatic logic [3:0] pull_n = r_pullin;
                if (enable_i && w_refi_expired) begin
                    if (pull_n > 4'd0)            pull_n = pull_n - 4'd1;
                    else if (pend_n < MAX_PENDING) pend_n = pend_n + 4'd1;
                    // else: saturate (data retention violation looming)
                end
                if (refresh_grant_i) begin
                    if (pend_n > 4'd0)      pend_n = pend_n - 4'd1;
                    else if (pull_n < 4'd8) pull_n = pull_n + 4'd1;
                end
                r_pending <= pend_n;
                r_pullin  <= pull_n;
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

    // Idle confirmation: demand_i is CAM occupancy and blinks off for a few
    // cycles between bursts; treating those micro-gaps as idle would release
    // postponed refreshes (and trigger pull-ins) mid-stream. Only a sustained
    // gap counts as idle.
    localparam logic [4:0] IDLE_CONFIRM = 5'd16;
    logic [4:0] r_idle_cnt;
    logic w_idle;
    assign w_idle = (r_idle_cnt >= IDLE_CONFIRM);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_idle_cnt <= '0;
        end else if (demand_i) begin
            r_idle_cnt <= '0;
        end else if (!w_idle) begin
            r_idle_cnt <= r_idle_cnt + 1'b1;
        end
    end)

    // Request: while demand persists the backlog must EXCEED the postpone
    // limit (0 = strict = request the moment anything is pending); once idle
    // is confirmed any backlog requests immediately, and with pull-in credit
    // available the request runs AHEAD of the backlog entirely.
    logic w_req;
    assign w_req = enable_i
                 && (w_idle ? (r_pending > 4'd0) || (r_pullin < w_pull_eff)
                            : (r_pending > w_post_eff));

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
        end
    end)

endmodule : refresh_ctrl
