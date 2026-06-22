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

`timescale 1ns / 1ps

`include "reset_defs.svh"

module refresh_ctrl
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_BANKS = 8,
    parameter int BA_W      = $clog2(NUM_BANKS)
)(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  logic [15:0] t_refi_i,         // refresh interval (MC cycles)
    input  logic [3:0]  refresh_burst_i,  // 1..8 drain count per req cycle
    input  logic        refpb_mode_i,     // 0 = REFab, 1 = REFpb (LPDDR2)
    input  logic        enable_i,

    output logic        refresh_req_o,
    input  logic        refresh_grant_i,
    output logic [3:0]  pending_refreshes_o,

    // D: drain + REFpb
    output logic        refresh_drain_active_o,
    output logic        refresh_kind_o,        // 0=REFab, 1=REFpb
    output logic [BA_W-1:0] refresh_bank_o,    // valid in REFpb mode

    // obs_* (future CSR readout)
    output logic [15:0] obs_refi_cnt_o,
    output logic [3:0]  obs_drain_remaining_o,
    output logic [BA_W-1:0] obs_bank_rotor_o,
    output logic [15:0] obs_grants_total_o
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

    logic w_grant_accept;
    assign w_grant_accept = refresh_grant_i && (r_pending > 4'd0);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_refi_cnt <= 16'd0;
            r_pending  <= 4'd0;
        end else begin
            // tREFI countdown — only ticks when enabled (init done).
            if (!enable_i) begin
                r_refi_cnt <= t_refi_i;
            end else if (w_refi_expired) begin
                r_refi_cnt <= t_refi_i;
            end else begin
                r_refi_cnt <= r_refi_cnt - 16'd1;
            end

            // Pending refresh accumulator
            // - tREFI expiry adds 1 (saturate at MAX_PENDING)
            // - grant subtracts 1
            if (enable_i && w_refi_expired && !w_grant_accept) begin
                if (r_pending < MAX_PENDING) begin
                    r_pending <= r_pending + 4'd1;
                end
                // else: saturate (DRAM data retention violation looming)
            end else if (!w_refi_expired && w_grant_accept) begin
                r_pending <= r_pending - 4'd1;
            end else if (enable_i && w_refi_expired && w_grant_accept) begin
                // simultaneous tick + grant — net zero change
                r_pending <= r_pending;
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

    logic w_drain_active;
    assign w_drain_active = (r_burst_remaining > 4'd0) && (r_pending > 4'd0);

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
        end else if (w_grant_accept) begin
            r_grants_total <= r_grants_total + 16'd1;
            if (refpb_mode_i) begin
                if (r_bank_rotor == BA_W'(NUM_BANKS-1)) begin
                    r_bank_rotor <= '0;
                end else begin
                    r_bank_rotor <= r_bank_rotor + BA_W'(1);
                end
            end else begin
                r_bank_rotor <= '0;
            end
        end
    end)

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
        end else begin
            refresh_req_o           <= (r_pending > 4'd0);
            pending_refreshes_o     <= r_pending;
            refresh_drain_active_o  <= w_drain_active;
            refresh_kind_o          <= refpb_mode_i;
            refresh_bank_o          <= r_bank_rotor;
            obs_refi_cnt_o          <= r_refi_cnt;
            obs_drain_remaining_o   <= r_burst_remaining;
            obs_bank_rotor_o        <= r_bank_rotor;
            obs_grants_total_o      <= r_grants_total;
        end
    end)

endmodule : refresh_ctrl
