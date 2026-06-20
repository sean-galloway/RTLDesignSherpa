// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: refresh_ctrl_fub
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
// v1 (TODO):
//   * `refresh_burst_i` (1..8) is ignored — every grant counts as 1.
//     Real silicon may want to drain multiple postponed refreshes
//     in a row before yielding.
//   * No tracking of REF-vs-REFpb (LPDDR2 per-bank refresh).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module refresh_ctrl_fub
    import ddr2_lpddr2_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  logic [15:0] t_refi_i,         // refresh interval (MC cycles)
    input  logic [3:0]  refresh_burst_i,  // 1..8 (per-bank or all-bank); v1 ignored
    input  logic        enable_i,

    output logic        refresh_req_o,
    input  logic        refresh_grant_i,
    output logic [3:0]  pending_refreshes_o
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

    assign refresh_req_o       = (r_pending > 4'd0);
    assign pending_refreshes_o = r_pending;

    wire unused_v1 = |{ refresh_burst_i };

endmodule : refresh_ctrl_fub
