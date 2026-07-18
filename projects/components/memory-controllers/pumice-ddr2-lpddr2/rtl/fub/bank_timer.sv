// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bank_timer
// Purpose: One DRAM bank's JEDEC "safe" timing tracker. NO state machine — just
//          a set of preset/decrement countdown timers plus a trivial row-open
//          register. The scheduler (pumice_cmd_arbiter, the single command
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

module bank_timer
    import pumice_pkg::*;
#(
    parameter int ROW_WIDTH = 14,
    parameter int TW        = 8       // timer width
) (
    input  logic                 clk,
    input  logic                 rst_n,

    // JEDEC timing config (controller cycles; command-relative)
    input  logic [TW-1:0]        t_rcd_i,
    input  logic [TW-1:0]        t_rp_i,
    input  logic [TW-1:0]        t_ras_i,
    input  logic [TW-1:0]        t_rc_i,
    input  logic [TW-1:0]        t_wr_i,    // WR cmd -> earliest PRE (incl WL+BL/2)
    input  logic [TW-1:0]        t_rtp_i,   // RD cmd -> earliest PRE

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

    // auto-precharge fires once the read/write recovery (preblk) AND tRAS elapse.
    logic w_ap_fire;
    assign w_ap_fire = r_ap_pending && (r_preblk == '0) && (r_ras == '0);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rcd <= '0; r_ras <= '0; r_rc <= '0; r_rp <= '0; r_preblk <= '0;
            r_row_valid <= 1'b0; r_open_row <= '0; r_ap_pending <= 1'b0;
        end else begin
            // tRCD / tRAS / tRC: reload on ACT, else count down (saturate at 0)
            if (set_act_i)         r_rcd <= t_rcd_i;
            else if (r_rcd != '0)  r_rcd <= r_rcd - 1'b1;

            if (set_act_i)         r_ras <= t_ras_i;
            else if (r_ras != '0)  r_ras <= r_ras - 1'b1;

            if (set_act_i)         r_rc  <= t_rc_i;
            else if (r_rc  != '0)  r_rc  <= r_rc - 1'b1;

            // tRP: reload on explicit PRE or auto-PRE fire, else count down
            if (set_pre_i || w_ap_fire) r_rp <= t_rp_i;
            else if (r_rp != '0)        r_rp <= r_rp - 1'b1;

            // preblk: reload on RD (tRTP) / WR (tWR), else count down
            if (set_rd_i)              r_preblk <= t_rtp_i;
            else if (set_wr_i)         r_preblk <= t_wr_i;
            else if (r_preblk != '0)   r_preblk <= r_preblk - 1'b1;

            // row-open + auto-precharge bit (ACT > explicit PRE > auto-PRE)
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
    assign safe_act_o = !r_row_valid && (r_rp == '0) && (r_rc == '0);
    // RD/WR: row open, tRCD met, not auto-precharging.
    assign safe_rd_o  = r_row_valid && (r_rcd == '0) && !r_ap_pending;
    assign safe_wr_o  = safe_rd_o;
    // PRE: row open, tRAS + tRTP/tWR met, not auto-precharging.
    assign safe_pre_o = r_row_valid && (r_ras == '0) && (r_preblk == '0) && !r_ap_pending;

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

endmodule : bank_timer
