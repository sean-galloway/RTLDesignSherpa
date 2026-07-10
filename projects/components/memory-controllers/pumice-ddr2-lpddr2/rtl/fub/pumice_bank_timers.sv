// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_bank_timers
// Purpose: Per-(rank,bank) JEDEC "safe" timing tracker for the pumice
//          command scheduler. OPEN-PAGE capable: after a non-auto-precharge
//          RD/WR the bank STAYS ACTIVE so column commands can stream to an
//          open row at tCCD rate (tCCD/tWTR/tRTW turnaround are enforced
//          globally in pumice_global_timers, ANDed by the arbiter). tRTP/tWR
//          gate ONLY the precharge, not the next column command.
//
// Per-bank timers (loaded on the event, count down, saturate at 0):
//   act_cnt      tRCD  — ACT -> RD/WR         (gates rdwr_ready)
//   ras_cnt      tRAS  — ACT -> PRE (min)     (gates pre_ready)
//   rc_cnt       tRC   — ACT -> ACT same bank (gates act_ready)
//   pre_cnt      tRP   — PRE -> ACT           (gates act_ready)
//   preblk_cnt   tRTP  (RD) / tWR (WR)        (gates pre_ready ONLY)
//                NOTE: t_wr_i must be command->earliest-PRE (i.e. include
//                WL + BL/2); t_rtp_i likewise command-relative.
//
// State: BANK_IDLE -> BANK_ACTIVATING -(tRCD)-> BANK_ACTIVE -(pre)->
//        BANK_PRECHARGING -(tRP)-> BANK_IDLE. Auto-precharge (RDA/WRA) sets
//        r_ap_pending; when preblk & tRAS clear, the bank auto-transitions
//        ACTIVE -> PRECHARGING internally (no scheduler PRE).
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md (scheduler layer)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_bank_timers
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    input  logic [7:0]                 t_rcd_i,
    input  logic [7:0]                 t_rp_i,
    input  logic [7:0]                 t_ras_i,
    input  logic [7:0]                 t_rc_i,
    input  logic [7:0]                 t_wr_i,    // WR cmd -> earliest PRE (incl WL+BL/2)
    input  logic [7:0]                 t_rtp_i,   // RD cmd -> earliest PRE

    // ----- bank-event strobes from the arbiter -----
    input  logic                       evt_act_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,
    input  logic                       evt_pre_i,
    input  logic                       evt_ap_i,   // auto-precharge (with RD/WR)
    input  logic [RKW-1:0]             evt_rank_i,
    input  logic [BKW-1:0]             evt_bank_i,
    input  logic [ROW_WIDTH-1:0]       evt_row_i,

    // ----- per-bank readiness to the arbiter -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_o,
    output bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]          bank_state_o,

    // ----- observability -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_act_cnt_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_preblk_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_ras_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_ap_pending_o
);

    bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]            r_state;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]             r_act_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]             r_preblk_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]             r_ras_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]             r_rc_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]             r_pre_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]   r_open_row;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  r_ap_pending;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_state      <= '0;   // BANK_IDLE
            r_act_cnt    <= '0;
            r_preblk_cnt <= '0;
            r_ras_cnt    <= '0;
            r_rc_cnt     <= '0;
            r_pre_cnt    <= '0;
            r_open_row   <= '0;
            r_ap_pending <= '0;
        end else begin
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                    // 1. countdown (saturate at 0)
                    if (r_act_cnt   [k][b] > 8'd0) r_act_cnt   [k][b] <= r_act_cnt   [k][b] - 8'd1;
                    if (r_preblk_cnt[k][b] > 8'd0) r_preblk_cnt[k][b] <= r_preblk_cnt[k][b] - 8'd1;
                    if (r_ras_cnt   [k][b] > 8'd0) r_ras_cnt   [k][b] <= r_ras_cnt   [k][b] - 8'd1;
                    if (r_rc_cnt    [k][b] > 8'd0) r_rc_cnt    [k][b] <= r_rc_cnt    [k][b] - 8'd1;
                    if (r_pre_cnt   [k][b] > 8'd0) r_pre_cnt   [k][b] <= r_pre_cnt   [k][b] - 8'd1;

                    // 2. state transitions on expiry
                    if (r_state[k][b] == BANK_ACTIVATING && r_act_cnt[k][b] == 8'd1)
                        r_state[k][b] <= BANK_ACTIVE;
                    // auto-precharge: internal PRE once preblk AND tRAS are met
                    if (r_state[k][b] == BANK_ACTIVE && r_ap_pending[k][b]
                        && r_preblk_cnt[k][b] == 8'd0 && r_ras_cnt[k][b] == 8'd0) begin
                        r_state     [k][b] <= BANK_PRECHARGING;
                        r_pre_cnt   [k][b] <= t_rp_i;
                        r_ap_pending[k][b] <= 1'b0;
                    end
                    if (r_state[k][b] == BANK_PRECHARGING && r_pre_cnt[k][b] == 8'd1)
                        r_state[k][b] <= BANK_IDLE;
                end
            end

            // 3. event strobes override for the targeted bank
            if (evt_act_i) begin
                r_state     [evt_rank_i][evt_bank_i] <= BANK_ACTIVATING;
                r_act_cnt   [evt_rank_i][evt_bank_i] <= t_rcd_i;
                r_rc_cnt    [evt_rank_i][evt_bank_i] <= t_rc_i;
                r_ras_cnt   [evt_rank_i][evt_bank_i] <= t_ras_i;
                r_open_row  [evt_rank_i][evt_bank_i] <= evt_row_i;
                r_ap_pending[evt_rank_i][evt_bank_i] <= 1'b0;
            end
            // RD/WR keep the bank ACTIVE (open-page); only load the PRE-block
            // timer + the auto-precharge flag.
            if (evt_rd_i) begin
                r_preblk_cnt[evt_rank_i][evt_bank_i] <= t_rtp_i;
                r_ap_pending[evt_rank_i][evt_bank_i] <= evt_ap_i;
            end
            if (evt_wr_i) begin
                r_preblk_cnt[evt_rank_i][evt_bank_i] <= t_wr_i;
                r_ap_pending[evt_rank_i][evt_bank_i] <= evt_ap_i;
            end
            if (evt_pre_i) begin
                r_state     [evt_rank_i][evt_bank_i] <= BANK_PRECHARGING;
                r_pre_cnt   [evt_rank_i][evt_bank_i] <= t_rp_i;
                r_ap_pending[evt_rank_i][evt_bank_i] <= 1'b0;
            end
        end
    end)

    //=========================================================================
    // Combinational readiness (registered out below).
    //=========================================================================
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_act_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_pre_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_row_active;

    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                w_act_ready [k][b] = (r_state[k][b] == BANK_IDLE)
                                  && (r_pre_cnt[k][b] == 8'd0)
                                  && (r_rc_cnt[k][b]  == 8'd0);
                // OPEN-PAGE: column commands gated only by tRCD + ACTIVE (+ global
                // tCCD in the arbiter); NOT by tRTP/tWR. Blocked while auto-PRE pends.
                w_rdwr_ready[k][b] = (r_state[k][b] == BANK_ACTIVE)
                                  && (r_act_cnt[k][b] == 8'd0)
                                  && !r_ap_pending[k][b];
                // explicit PRE allowed once tRAS + tRTP/tWR met (non-AP rows)
                w_pre_ready [k][b] = (r_state[k][b] == BANK_ACTIVE)
                                  && (r_ras_cnt[k][b]    == 8'd0)
                                  && (r_preblk_cnt[k][b] == 8'd0)
                                  && !r_ap_pending[k][b];
                w_row_active[k][b] = (r_state[k][b] == BANK_ACTIVE);
            end
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            bank_act_ready_o  <= '1;   // all idle -> ready to ACT
            bank_rdwr_ready_o <= '0;
            bank_pre_ready_o  <= '0;
            bank_row_active_o <= '0;
            bank_open_row_o   <= '0;
            bank_state_o      <= '0;
        end else begin
            bank_act_ready_o  <= w_act_ready;
            bank_rdwr_ready_o <= w_rdwr_ready;
            bank_pre_ready_o  <= w_pre_ready;
            bank_row_active_o <= w_row_active;
            bank_open_row_o   <= r_open_row;
            bank_state_o      <= r_state;
        end
    end)

    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                obs_act_cnt_nz_o[k][b] = (r_act_cnt   [k][b] != 8'd0);
                obs_preblk_nz_o [k][b] = (r_preblk_cnt[k][b] != 8'd0);
                obs_ras_nz_o    [k][b] = (r_ras_cnt   [k][b] != 8'd0);
                obs_ap_pending_o[k][b] = r_ap_pending [k][b];
            end
        end
    end

endmodule : pumice_bank_timers
