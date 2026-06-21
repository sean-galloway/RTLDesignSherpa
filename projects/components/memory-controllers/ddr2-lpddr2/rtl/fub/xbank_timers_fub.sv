// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: xbank_timers_fub
// Purpose: Per-(rank,bank) JEDEC timing tracker.
//
//          For each bank, maintain three independent countdown timers
//          plus a `bank_state`/`open_row` register:
//            * act_busy_cnt   — counts since ACT; tRCD until 0
//            * rdwr_busy_cnt  — counts since RD/WR; tWR or tRTP until 0
//            * pre_busy_cnt   — counts since PRE; tRP until 0
//
//          A bank is "ready for X" when the relevant counter is 0
//          AND the bank state allows it.
//
//          On each event strobe (ACT/RD/WR/PRE), reload the relevant
//          counter and transition state. The scheduler queries the
//          combinational ready vectors to decide.
//
// State transitions (closed-page friendly v1):
//   IDLE       --act-->  ACTIVATING (act_busy=tRCD)
//   ACTIVATING --tRCD-->  ACTIVE
//   ACTIVE     --rd-->    RD_BUSY (rdwr_busy=tRTP)
//   ACTIVE     --wr-->    WR_BUSY (rdwr_busy=tWR)
//   RD_BUSY    --tRTP-->  ACTIVE  (closed-page scheduler issues PRE next)
//   WR_BUSY    --tWR-->   ACTIVE
//   ACTIVE     --pre-->   PRECHARGING (pre_busy=tRP)
//   PRECHARGING --tRP-->  IDLE
//
// v1 (TODO):
//   * tRC (ACT-to-ACT same bank) tracked via act_busy_cnt indirectly
//     (act_busy >= max(tRCD, tRC-tRP)) — approximation; needs a
//     separate counter for strict tRC enforcement.
//   * Per-bank refresh state (BANK_REFRESHING) is set externally; this
//     module doesn't drive it yet.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module xbank_timers_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    input  logic [7:0]                 t_rcd_i,
    input  logic [7:0]                 t_rp_i,
    input  logic [7:0]                 t_ras_i,    // v1: informational
    input  logic [7:0]                 t_rc_i,     // v1: informational
    input  logic [7:0]                 t_wr_i,
    input  logic [7:0]                 t_wtr_i,    // v1: not per-bank
    input  logic [7:0]                 t_rtp_i,

    // ----- bank-event strobes from scheduler -----
    input  logic                       evt_act_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,
    input  logic                       evt_pre_i,
    input  logic [RKW-1:0]             evt_rank_i,
    input  logic [BKW-1:0]             evt_bank_i,
    input  logic [ROW_WIDTH-1:0]       evt_row_i,    // for ACT row-tracking

    // ----- per-bank readiness back to scheduler -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_act_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_rdwr_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_pre_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_row_active_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]   bank_open_row_o,
    output bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]           bank_state_o
);

    //=========================================================================
    // Per-bank state
    //=========================================================================
    bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]            r_state;
    logic        [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]       r_act_cnt;
    logic        [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]       r_rdwr_cnt;
    logic        [NUM_RANKS-1:0][NUM_BANKS-1:0][7:0]       r_pre_cnt;
    logic        [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] r_open_row;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state    <= '0;   // BANK_IDLE = 3'h0
            r_act_cnt  <= '0;
            r_rdwr_cnt <= '0;
            r_pre_cnt  <= '0;
            r_open_row <= '0;
        end else begin
            // 1. Decrement all per-bank counters (saturate at 0).
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                    if (r_act_cnt[k][b]  > 8'd0) r_act_cnt[k][b]  <= r_act_cnt[k][b]  - 8'd1;
                    if (r_rdwr_cnt[k][b] > 8'd0) r_rdwr_cnt[k][b] <= r_rdwr_cnt[k][b] - 8'd1;
                    if (r_pre_cnt[k][b]  > 8'd0) r_pre_cnt[k][b]  <= r_pre_cnt[k][b]  - 8'd1;

                    // 2. State transitions on counter expiry.
                    if (r_state[k][b] == BANK_ACTIVATING && r_act_cnt[k][b] == 8'd1) begin
                        r_state[k][b] <= BANK_ACTIVE;
                    end
                    if (r_state[k][b] == BANK_RD_BUSY && r_rdwr_cnt[k][b] == 8'd1) begin
                        r_state[k][b] <= BANK_ACTIVE;
                    end
                    if (r_state[k][b] == BANK_WR_BUSY && r_rdwr_cnt[k][b] == 8'd1) begin
                        r_state[k][b] <= BANK_ACTIVE;
                    end
                    if (r_state[k][b] == BANK_PRECHARGING && r_pre_cnt[k][b] == 8'd1) begin
                        r_state[k][b] <= BANK_IDLE;
                    end
                end
            end

            // 3. Apply incoming event strobes — overrides above for the
            //    targeted bank.
            if (evt_act_i) begin
                r_state   [evt_rank_i][evt_bank_i] <= BANK_ACTIVATING;
                r_act_cnt [evt_rank_i][evt_bank_i] <= t_rcd_i;
                r_open_row[evt_rank_i][evt_bank_i] <= evt_row_i;
            end
            if (evt_rd_i) begin
                r_state   [evt_rank_i][evt_bank_i] <= BANK_RD_BUSY;
                r_rdwr_cnt[evt_rank_i][evt_bank_i] <= t_rtp_i;
            end
            if (evt_wr_i) begin
                r_state   [evt_rank_i][evt_bank_i] <= BANK_WR_BUSY;
                r_rdwr_cnt[evt_rank_i][evt_bank_i] <= t_wr_i;
            end
            if (evt_pre_i) begin
                r_state  [evt_rank_i][evt_bank_i] <= BANK_PRECHARGING;
                r_pre_cnt[evt_rank_i][evt_bank_i] <= t_rp_i;
            end
        end
    end)

    //=========================================================================
    // Combinational per-bank ready vectors.
    //   act_ready  : bank can take an ACT  (state==IDLE AND pre_cnt==0)
    //   rdwr_ready : bank can take a RD/WR (state==ACTIVE AND act_cnt==0
    //                                       AND rdwr_cnt==0)
    //   pre_ready  : bank can take a PRE   (state==ACTIVE AND rdwr_cnt==0)
    //=========================================================================
    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                bank_act_ready_o [k][b] = (r_state[k][b] == BANK_IDLE)
                                       && (r_pre_cnt[k][b] == 8'd0);
                bank_rdwr_ready_o[k][b] = (r_state[k][b] == BANK_ACTIVE)
                                       && (r_act_cnt[k][b]  == 8'd0)
                                       && (r_rdwr_cnt[k][b] == 8'd0);
                bank_pre_ready_o [k][b] = (r_state[k][b] == BANK_ACTIVE)
                                       && (r_rdwr_cnt[k][b] == 8'd0);
                bank_row_active_o[k][b] = (r_state[k][b] == BANK_ACTIVE)
                                       || (r_state[k][b] == BANK_RD_BUSY)
                                       || (r_state[k][b] == BANK_WR_BUSY);
                bank_open_row_o  [k][b] = r_open_row[k][b];
            end
        end
    end

    assign bank_state_o = r_state;

    wire unused_v1 = |{ t_ras_i, t_rc_i, t_wtr_i };

endmodule : xbank_timers_fub
