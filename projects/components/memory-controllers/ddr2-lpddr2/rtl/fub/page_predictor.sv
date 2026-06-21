// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: page_predictor
// Purpose: Per-(rank, bank) 2-bit saturating "predict open" hint for
//          the HAPPY hybrid page policy.
//
//          Each (rank, bank) has a 2-bit counter:
//            00 = strongly closed   (prefer auto-precharge)
//            01 = weakly closed     (prefer auto-precharge)
//            10 = weakly open       (prefer leave-open)
//            11 = strongly open     (prefer leave-open)
//
//          Update rules (driven by evt_act_i with row info):
//            * Row HIT  (ACT on same row as previous) → counter ++
//            * Row MISS (ACT on different row)         → counter --
//
//          Output `predict_open_o[r][b] = counter[MSB]` is the hint
//          the scheduler uses to decide RDA/WRA vs RD/WR in HAPPY_HYBRID
//          mode. Hysteresis means the predictor doesn't flip on every
//          single access.
//
//          The predictor is updated on the ACT event (which carries the
//          target row). At that moment we compare against the LAST row
//          we saw for that bank (a per-bank history register). The first
//          ACT on a bank is treated as neither hit nor miss (no update).
//
// Strict-flop outputs: every output port is the Q of a dedicated flop.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module page_predictor
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

    // ----- ACT event from scheduler (post-issue, registered) -----
    input  logic                       evt_act_i,
    input  logic [RKW-1:0]             evt_rank_i,
    input  logic [BKW-1:0]             evt_bank_i,
    input  logic [ROW_WIDTH-1:0]       evt_row_i,

    // ----- prediction output: 1 = predict next access will hit -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0] predict_open_o
);

    //=========================================================================
    // Per-(rank, bank) state.
    //=========================================================================
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][1:0]            r_counter;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  r_last_row;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 r_first_act_done;

    //=========================================================================
    // Update on ACT event.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            // Initialize at "weakly closed" — closed-page-like behavior
            // until the predictor has seen evidence of locality.
            r_counter        <= '0;
            r_last_row       <= '0;
            r_first_act_done <= '0;
        end else if (evt_act_i) begin
            // Update history row regardless of hit/miss.
            r_last_row[evt_rank_i][evt_bank_i] <= evt_row_i;

            if (!r_first_act_done[evt_rank_i][evt_bank_i]) begin
                // First ACT on this bank — no update, just record.
                r_first_act_done[evt_rank_i][evt_bank_i] <= 1'b1;
            end else begin
                if (r_last_row[evt_rank_i][evt_bank_i] == evt_row_i) begin
                    // Row HIT — saturate up.
                    if (r_counter[evt_rank_i][evt_bank_i] != 2'b11) begin
                        r_counter[evt_rank_i][evt_bank_i] <=
                            r_counter[evt_rank_i][evt_bank_i] + 2'b01;
                    end
                end else begin
                    // Row MISS — saturate down.
                    if (r_counter[evt_rank_i][evt_bank_i] != 2'b00) begin
                        r_counter[evt_rank_i][evt_bank_i] <=
                            r_counter[evt_rank_i][evt_bank_i] - 2'b01;
                    end
                end
            end
        end
    end)

    //=========================================================================
    // Strict-flop output: predict-open = counter MSB.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            predict_open_o <= '0;
        end else begin
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned b = 0; b < NUM_BANKS; b++) begin
                    predict_open_o[k][b] <= r_counter[k][b][1];
                end
            end
        end
    end)

endmodule : page_predictor
