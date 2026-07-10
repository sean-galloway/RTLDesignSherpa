// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_rd_aligner
// Purpose: DFI read-data alignment (mirror of the write serializer). On a RD
//          command (rd_fire), drive dfi_rddata_en for the read window starting
//          t_rddata_en DFI cycles later; capture dfi_rddata whenever the PHY
//          asserts dfi_rddata_valid, and push one DFI-word/cycle into the read
//          FIFO {last, resp, data} — bubble-free, one word per valid cycle.
//
//          Internal unit is the DFI word (= dfi_rddata width). BL_WORDS =
//          BL/DFI_RATE words per burst; `last` marks the final word so the read
//          intake can split words back to AXI R beats. v1: one outstanding read
//          window (single-issue, tRTW/tCCD spaced).
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_rd_aligner #(
    parameter int DFI_DATA_WIDTH  = 128,
    parameter int DFI_RATE        = 2,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int BL_WORDS        = 4,     // DFI words per read burst (BL/DFI_RATE)
    parameter int RDEN_W          = 8
) (
    input  logic                        dfi_clk,
    input  logic                        dfi_rstn,

    input  logic [RDEN_W-1:0]           t_rddata_en_i,   // RD cmd -> rddata_en

    // RD command strobe (from pumice_dfi_cmd_path)
    input  logic                        rd_fire_i,

    // DFI read-data bus (from PHY)
    output logic [DFI_EN_WIDTH-1:0]     dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]   dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]  dfi_rddata_valid_i,

    // read FIFO push (DFI-word granular): {data, resp, last} -> CDC rddata FIFO
    output logic                        rd_valid_o,
    input  logic                        rd_ready_i,
    output logic [DFI_DATA_WIDTH-1:0]   rd_data_o,
    output logic [1:0]                  rd_resp_o,
    output logic                        rd_last_o
);

    localparam logic [1:0] RESP_OKAY = 2'b00;
    localparam int CNTW = (BL_WORDS > 1) ? $clog2(BL_WORDS) : 1;
    // S_EN en-cycle count = r_ecnt_seed + 1. When t_rddata_en==0 the fire cycle
    // already drives word0 (w_en_now), so S_EN needs BL_WORDS-1 more (seed-2);
    // otherwise S_EN covers all BL_WORDS (seed-1).
    localparam int ECNT_SEED     = (BL_WORDS > 1) ? (BL_WORDS - 1) : 0;
    localparam int ECNT_SEED_IMM = (BL_WORDS > 2) ? (BL_WORDS - 2) : 0;

    // ---- rddata_en window: assert for BL_WORDS cycles, t_rddata_en after RD --
    typedef enum logic [1:0] { S_IDLE, S_WAIT, S_EN } en_state_e;
    en_state_e            r_es;
    logic [RDEN_W-1:0]    r_ewait;
    logic [CNTW:0]        r_ecnt;   // remaining en cycles

    logic w_en_now;                 // t_rddata_en==0 immediate case
    assign w_en_now = rd_fire_i && (t_rddata_en_i == '0);
    assign dfi_rddata_en_o = ((r_es == S_EN) || w_en_now) ? {DFI_EN_WIDTH{1'b1}} : '0;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_es    <= S_IDLE;
            r_ewait <= '0;
            r_ecnt  <= '0;
        end else begin
            unique case (r_es)
                S_IDLE:
                    if (rd_fire_i) begin
                        if (t_rddata_en_i == '0) begin
                            r_ecnt <= (CNTW+1)'(ECNT_SEED_IMM);
                            r_es   <= (BL_WORDS > 1) ? S_EN : S_IDLE;  // word0 via w_en_now
                        end else begin
                            r_ecnt <= (CNTW+1)'(ECNT_SEED);
                            if (t_rddata_en_i == 8'd1) r_es <= S_EN;
                            else begin r_ewait <= t_rddata_en_i - 8'd1; r_es <= S_WAIT; end
                        end
                    end
                S_WAIT:
                    if (r_ewait == 8'd1) r_es <= S_EN;
                    else                 r_ewait <= r_ewait - 8'd1;
                S_EN:
                    if (r_ecnt == '0) r_es <= S_IDLE;
                    else              r_ecnt <= r_ecnt - 1'b1;
                default: r_es <= S_IDLE;
            endcase
        end
    )

    // ---- capture: push a word to the read FIFO on each rddata_valid ---------
    logic            w_word_valid;
    assign w_word_valid = |dfi_rddata_valid_i;

    logic [CNTW:0] r_rcnt;    // words captured so far in this burst
    logic          r_rbusy;

    assign rd_valid_o = w_word_valid;
    assign rd_data_o  = dfi_rddata_i;
    assign rd_resp_o  = RESP_OKAY;
    assign rd_last_o  = w_word_valid && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_rcnt  <= '0;
            r_rbusy <= 1'b0;
        end else begin
            if (w_word_valid && rd_ready_i) begin
                if (r_rcnt == (CNTW+1)'(BL_WORDS - 1)) r_rcnt <= '0;   // burst done
                else                                    r_rcnt <= r_rcnt + 1'b1;
            end
        end
    )

endmodule : pumice_dfi_rd_aligner
