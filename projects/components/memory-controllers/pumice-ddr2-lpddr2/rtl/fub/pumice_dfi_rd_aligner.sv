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
//          intake can split words back to AXI R beats. The rddata_en window is a
//          STATELESS delay line (shift register of fires + windowed-OR), so any
//          number of outstanding reads at any cadence (contiguous BL_WORDS-apart
//          OR tCCD-spaced with a DQ bubble) are handled by construction — no FSM.
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

    // ---- rddata_en window: a STATELESS delay line (no FSM) ------------------
    // A read fired k cycles ago is "due" its rddata_en window over the cycles
    // [t_rddata_en, t_rddata_en+BL_WORDS-1] after the fire. Track fires in a
    // shift register (r_age[k] = a read fired k+1 cycles ago) and assert enable
    // whenever ANY in-flight fire is inside its own window. This handles every
    // read cadence by construction: reads BL_WORDS apart -> adjacent windows ->
    // contiguous enable; reads paced further (tCCD > BL_WORDS, the x16 BL4 case)
    // -> a matching bubble; N reads in flight -> N independent windows. There is
    // no "next window" decision to mis-time — the prior FSM's contiguous-window
    // assumption is what dropped the tCCD bubble and read a zero beat on silicon.
    localparam int MAX_RDDATA_EN = 31;                 // DFI cycles; DDR2/3 rd-lat fits
    localparam int PIPE          = MAX_RDDATA_EN + BL_WORDS;

    logic [PIPE-1:0] r_age;
    // w_fired[j] = a read fired j cycles ago; j=0 is this cycle (combinational,
    // so t_rddata_en==0 drives word0 on the fire cycle itself).
    logic [PIPE:0]   w_fired;
    assign w_fired = {r_age, rd_fire_i};

    logic w_en;
    always_comb begin
        w_en = 1'b0;
        for (int b = 0; b < BL_WORDS; b++) begin
            automatic int unsigned idx = int'(t_rddata_en_i) + b;
            if (idx <= PIPE) w_en |= w_fired[idx];
        end
    end
    assign dfi_rddata_en_o = w_en ? {DFI_EN_WIDTH{1'b1}} : '0;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) r_age <= '0;
        else                         r_age <= {r_age[PIPE-2:0], rd_fire_i};
    )

    // ---- capture: gate to the aligner's own enable window -------------------
    // The a7ddrphy asserts a PREAMBLE dfi_rddata_valid one cycle BEFORE the
    // enable window (data still 0), then the real valid+data after. Capturing on
    // raw |dfi_rddata_valid| grabs that zero preamble beat and shifts the whole
    // read stream -> the on-silicon 2-of-4 device-word corruption. Only data that
    // arrives once THIS read's enable window has opened is real: accumulate a
    // per-read capture CREDIT of +1 per ENABLE cycle (= BL_WORDS per read, and
    // never before the enable, so the pre-enable preamble is skipped), -1 per
    // captured word; capture only while credit != 0.
    localparam int CRDW = $clog2((PIPE + 1) * BL_WORDS + 1) + 1;
    logic [CRDW-1:0] r_credit;
    logic [CNTW:0]   r_rcnt;    // words captured so far in this burst

    logic w_capture, w_cap_fire;
    assign w_capture  = (|dfi_rddata_valid_i) && (r_credit != '0);
    assign w_cap_fire = w_capture && rd_ready_i;

    assign rd_valid_o = w_capture;
    assign rd_data_o  = dfi_rddata_i;
    assign rd_resp_o  = RESP_OKAY;
    assign rd_last_o  = w_capture && (r_rcnt == (CNTW+1)'(BL_WORDS - 1));

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_rcnt   <= '0;
            r_credit <= '0;
        end else begin
            r_credit <= r_credit
                      + (w_en       ? CRDW'(1) : CRDW'(0))   // +1 per enable cycle
                      - (w_cap_fire ? CRDW'(1) : CRDW'(0));
            if (w_cap_fire) begin
                if (r_rcnt == (CNTW+1)'(BL_WORDS - 1)) r_rcnt <= '0;   // burst done
                else                                    r_rcnt <= r_rcnt + 1'b1;
            end
        end
    )

endmodule : pumice_dfi_rd_aligner
