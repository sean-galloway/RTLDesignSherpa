// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_wr_serializer
// Purpose: Drive DFI write data. Purely mechanical: on a WR command (wr_fire),
//          wait t_phy_wrlat DFI cycles, then stream one DFI-word per cycle from
//          the write-data FIFO onto dfi_wrdata (+ en + mask) until the burst's
//          `last` word. One pop = one DFI cycle = ZERO bubbles.
//
//          The internal datapath unit IS the DFI word (dfi_wrdata width): it
//          already carries all DFI_RATE phases, so dfi_signal_pack splits it to
//          the pins. No per-beat packing here. The write data is pre-staged in
//          the FIFO (the wr CAM drains it when the command is scheduled), so at
//          wr_fire the burst is already waiting — the drive never stalls.
//
//          AXI wstrb=1 (write byte) -> DFI mask=1 means MASK. mask = ~strb.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_wr_serializer #(
    parameter int DFI_DATA_WIDTH = 128,             // = DRAM_BEAT_WIDTH * DFI_RATE
    parameter int DFI_RATE       = 2,
    parameter int DFI_STRB_WIDTH = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int WRLAT_W        = 8
) (
    input  logic                        dfi_clk,
    input  logic                        dfi_rstn,

    input  logic [WRLAT_W-1:0]          t_phy_wrlat_i,   // WR cmd -> wrdata_en

    // WR command strobe (from pumice_dfi_cmd_path, dfi_clk)
    input  logic                        wr_fire_i,

    // write-data FIFO (DFI-word granular): {last, strb, data}
    input  logic                        wd_valid_i,
    output logic                        wd_ready_o,
    input  logic [DFI_DATA_WIDTH-1:0]   wd_data_i,
    input  logic [DFI_STRB_WIDTH-1:0]   wd_strb_i,
    input  logic                        wd_last_i,

    // DFI write-data bus
    output logic [DFI_DATA_WIDTH-1:0]   dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]     dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]   dfi_wrdata_mask_o
);

    // STATELESS multi-burst serializer (no FSM — mirror of pumice_dfi_rd_aligner).
    // Each WR command (wr_fire_i) MATURES t_phy_wrlat DFI cycles later, when its
    // burst becomes eligible to drive; the burst then streams one DFI-word/cycle
    // from the FIFO until wd_last. Track fires in a shift register and count
    // matured-but-not-finished bursts in r_owed. Drive whenever a burst is owed
    // and the FIFO has a word. This handles every write cadence by construction:
    // consecutive bursts BL_WORDS apart mature back-to-back (contiguous drive);
    // tCCD-paced writes (tCCD > DQ occupancy, the x16 BL4 case) mature with a
    // matching bubble; N in flight -> N owed. The prior FSM's "seamless
    // continuation" assumed the next burst was always due the cycle after the
    // last word, which drops the tCCD bubble and drives write data early.
    localparam int MAX_WRLAT = 31;                 // DFI cycles; DDR2/3 wr-lat fits
    localparam int PIPE       = MAX_WRLAT + 1;

    logic [PIPE-1:0] r_age;
    // w_fired[j] = a WR command fired j cycles ago; j=0 is this cycle (so
    // t_phy_wrlat==0 matures/drives word0 on the fire cycle itself).
    logic [PIPE:0]   w_fired;
    assign w_fired = {r_age, wr_fire_i};

    // A fire matures (its burst becomes eligible to drive) at age t_phy_wrlat.
    logic w_mature;
    always_comb begin
        automatic int unsigned midx = int'(t_phy_wrlat_i);
        w_mature = (midx <= PIPE) ? w_fired[midx] : 1'b0;
    end

    // Matured bursts owed a drive (including one maturing this cycle).
    localparam int OWEDW = 3;   // paced => small; bounded by in-flight WR depth
    logic [OWEDW-1:0] r_owed;
    logic [OWEDW-1:0] w_owed_now;
    assign w_owed_now = r_owed + (w_mature ? OWEDW'(1) : OWEDW'(0));

    logic w_drive;
    assign w_drive    = (w_owed_now != '0) && wd_valid_i;
    assign wd_ready_o = w_drive;                 // pop as we drive (1 word/cycle)

    assign dfi_wrdata_o      = wd_data_i;
    assign dfi_wrdata_en_o   = w_drive ? {DFI_EN_WIDTH{1'b1}}   : '0;
    assign dfi_wrdata_mask_o = w_drive ? ~wd_strb_i             : '0;

    // a driven word marked last completes the front burst
    logic w_burst_last;
    assign w_burst_last = w_drive && wd_last_i;

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_age  <= '0;
            r_owed <= '0;
        end else begin
            r_age  <= {r_age[PIPE-2:0], wr_fire_i};
            r_owed <= w_owed_now - (w_burst_last ? OWEDW'(1) : OWEDW'(0));
        end
    )

endmodule : pumice_dfi_wr_serializer
