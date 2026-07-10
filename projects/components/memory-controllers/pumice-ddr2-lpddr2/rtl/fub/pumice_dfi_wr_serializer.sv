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

    // A tiny latency queue of pending WR fires: each WR command starts a burst
    // t_phy_wrlat cycles later. With single-issue + tCCD spacing there is at
    // most one burst in flight, but a small countdown-per-fire is robust.
    // v1: one outstanding burst (single-issue, tWTR/tCCD spaced).
    typedef enum logic [1:0] { S_IDLE, S_WAIT, S_DRIVE } state_e;
    state_e            r_state;
    logic [WRLAT_W-1:0] r_wait;

    // Immediate-drive case: t_phy_wrlat == 0 means dfi_wrdata_en is concurrent
    // with the WR command (the a7ddrphy pre-pull board config uses this). That
    // needs a combinational drive on the wr_fire cycle itself.
    logic w_drive_now;
    assign w_drive_now = wr_fire_i && (t_phy_wrlat_i == '0);

    // drive when in S_DRIVE (or the immediate case) and the FIFO has the word
    logic w_drive;
    assign w_drive    = ((r_state == S_DRIVE) || w_drive_now) && wd_valid_i;
    assign wd_ready_o = w_drive;                 // pop as we drive (1 word/cycle)

    assign dfi_wrdata_o      = wd_data_i;
    assign dfi_wrdata_en_o   = w_drive ? {DFI_EN_WIDTH{1'b1}}   : '0;
    assign dfi_wrdata_mask_o = w_drive ? ~wd_strb_i             : '0;

    // Latency: first dfi_wrdata_en lands exactly t_phy_wrlat cycles after the
    // wr_fire pulse. Registered state becomes S_DRIVE at the (t_phy_wrlat-1)-th
    // edge after fire, so DRIVE is active during cycle fire+t_phy_wrlat.
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_state <= S_IDLE;
            r_wait  <= '0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (wr_fire_i) begin
                        if (t_phy_wrlat_i == '0) begin
                            // drove word0 combinationally this cycle; continue
                            // the rest of the burst next cycle unless it was 1 word
                            r_state <= (wd_valid_i && wd_last_i) ? S_IDLE : S_DRIVE;
                        end else if (t_phy_wrlat_i == 8'd1) begin
                            r_state <= S_DRIVE;                 // DRIVE at fire+1
                        end else begin
                            r_wait  <= t_phy_wrlat_i - 8'd1;    // WAIT wrlat-1 cyc
                            r_state <= S_WAIT;
                        end
                    end
                end
                S_WAIT: begin
                    if (r_wait == 8'd1) r_state <= S_DRIVE;     // DRIVE at fire+wrlat
                    else                r_wait  <= r_wait - 8'd1;
                end
                S_DRIVE: begin
                    if (w_drive && wd_last_i) r_state <= S_IDLE;
                end
                default: r_state <= S_IDLE;
            endcase
        end
    )

endmodule : pumice_dfi_wr_serializer
