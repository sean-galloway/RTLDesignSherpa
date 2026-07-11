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

    // Pipelined multi-burst serializer. Each WR command (wr_fire_i) queues one
    // burst; the burst's data drives t_phy_wrlat cycles after that fire, one
    // DFI-word per cycle until wd_last. The DFI cmd path paces column commands
    // exactly BL_WORDS DFI cycles apart (= the burst's DQ-bus occupancy), so a
    // following WR command's data is due the cycle right after the current
    // burst's last word — for ANY t_phy_wrlat (fire_{n+1}=fire_n+W ->
    // data_{n+1}=fire_n+W+L = burst_n_end+1). We therefore drive bursts
    // back-to-back with ZERO bubbles: on the last word, if another fire is
    // pending we continue straight into the next burst instead of returning to
    // idle. A fire that arrives while a burst is in flight is counted in
    // r_pending (was previously DROPPED, stranding the write in the PHY).
    localparam int PCW = 3;   // pending-fire counter (paced => small)
    typedef enum logic [1:0] { S_IDLE, S_WAIT, S_DRIVE } state_e;
    state_e             r_state;
    logic [WRLAT_W-1:0] r_wait;
    logic [PCW-1:0]     r_pending;

    // Fires available to start a burst this cycle (already-pending + this cycle).
    logic [PCW-1:0] w_avail;
    assign w_avail = r_pending + (wr_fire_i ? PCW'(1) : PCW'(0));

    // Begin a burst's FIRST word this cycle: from idle with t_phy_wrlat==0, or
    // seamlessly continuing on the previous burst's last word.
    logic w_start_now;   // drive word0 of a NEW burst this cycle
    assign w_start_now = (r_state == S_IDLE) && (w_avail != '0) && (t_phy_wrlat_i == '0);

    // drive when mid-burst (S_DRIVE) or starting a burst immediately, FIFO ready
    logic w_drive;
    assign w_drive    = ((r_state == S_DRIVE) || w_start_now) && wd_valid_i;
    assign wd_ready_o = w_drive;                 // pop as we drive (1 word/cycle)

    assign dfi_wrdata_o      = wd_data_i;
    assign dfi_wrdata_en_o   = w_drive ? {DFI_EN_WIDTH{1'b1}}   : '0;
    assign dfi_wrdata_mask_o = w_drive ? ~wd_strb_i             : '0;

    // burst-last strobe (a driven word marked last)
    logic w_burst_last;
    assign w_burst_last = w_drive && wd_last_i;

    // Whether we consume a pending fire this cycle to START a new burst.
    logic w_consume;
    always_comb begin
        w_consume = 1'b0;
        unique case (r_state)
            S_IDLE:  w_consume = (w_avail != '0);                 // start burst0
            S_DRIVE: w_consume = w_burst_last && (w_avail != '0); // seamless next
            default: w_consume = 1'b0;                            // WAIT: already consumed
        endcase
    end

    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_state   <= S_IDLE;
            r_wait    <= '0;
            r_pending <= '0;
        end else begin
            // pending fires: +1 on a fire, -1 when a burst starts driving
            r_pending <= w_avail - (w_consume ? PCW'(1) : PCW'(0));

            unique case (r_state)
                S_IDLE: begin
                    if (w_avail != '0) begin
                        if (t_phy_wrlat_i == '0)
                            // word0 drove combinationally this cycle; continue
                            // unless it was a single-word burst
                            r_state <= (wd_valid_i && wd_last_i) ? S_IDLE : S_DRIVE;
                        else if (t_phy_wrlat_i == 8'd1)
                            r_state <= S_DRIVE;                  // DRIVE at fire+1
                        else begin
                            r_wait  <= t_phy_wrlat_i - 8'd1;     // WAIT wrlat-1
                            r_state <= S_WAIT;
                        end
                    end
                end
                S_WAIT: begin
                    if (r_wait == 8'd1) r_state <= S_DRIVE;      // DRIVE at fire+wrlat
                    else                r_wait  <= r_wait - 8'd1;
                end
                S_DRIVE: begin
                    // On the last word: continue seamlessly if another burst is
                    // pending (its data is due next cycle), else go idle.
                    if (w_burst_last)
                        r_state <= (w_avail != '0) ? S_DRIVE : S_IDLE;
                end
                default: r_state <= S_IDLE;
            endcase
        end
    )

endmodule : pumice_dfi_wr_serializer
