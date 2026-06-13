// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: axi_bus_meter
// Purpose: Per-cycle valid/ready bucket counter for one AXI data channel.
//          Used by stream_char to characterize datapath utilization on the
//          stream engine's read R bus and write W bus.
//
// One instance per AXI bus to be measured. Drop in on the R channel of the
// read engine (aggregate + per-channel via rid) and on the W channel of the
// write engine (aggregate + per-channel via an engine-side sideband, since
// W beats carry no id in AXI4).
//
// Cycle classification (methodology: see DMA_UTILIZATION_MEASUREMENT.md §3):
//
//   valid  ready    bucket           meaning
//   -----  -----    ------           -------
//     1      1      productive       data delivered
//     1      0      backpressure     master wants to send, slave stalls
//     0      1      starvation       slave ready, master not producing
//     0      0      idle             both sides quiet
//
// Counters:
//   - Aggregate (32-bit, 4 buckets) -- always increments based on bus state.
//     Lives 42.9 s at 100 MHz before overflow, plenty for a single run.
//   - Per-channel (16-bit, 4 buckets, NUM_CHANNELS deep) -- increments the
//     bucket for `i_channel_id` only when `i_channel_valid` is high. The
//     caller drives `i_channel_valid` true whenever some channel is on the
//     hook for the current cycle (e.g. mid-burst). For cycles where the
//     engine has no work on any channel, leave it low and only aggregate
//     idle/starvation get attributed.
//   - Per-channel overflow sticky: NUM_CHANNELS x 4 bits. Each bit is set
//     when the corresponding 16-bit counter wraps. Software checks this
//     mask after stopping the meter; if any bit is set, the burst was too
//     long for 16-bit per-channel resolution (>655 us at 100 MHz) and the
//     per-channel numbers should be discarded for that channel.
//
// Clearing:
//   - `i_clear` is a synchronous one-cycle pulse. On clear, all counters
//     reset to 0 and all overflow stickies clear. Wire to the same control
//     bit that clears the debug_sram + harness CRC state (so the host gets
//     atomic reset of the entire measurement substrate from one CSR write).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_bus_meter #(
    parameter int NUM_CHANNELS = 8,
    parameter int CW           = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    // Synchronous clear pulse (one cycle wide).
    input  logic                          i_clear,

    // Freeze input. When high, every counter and overflow sticky holds
    // its value -- no productive/backpressure/starvation/idle increments,
    // no overflow flag flips. Drive this from the characterization
    // timer's 'done' so the measurement window closes the moment the
    // workload finishes; otherwise the lifetime starvation count drifts
    // upward at one bit per cycle for every cycle of post-burst
    // host-side polling, contaminating the in-window utilization math.
    // Hold low for unbounded free-running measurement.
    input  logic                          i_freeze,

    // AXI bus snoop. For the read engine, wire i_valid=m_axi_rvalid,
    // i_ready=m_axi_rready, i_channel_id=m_axi_rid[CW-1:0], and
    // i_channel_valid=m_axi_rvalid (rid is only meaningful when rvalid).
    // For the write engine, wire i_valid=m_axi_wvalid, i_ready=m_axi_wready,
    // i_channel_id=<engine's r_w_channel_id sideband>, and i_channel_valid
    // to a "W beats in flight on this channel" indicator from the engine.
    input  logic                          i_valid,
    input  logic                          i_ready,
    input  logic [CW-1:0]                 i_channel_id,
    input  logic                          i_channel_valid,

    // Aggregate counters
    output logic [31:0]                   o_agg_productive,
    output logic [31:0]                   o_agg_backpressure,
    output logic [31:0]                   o_agg_starvation,
    output logic [31:0]                   o_agg_idle,

    // Per-channel counters
    output logic [15:0]                   o_ch_productive   [NUM_CHANNELS],
    output logic [15:0]                   o_ch_backpressure [NUM_CHANNELS],
    output logic [15:0]                   o_ch_starvation   [NUM_CHANNELS],
    output logic [15:0]                   o_ch_idle         [NUM_CHANNELS],

    // Per-channel overflow stickies, packed {prod, bp, starv, idle} per channel.
    output logic [NUM_CHANNELS*4-1:0]     o_ch_overflow
);

    // =========================================================================
    // Bucket selection
    // =========================================================================
    logic w_prod, w_bp, w_starv, w_idle;
    assign w_prod  =  i_valid &&  i_ready;
    assign w_bp    =  i_valid && !i_ready;
    assign w_starv = !i_valid &&  i_ready;
    assign w_idle  = !i_valid && !i_ready;

    // =========================================================================
    // Aggregate counters
    // =========================================================================
    logic [31:0] r_agg_prod, r_agg_bp, r_agg_starv, r_agg_idle;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_agg_prod  <= '0;
            r_agg_bp    <= '0;
            r_agg_starv <= '0;
            r_agg_idle  <= '0;
        end else if (i_clear) begin
            r_agg_prod  <= '0;
            r_agg_bp    <= '0;
            r_agg_starv <= '0;
            r_agg_idle  <= '0;
        end else if (!i_freeze) begin
            if (w_prod)  r_agg_prod  <= r_agg_prod  + 32'd1;
            if (w_bp)    r_agg_bp    <= r_agg_bp    + 32'd1;
            if (w_starv) r_agg_starv <= r_agg_starv + 32'd1;
            if (w_idle)  r_agg_idle  <= r_agg_idle  + 32'd1;
        end
    )

    assign o_agg_productive   = r_agg_prod;
    assign o_agg_backpressure = r_agg_bp;
    assign o_agg_starvation   = r_agg_starv;
    assign o_agg_idle         = r_agg_idle;

    // =========================================================================
    // Per-channel counters + overflow stickies
    // =========================================================================
    logic [15:0] r_ch_prod   [NUM_CHANNELS];
    logic [15:0] r_ch_bp     [NUM_CHANNELS];
    logic [15:0] r_ch_starv  [NUM_CHANNELS];
    logic [15:0] r_ch_idle   [NUM_CHANNELS];
    logic [3:0]  r_ch_overflow [NUM_CHANNELS];  // {prod, bp, starv, idle}

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int c = 0; c < NUM_CHANNELS; c++) begin
                r_ch_prod    [c] <= '0;
                r_ch_bp      [c] <= '0;
                r_ch_starv   [c] <= '0;
                r_ch_idle    [c] <= '0;
                r_ch_overflow[c] <= '0;
            end
        end else if (i_clear) begin
            for (int c = 0; c < NUM_CHANNELS; c++) begin
                r_ch_prod    [c] <= '0;
                r_ch_bp      [c] <= '0;
                r_ch_starv   [c] <= '0;
                r_ch_idle    [c] <= '0;
                r_ch_overflow[c] <= '0;
            end
        end else if (!i_freeze && i_channel_valid) begin
            // Only increment the channel pointed to by i_channel_id.
            // The other channels' counters are unchanged this cycle.
            if (w_prod)  begin
                if (r_ch_prod   [i_channel_id] == 16'hFFFF)
                    r_ch_overflow[i_channel_id][3] <= 1'b1;
                r_ch_prod   [i_channel_id] <= r_ch_prod   [i_channel_id] + 16'd1;
            end
            if (w_bp)    begin
                if (r_ch_bp     [i_channel_id] == 16'hFFFF)
                    r_ch_overflow[i_channel_id][2] <= 1'b1;
                r_ch_bp     [i_channel_id] <= r_ch_bp     [i_channel_id] + 16'd1;
            end
            if (w_starv) begin
                if (r_ch_starv  [i_channel_id] == 16'hFFFF)
                    r_ch_overflow[i_channel_id][1] <= 1'b1;
                r_ch_starv  [i_channel_id] <= r_ch_starv  [i_channel_id] + 16'd1;
            end
            if (w_idle)  begin
                if (r_ch_idle   [i_channel_id] == 16'hFFFF)
                    r_ch_overflow[i_channel_id][0] <= 1'b1;
                r_ch_idle   [i_channel_id] <= r_ch_idle   [i_channel_id] + 16'd1;
            end
        end
    )

    // Output array drivers (Verilator can't infer unpacked-array assigns
    // from a register array directly, so name them explicitly).
    always_comb begin
        for (int c = 0; c < NUM_CHANNELS; c++) begin
            o_ch_productive  [c] = r_ch_prod  [c];
            o_ch_backpressure[c] = r_ch_bp    [c];
            o_ch_starvation  [c] = r_ch_starv [c];
            o_ch_idle        [c] = r_ch_idle  [c];
        end
    end

    // Pack overflow stickies as {ch[N-1], ..., ch[0]}, each 4 bits.
    always_comb begin
        o_ch_overflow = '0;
        for (int c = 0; c < NUM_CHANNELS; c++) begin
            o_ch_overflow[c*4 +: 4] = r_ch_overflow[c];
        end
    end

endmodule : axi_bus_meter
