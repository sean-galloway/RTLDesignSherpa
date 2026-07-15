// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axis_bus_meter
// Purpose: Per-cycle valid/ready bucket counter + byte/packet counters for one
//          AXI-Stream (AXIS) channel. The AXIS analogue of axi_bus_meter: same
//          4-bucket cycle classification, plus AXIS-native throughput counters
//          (bytes via tstrb, packets via tlast) that are WINDOW-INDEPENDENT.
//
// One instance per AXIS bus to be measured. Snoop tvalid/tready/tlast/tstrb/tid;
// the block is a pure observer (drives nothing back onto the bus).
//
// Cycle classification (identical to axi_bus_meter; see
// DMA_UTILIZATION_MEASUREMENT.md §3):
//
//   valid  ready    bucket           meaning
//   -----  -----    ------           -------
//     1      1      productive       beat transferred
//     1      0      backpressure     master wants to send, slave stalls
//     0      1      starvation       slave ready, master not producing
//     0      0      idle             both sides quiet
//
// AXIS-native counters (increment ONLY on a productive beat, valid&ready):
//   - o_agg_bytes   : += popcount(tstrb) each productive beat. This is the exact
//                     number of payload bytes moved, independent of how long the
//                     measurement window is held open -- so throughput =
//                     bytes / (busy_time) is robust to backpressure/idle padding
//                     that would distort a pure cycle-utilization figure.
//   - o_agg_beats   : += 1 each productive beat (== o_agg_productive; provided
//                     for convenience alongside bytes/packets).
//   - o_agg_packets : += 1 each productive beat with tlast (stream packets).
//
// Counters:
//   - Aggregate cycle buckets: 32-bit (42.9 s @ 100 MHz before wrap).
//   - Aggregate bytes: 64-bit (won't wrap in any realistic run).
//   - Aggregate beats/packets: 32-bit.
//   - Per-channel (by tid) cycle buckets: 16-bit x NUM_CHANNELS, with a
//     per-channel 4-bit overflow sticky (see axi_bus_meter for semantics).
//
// Control:
//   - i_clear  : synchronous one-cycle pulse; zeroes every counter + sticky.
//   - i_freeze : hold high to freeze the window (no counter moves). Drive from
//                the characterization window controller.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis_bus_meter #(
    parameter int DATA_WIDTH   = 512,
    parameter int NUM_CHANNELS = 8,
    parameter int TID_WIDTH    = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int SW           = DATA_WIDTH / 8,                    // tstrb width
    parameter int CW           = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                      aclk,
    input  logic                      aresetn,

    // Synchronous clear pulse (one cycle wide).
    input  logic                      i_clear,
    // Freeze: hold high to close the measurement window.
    input  logic                      i_freeze,

    // AXIS bus snoop. tid selects the per-channel bin (its low CW bits); for a
    // single-stream bus tie tid=0. tstrb counts payload bytes; if the stream has
    // no tstrb, tie it all-ones so bytes == beats * (DATA_WIDTH/8).
    input  logic                      i_tvalid,
    input  logic                      i_tready,
    input  logic                      i_tlast,
    input  logic [SW-1:0]             i_tstrb,
    input  logic [TID_WIDTH-1:0]      i_tid,

    // Aggregate cycle buckets
    output logic [31:0]               o_agg_productive,
    output logic [31:0]               o_agg_backpressure,
    output logic [31:0]               o_agg_starvation,
    output logic [31:0]               o_agg_idle,

    // Aggregate AXIS-native throughput counters (productive beats only)
    output logic [63:0]               o_agg_bytes,
    output logic [31:0]               o_agg_beats,
    output logic [31:0]               o_agg_packets,

    // Per-channel (by tid) cycle buckets
    output logic [15:0]               o_ch_productive   [NUM_CHANNELS],
    output logic [15:0]               o_ch_backpressure [NUM_CHANNELS],
    output logic [15:0]               o_ch_starvation   [NUM_CHANNELS],
    output logic [15:0]               o_ch_idle         [NUM_CHANNELS],

    // Per-channel overflow stickies, packed {prod, bp, starv, idle} per channel.
    output logic [NUM_CHANNELS*4-1:0] o_ch_overflow
);

    // =========================================================================
    // Bucket selection + payload-byte popcount
    // =========================================================================
    logic w_prod, w_bp, w_starv, w_idle;
    assign w_prod  =  i_tvalid &&  i_tready;
    assign w_bp    =  i_tvalid && !i_tready;
    assign w_starv = !i_tvalid &&  i_tready;
    assign w_idle  = !i_tvalid && !i_tready;

    // Byte count of THIS beat = number of asserted tstrb lanes.
    logic [$clog2(SW+1)-1:0] w_beat_bytes;
    always_comb begin
        w_beat_bytes = '0;
        for (int b = 0; b < SW; b++) w_beat_bytes += ($clog2(SW+1))'(i_tstrb[b]);
    end

    // Channel bin index (low CW bits of tid).
    logic [CW-1:0] w_ch;
    assign w_ch = i_tid[CW-1:0];

    // =========================================================================
    // Aggregate cycle buckets
    // =========================================================================
    logic [31:0] r_agg_prod, r_agg_bp, r_agg_starv, r_agg_idle;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_agg_prod <= '0; r_agg_bp <= '0; r_agg_starv <= '0; r_agg_idle <= '0;
        end else if (i_clear) begin
            r_agg_prod <= '0; r_agg_bp <= '0; r_agg_starv <= '0; r_agg_idle <= '0;
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
    // Aggregate AXIS-native throughput counters (productive beats only)
    // =========================================================================
    logic [63:0] r_agg_bytes;
    logic [31:0] r_agg_beats, r_agg_packets;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_agg_bytes <= '0; r_agg_beats <= '0; r_agg_packets <= '0;
        end else if (i_clear) begin
            r_agg_bytes <= '0; r_agg_beats <= '0; r_agg_packets <= '0;
        end else if (!i_freeze && w_prod) begin
            r_agg_bytes   <= r_agg_bytes   + 64'(w_beat_bytes);
            r_agg_beats   <= r_agg_beats   + 32'd1;
            if (i_tlast) r_agg_packets <= r_agg_packets + 32'd1;
        end
    )
    assign o_agg_bytes   = r_agg_bytes;
    assign o_agg_beats   = r_agg_beats;
    assign o_agg_packets = r_agg_packets;

    // =========================================================================
    // Per-channel cycle buckets + overflow stickies (binned by tid)
    // =========================================================================
    logic [15:0] r_ch_prod  [NUM_CHANNELS];
    logic [15:0] r_ch_bp    [NUM_CHANNELS];
    logic [15:0] r_ch_starv [NUM_CHANNELS];
    logic [15:0] r_ch_idle  [NUM_CHANNELS];
    logic [3:0]  r_ch_overflow [NUM_CHANNELS];  // {prod, bp, starv, idle}

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int c = 0; c < NUM_CHANNELS; c++) begin
                r_ch_prod[c] <= '0; r_ch_bp[c] <= '0; r_ch_starv[c] <= '0;
                r_ch_idle[c] <= '0; r_ch_overflow[c] <= '0;
            end
        end else if (i_clear) begin
            for (int c = 0; c < NUM_CHANNELS; c++) begin
                r_ch_prod[c] <= '0; r_ch_bp[c] <= '0; r_ch_starv[c] <= '0;
                r_ch_idle[c] <= '0; r_ch_overflow[c] <= '0;
            end
        end else if (!i_freeze) begin
            // AXIS carries tid on every valid cycle, so bin by tid whenever the
            // bus is active (valid or ready). Idle cycles (both low) are not
            // attributable to a channel and only land in the aggregate.
            if (w_prod) begin
                if (r_ch_prod [w_ch] == 16'hFFFF) r_ch_overflow[w_ch][3] <= 1'b1;
                r_ch_prod [w_ch] <= r_ch_prod [w_ch] + 16'd1;
            end
            if (w_bp) begin
                if (r_ch_bp   [w_ch] == 16'hFFFF) r_ch_overflow[w_ch][2] <= 1'b1;
                r_ch_bp   [w_ch] <= r_ch_bp   [w_ch] + 16'd1;
            end
            if (w_starv) begin
                if (r_ch_starv[w_ch] == 16'hFFFF) r_ch_overflow[w_ch][1] <= 1'b1;
                r_ch_starv[w_ch] <= r_ch_starv[w_ch] + 16'd1;
            end
        end
    )

    always_comb begin
        for (int c = 0; c < NUM_CHANNELS; c++) begin
            o_ch_productive  [c] = r_ch_prod [c];
            o_ch_backpressure[c] = r_ch_bp   [c];
            o_ch_starvation  [c] = r_ch_starv[c];
            o_ch_idle        [c] = r_ch_idle [c];
        end
    end
    always_comb begin
        o_ch_overflow = '0;
        for (int c = 0; c < NUM_CHANNELS; c++) o_ch_overflow[c*4 +: 4] = r_ch_overflow[c];
    end

endmodule : axis_bus_meter
