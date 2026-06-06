// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter_threshold
// Purpose: Active-trans-count + latency threshold detection (split out of
//          axi_monitor_reporter so integrators can drop it with
//          ENABLE_THRESHOLD_LOGIC=0). Owns the per-slot latency pipeline
//          (16 × 32-bit flops + 16 × threshold flags) so the area saving
//          is real when disabled.
//
// Emits ONE packet at a time via pkt_valid (top reporter strobes pkt_taken
// to clear edge flags and arm the next detection). Active-count and
// latency-event arbitration is internal: active-count wins because it
// reflects an instantaneous condition rather than a per-slot late event.
//
// Sequential. Author: sean galloway. Created: 2026-06-06.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_reporter_threshold
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 16,
    parameter bit IS_READ          = 1'b1,
    parameter int IDX_W            = $clog2(MAX_TRANSACTIONS)
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    input  bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    input  logic                        cfg_threshold_enable,
    input  logic [15:0]                 active_trans_threshold,
    input  logic [31:0]                 latency_threshold,

    // Top reporter tells us when output bus is free (no FIFO read + no
    // monbus_valid). Threshold packets bypass the FIFO and inject
    // directly; we need to know when not to overwrite an in-flight one.
    input  logic                        output_busy,
    input  logic                        pkt_taken,   // pulsed when our packet was accepted

    output logic                        pkt_valid,
    output logic [3:0]                  pkt_type,
    output logic [7:0]                  pkt_event_code,
    output logic [8:0]                  pkt_channel,
    output logic [63:0]                 pkt_data
);

    function automatic logic [63:0] pad_address(input logic [31:0] v);
        return 64'(v);
    endfunction

    // Edge-sticky flags so we don't re-fire on the same crossing every cycle.
    logic r_active_crossed;
    logic r_latency_crossed;

    // Per-slot registered latency + threshold-exceeded flags.
    // Computed combinationally would yield a 16-wide CARRY chain plus mux
    // to the output; the pipeline below splits this across a cycle.
    logic [31:0]                 r_latency [MAX_TRANSACTIONS];
    logic [MAX_TRANSACTIONS-1:0] r_latency_over_thresh;

    // Active count (combinational).
    logic [7:0] w_active_count;
    logic       w_active_detect;
    always_comb begin
        w_active_count = '0;
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (trans_table[idx].valid &&
                trans_table[idx].state != TRANS_COMPLETE &&
                trans_table[idx].state != TRANS_ERROR) begin
                w_active_count = w_active_count + 1'b1;
            end
        end
        /* verilator lint_off WIDTHEXPAND */
        w_active_detect = cfg_threshold_enable &&
                          ({8'h0, w_active_count} > active_trans_threshold) &&
                          !r_active_crossed && !output_busy;
        /* verilator lint_on WIDTHEXPAND */
    end

    // Latency event selection (combinational, off the registered pipeline).
    logic [IDX_W-1:0] w_lat_sel;
    logic             w_has_lat;
    always_comb begin
        w_lat_sel = '0;
        w_has_lat = 1'b0;
        if (cfg_threshold_enable) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (r_latency_over_thresh[idx] && !w_has_lat) begin
                    /* verilator lint_off WIDTHTRUNC */
                    w_lat_sel = idx[IDX_W-1:0];
                    /* verilator lint_on WIDTHTRUNC */
                    w_has_lat = 1'b1;
                end
            end
        end
    end

    // Pipeline registers + edge flags.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_latency[idx] <= '0;
            end
            r_latency_over_thresh <= '0;
            r_active_crossed      <= 1'b0;
            r_latency_crossed     <= 1'b0;
        end else begin
            // Per-slot latency pipeline — computed from LIVE trans_table
            // so r_latency[idx] is in-sync with the next-cycle scan.
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                logic [31:0] lat;
                if (IS_READ) begin
                    lat = trans_table[idx].data_timestamp -
                          trans_table[idx].addr_timestamp;
                end else begin
                    lat = trans_table[idx].resp_timestamp -
                          trans_table[idx].addr_timestamp;
                end
                r_latency[idx] <= lat;
                r_latency_over_thresh[idx] <=
                    trans_table[idx].valid &&
                    (trans_table[idx].state == TRANS_COMPLETE) &&
                    (lat > latency_threshold) &&
                    !r_latency_crossed;
            end

            // Edge flags. Set when we fire; clear when condition lifts.
            if (w_active_detect && pkt_taken && pkt_type == PktTypeThreshold &&
                pkt_event_code == AXI_THRESH_ACTIVE_COUNT) begin
                r_active_crossed <= 1'b1;
            end
            /* verilator lint_off WIDTHEXPAND */
            else if ({8'h0, w_active_count} <= active_trans_threshold) begin
                r_active_crossed <= 1'b0;
            end
            /* verilator lint_on WIDTHEXPAND */

            if (w_has_lat && pkt_taken && pkt_type == PktTypeThreshold &&
                pkt_event_code == AXI_THRESH_LATENCY) begin
                r_latency_crossed <= 1'b1;
            end
        end
    )

    // Output mux: active-count beats latency event.
    always_comb begin
        pkt_valid      = 1'b0;
        pkt_type       = PktTypeThreshold;
        pkt_event_code = AXI_THRESH_ACTIVE_COUNT;
        pkt_channel    = '0;
        pkt_data       = '0;

        if (w_active_detect) begin
            pkt_valid      = 1'b1;
            pkt_event_code = AXI_THRESH_ACTIVE_COUNT;
            pkt_data       = 64'(w_active_count);  // zero-extend
            pkt_channel    = '0;
        end else if (w_has_lat && !output_busy) begin
            pkt_valid      = 1'b1;
            pkt_event_code = AXI_THRESH_LATENCY;
            pkt_data       = pad_address(r_latency[w_lat_sel]);
            pkt_channel    = {3'b0, trans_table[w_lat_sel].channel[5:0]};
        end
    end

endmodule : axi_monitor_reporter_threshold
