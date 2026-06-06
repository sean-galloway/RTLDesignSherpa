// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter (0.9 refactor)
// Purpose: Thin top reporter — multiplexes per-packet-type sub-blocks
//          into the shared monbus FIFO + output register, marks events
//          as reported back to trans_mgr, and constructs the final
//          128-bit monitor_packet via the package helper.
//
// Per-packet-type detection lives in sub-blocks so integrators can drop
// any combination via ENABLE_*_LOGIC parameters and pay zero LUT/FF cost:
//   ENABLE_ERROR_LOGIC     : axi_monitor_reporter_error      (combinational)
//   ENABLE_TIMEOUT_LOGIC   : axi_monitor_reporter_timeout    (combinational)
//   ENABLE_COMPL_LOGIC     : axi_monitor_reporter_compl      (combinational)
//   ENABLE_THRESHOLD_LOGIC : axi_monitor_reporter_threshold  (16 latency flops + edge flags)
//   ENABLE_PERF_LOGIC      : axi_monitor_reporter_perf       (counters + 5-state FSM)
//
// Bridge case: set ERROR=1, all others 0 → ~70% of reporter LUT/FF drops.
//
// Documentation: rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md
// Author: sean galloway
// Created: 2025-10-18 (original) / 2026-06-06 (sub-block refactor)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_reporter
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    // NOTE: `import monitor_pkg::*;` intentionally omitted -- its helper
    // functions (get_packet_type etc.) duplicate monitor_common_pkg's, and
    // Vivado flags the duplicates as ambiguous under wildcard imports.
#(
    parameter int MAX_TRANSACTIONS    = 16,
    parameter int ADDR_WIDTH          = 32,
    parameter logic [7:0]  UNIT_ID    = 8'h09,
    parameter logic [15:0] AGENT_ID   = 16'h0063,
    parameter bit IS_READ             = 1'b1,
    parameter bit ENABLE_PERF_PACKETS = 1'b0,    // legacy alias for ENABLE_PERF_LOGIC compat
    parameter int INTR_FIFO_DEPTH     = 8,
    // Sub-block enables — gate the LOGIC, not just packet emission. Default
    // 1'b1 preserves legacy behavior; integrators (e.g. bridge) set 0 to
    // synthesize away unused detection cones.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = ENABLE_PERF_PACKETS
)
(
    input  logic                     aclk,
    input  logic                     aresetn,

    input  bus_transaction_t         trans_table[MAX_TRANSACTIONS],
    input  logic [MAX_TRANSACTIONS-1:0] timeout_detected,

    input  logic                     cfg_error_enable,
    input  logic                     cfg_compl_enable,
    input  logic                     cfg_threshold_enable,
    input  logic                     cfg_timeout_enable,
    input  logic                     cfg_perf_enable,
    input  logic                     cfg_debug_enable,    // reserved — debug emitter is future work

    input  logic                              monbus_ready,
    output logic                              monbus_valid,
    output monitor_packet_t                   monbus_packet,

    output logic [15:0]              event_count,
    output logic [15:0]              perf_completed_count,
    output logic [15:0]              perf_error_count,

    input  logic [15:0]              active_trans_threshold,
    input  logic [31:0]              latency_threshold,

    output logic [MAX_TRANSACTIONS-1:0] event_reported_flags
);

    localparam int IDX_W = $clog2(MAX_TRANSACTIONS);

    // -------------------------------------------------------------------------
    // Shared state: registered trans_table, event_reported, event_count.
    // -------------------------------------------------------------------------
    bus_transaction_t            r_trans_table_local [MAX_TRANSACTIONS];
    logic [MAX_TRANSACTIONS-1:0] r_event_reported;
    logic [15:0]                 r_event_count;
    assign event_reported_flags = r_event_reported;
    assign event_count          = r_event_count;

    // Reserved-for-future debug input.
    /* verilator lint_off UNUSED */
    logic unused_cfg_debug_enable;
    assign unused_cfg_debug_enable = cfg_debug_enable;
    /* verilator lint_on UNUSED */

    // -------------------------------------------------------------------------
    // FIFO entry type (local — sub-blocks export raw fields).
    // -------------------------------------------------------------------------
    typedef struct packed {
        logic [3:0]  packet_type;
        logic [7:0]  event_code;
        logic [8:0]  channel;
        logic [63:0] data;
    } monbus_entry_t;

    logic                             w_fifo_wr_valid;
    logic                             w_fifo_wr_ready;
    monbus_entry_t                    w_fifo_wr_data;
    logic                             w_fifo_rd_valid;
    logic                             w_fifo_rd_ready;
    monbus_entry_t                    w_fifo_rd_data;
    logic [$clog2(INTR_FIFO_DEPTH):0] w_fifo_count;

    gaxi_fifo_sync #(
        .REGISTERED      (1),
        .DATA_WIDTH      ($bits(monbus_entry_t)),
        .DEPTH           (INTR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1)
    ) intr_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_fifo_wr_valid),
        .wr_ready    (w_fifo_wr_ready),
        .wr_data     (w_fifo_wr_data),
        .rd_ready    (w_fifo_rd_ready),
        .count       (w_fifo_count),
        .rd_valid    (w_fifo_rd_valid),
        .rd_data     (w_fifo_rd_data)
    );

    // -------------------------------------------------------------------------
    // Sub-block outputs (tied to 0 when disabled by ENABLE_*).
    // -------------------------------------------------------------------------
    logic              err_valid,  to_valid,  compl_valid;
    logic [3:0]        err_type,   to_type,   compl_type;
    logic [7:0]        err_code,   to_code,   compl_code;
    logic [8:0]        err_chan,   to_chan,   compl_chan;
    logic [63:0]       err_data,   to_data,   compl_data;
    logic [IDX_W-1:0]  err_idx,    to_idx,    compl_idx;

    if (ENABLE_ERROR_LOGIC) begin : g_err
        axi_monitor_reporter_error #(
            .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
            .IDX_W            (IDX_W)
        ) u_err (
            .trans_table     (r_trans_table_local),
            .event_reported  (r_event_reported),
            .timeout_detected(timeout_detected),
            .cfg_error_enable(cfg_error_enable),
            .pkt_valid       (err_valid),
            .pkt_type        (err_type),
            .pkt_event_code  (err_code),
            .pkt_channel     (err_chan),
            .pkt_data        (err_data),
            .sel_idx         (err_idx)
        );
    end else begin : g_no_err
        assign err_valid = 1'b0;
        assign err_type  = '0;
        assign err_code  = '0;
        assign err_chan  = '0;
        assign err_data  = '0;
        assign err_idx   = '0;
    end

    if (ENABLE_TIMEOUT_LOGIC) begin : g_to
        axi_monitor_reporter_timeout #(
            .MAX_TRANSACTIONS  (MAX_TRANSACTIONS),
            .IDX_W             (IDX_W)
        ) u_to (
            .trans_table       (r_trans_table_local),
            .event_reported    (r_event_reported),
            .timeout_detected  (timeout_detected),
            .cfg_timeout_enable(cfg_timeout_enable),
            .pkt_valid         (to_valid),
            .pkt_type          (to_type),
            .pkt_event_code    (to_code),
            .pkt_channel       (to_chan),
            .pkt_data          (to_data),
            .sel_idx           (to_idx)
        );
    end else begin : g_no_to
        assign to_valid = 1'b0;
        assign to_type  = '0;
        assign to_code  = '0;
        assign to_chan  = '0;
        assign to_data  = '0;
        assign to_idx   = '0;
    end

    if (ENABLE_COMPL_LOGIC) begin : g_compl
        axi_monitor_reporter_compl #(
            .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
            .IDX_W           (IDX_W)
        ) u_compl (
            .trans_table     (r_trans_table_local),
            .event_reported  (r_event_reported),
            .cfg_compl_enable(cfg_compl_enable),
            .pkt_valid       (compl_valid),
            .pkt_type        (compl_type),
            .pkt_event_code  (compl_code),
            .pkt_channel     (compl_chan),
            .pkt_data        (compl_data),
            .sel_idx         (compl_idx)
        );
    end else begin : g_no_compl
        assign compl_valid = 1'b0;
        assign compl_type  = '0;
        assign compl_code  = '0;
        assign compl_chan  = '0;
        assign compl_data  = '0;
        assign compl_idx   = '0;
    end

    // -------------------------------------------------------------------------
    // FIFO write mux: priority error > timeout > compl (matches legacy).
    // -------------------------------------------------------------------------
    always_comb begin
        w_fifo_wr_valid       = 1'b0;
        w_fifo_wr_data        = '{default: '0};
        if (err_valid) begin
            w_fifo_wr_valid       = 1'b1;
            w_fifo_wr_data.packet_type = err_type;
            w_fifo_wr_data.event_code  = err_code;
            w_fifo_wr_data.channel     = err_chan;
            w_fifo_wr_data.data        = err_data;
        end else if (to_valid) begin
            w_fifo_wr_valid       = 1'b1;
            w_fifo_wr_data.packet_type = to_type;
            w_fifo_wr_data.event_code  = to_code;
            w_fifo_wr_data.channel     = to_chan;
            w_fifo_wr_data.data        = to_data;
        end else if (compl_valid) begin
            w_fifo_wr_valid       = 1'b1;
            w_fifo_wr_data.packet_type = compl_type;
            w_fifo_wr_data.event_code  = compl_code;
            w_fifo_wr_data.channel     = compl_chan;
            w_fifo_wr_data.data        = compl_data;
        end
    end

    assign w_fifo_rd_ready = monbus_ready && monbus_valid;

    // -------------------------------------------------------------------------
    // Event marking + counter feedback masks.
    //   - w_error_events / w_compl_events drive the perf sub-block counters
    //     AND the r_event_reported flop.
    //   - Marking is gated on FIFO accept (w_fifo_wr_valid & w_fifo_wr_ready)
    //     to match legacy behavior: a successful FIFO write marks all matching
    //     events as reported in that cycle.
    // -------------------------------------------------------------------------
    logic [MAX_TRANSACTIONS-1:0] w_events_to_mark;
    logic [MAX_TRANSACTIONS-1:0] w_error_events;
    logic [MAX_TRANSACTIONS-1:0] w_completion_events;
    always_comb begin
        w_events_to_mark    = '0;
        w_error_events      = '0;
        w_completion_events = '0;
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid &&
                (r_trans_table_local[idx].state == TRANS_ERROR ||
                 r_trans_table_local[idx].state == TRANS_ORPHANED ||
                 r_trans_table_local[idx].state == TRANS_COMPLETE) &&
                !r_event_reported[idx] && w_fifo_wr_valid && w_fifo_wr_ready) begin
                w_events_to_mark[idx] = 1'b1;
                if (r_trans_table_local[idx].state == TRANS_ERROR ||
                    r_trans_table_local[idx].state == TRANS_ORPHANED) begin
                    w_error_events[idx] = 1'b1;
                end else if (r_trans_table_local[idx].state == TRANS_COMPLETE) begin
                    w_completion_events[idx] = 1'b1;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Threshold sub-block (stateful — 16 latency flops + 2 edge flags + active
    // count detection). Drops entirely when ENABLE_THRESHOLD_LOGIC=0.
    // -------------------------------------------------------------------------
    logic        thresh_valid, thresh_taken;
    logic [3:0]  thresh_type;
    logic [7:0]  thresh_code;
    logic [8:0]  thresh_chan;
    logic [63:0] thresh_data;
    logic        w_output_busy;
    assign w_output_busy = monbus_valid || w_fifo_rd_valid;

    if (ENABLE_THRESHOLD_LOGIC) begin : g_thresh
        axi_monitor_reporter_threshold #(
            .MAX_TRANSACTIONS      (MAX_TRANSACTIONS),
            .IS_READ               (IS_READ),
            .IDX_W                 (IDX_W)
        ) u_thresh (
            .aclk                   (aclk),
            .aresetn                (aresetn),
            .trans_table            (r_trans_table_local),
            .cfg_threshold_enable   (cfg_threshold_enable),
            .active_trans_threshold (active_trans_threshold),
            .latency_threshold      (latency_threshold),
            .output_busy            (w_output_busy),
            .pkt_taken              (thresh_taken),
            .pkt_valid              (thresh_valid),
            .pkt_type               (thresh_type),
            .pkt_event_code         (thresh_code),
            .pkt_channel            (thresh_chan),
            .pkt_data               (thresh_data)
        );
    end else begin : g_no_thresh
        assign thresh_valid = 1'b0;
        assign thresh_type  = '0;
        assign thresh_code  = '0;
        assign thresh_chan  = '0;
        assign thresh_data  = '0;
    end

    // -------------------------------------------------------------------------
    // Perf sub-block (legacy completion/error count rollups). Drops entirely
    // when ENABLE_PERF_LOGIC=0; Stage A/B window perfmon is independent.
    // -------------------------------------------------------------------------
    logic        perf_valid, perf_taken;
    logic [3:0]  perf_type;
    logic [7:0]  perf_code;
    logic [8:0]  perf_chan;
    logic [63:0] perf_data;
    logic [15:0] perf_completed_count_w;
    logic [15:0] perf_error_count_w;

    if (ENABLE_PERF_LOGIC) begin : g_perf
        axi_monitor_reporter_perf #(
            .MAX_TRANSACTIONS(MAX_TRANSACTIONS)
        ) u_perf (
            .aclk                (aclk),
            .aresetn             (aresetn),
            .cfg_perf_enable     (cfg_perf_enable),
            .output_busy         (w_output_busy),
            .pkt_taken           (perf_taken),
            .error_marked_mask   (w_error_events),
            .compl_marked_mask   (w_completion_events),
            .pkt_valid           (perf_valid),
            .pkt_type            (perf_type),
            .pkt_event_code      (perf_code),
            .pkt_channel         (perf_chan),
            .pkt_data            (perf_data),
            .perf_completed_count(perf_completed_count_w),
            .perf_error_count    (perf_error_count_w)
        );
    end else begin : g_no_perf
        assign perf_valid             = 1'b0;
        assign perf_type              = '0;
        assign perf_code              = '0;
        assign perf_chan              = '0;
        assign perf_data              = '0;
        assign perf_completed_count_w = '0;
        assign perf_error_count_w     = '0;
    end

    assign perf_completed_count = perf_completed_count_w;
    assign perf_error_count     = perf_error_count_w;

    // -------------------------------------------------------------------------
    // Output mux + register: FIFO read > threshold > perf.
    // -------------------------------------------------------------------------
    logic [3:0]  r_packet_type;
    logic [7:0]  r_event_code;
    logic [63:0] r_event_data;
    logic [8:0]  r_event_channel;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= '0;
            end
            monbus_valid     <= 1'b0;
            r_event_count    <= '0;
            r_event_reported <= '0;
            r_packet_type    <= PktTypeError;
            r_event_code     <= EVT_NONE;
            r_event_data     <= '0;
            r_event_channel  <= '0;
        end else begin
            // Snapshot trans_table.
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= trans_table[idx];
            end

            // Dequeue current output once accepted.
            if (monbus_valid && monbus_ready) begin
                monbus_valid <= 1'b0;
            end

            // Mark events as reported + bump count.
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (!r_trans_table_local[idx].valid) begin
                    r_event_reported[idx] <= 1'b0;        // FIX-001: reuse slot
                end else if (w_events_to_mark[idx]) begin
                    r_event_reported[idx] <= 1'b1;
                    r_event_count         <= r_event_count + 1'b1;
                end
            end

            // Priority emit: FIFO -> threshold -> perf. Only one source per
            // cycle; threshold/perf gate on (!monbus_valid && !w_fifo_rd_valid)
            // via output_busy inside the sub-blocks.
            if (!monbus_valid && w_fifo_rd_valid) begin
                monbus_valid    <= 1'b1;
                r_packet_type   <= w_fifo_rd_data.packet_type;
                r_event_code    <= w_fifo_rd_data.event_code;
                r_event_data    <= w_fifo_rd_data.data;
                r_event_channel <= w_fifo_rd_data.channel;
            end else if (thresh_valid && !monbus_valid && !w_fifo_rd_valid) begin
                monbus_valid    <= 1'b1;
                r_packet_type   <= thresh_type;
                r_event_code    <= thresh_code;
                r_event_data    <= thresh_data;
                r_event_channel <= thresh_chan;
                r_event_count   <= r_event_count + 1'b1;
            end else if (perf_valid && !monbus_valid && !w_fifo_rd_valid) begin
                monbus_valid    <= 1'b1;
                r_packet_type   <= perf_type;
                r_event_code    <= perf_code;
                r_event_data    <= perf_data;
                r_event_channel <= perf_chan;
            end
        end
    )

    // pkt_taken pulses to threshold/perf when their packet was emitted.
    // Threshold uses it to set edge-sticky crossed flags; perf currently
    // ignores it (kept on the port for future back-pressure).
    assign thresh_taken = thresh_valid && !monbus_valid && !w_fifo_rd_valid;
    assign perf_taken   = perf_valid   && !monbus_valid && !w_fifo_rd_valid &&
                          !thresh_valid;

    // -------------------------------------------------------------------------
    // Construct the 128-bit monitor bus packet via package helper.
    // -------------------------------------------------------------------------
    always_comb begin
        monbus_packet = create_monitor_packet(
            r_packet_type,
            PROTOCOL_AXI,
            r_event_code,
            r_event_channel,
            UNIT_ID,
            AGENT_ID,
            r_event_data
        );
    end

    // w_fifo_count is observed by the FIFO instance only — tie it
    // through an unused-bit sink to keep the linter quiet.
    /* verilator lint_off UNUSED */
    logic unused_fifo_count;
    assign unused_fifo_count = |w_fifo_count;
    /* verilator lint_on UNUSED */

endmodule : axi_monitor_reporter
