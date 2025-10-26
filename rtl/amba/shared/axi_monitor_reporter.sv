// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter
// Purpose: Axi Monitor Reporter module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI Monitor Bus Reporter - Updated for Generic Monitor Package
 *
 * This module reports events and errors through a shared monitor bus.
 * It detects conditions from the AXI transaction table and formats them into
 * standard 64-bit interrupt packet format for system-wide event notification.
 * Updated to work with the enhanced monitor_pkg that supports multiple protocols.
 */

`include "reset_defs.svh"
module axi_monitor_reporter
    import monitor_pkg::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int UNIT_ID             = 9,    // Unit identifier (4 bits used)
    parameter int AGENT_ID            = 99,   // Agent identifier (8 bits used)
    parameter bit IS_READ             = 1'b1,    // 1 for read, 0 for write
    parameter bit ENABLE_PERF_PACKETS = 1'b0,    // Enable performance metrics tracking
    parameter int INTR_FIFO_DEPTH     = 8     // interrupt fifo depth
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Transaction table (read-only access) - Fixed: Use unpacked array
    input  bus_transaction_t         trans_table[MAX_TRANSACTIONS],

    // Timeout detection flags from timeout module
    input  logic [MAX_TRANSACTIONS-1:0] timeout_detected,

    // Configuration enables for different packet types
    input  logic                     cfg_error_enable,    // Enable error packets
    input  logic                     cfg_compl_enable,    // Enable completion packets
    input  logic                     cfg_threshold_enable,// Enable threshold packets
    input  logic                     cfg_timeout_enable,  // Enable timeout packets
    input  logic                     cfg_perf_enable,     // Enable performance packets
    input  logic                     cfg_debug_enable,    // Enable debug packets

    // Interrupt bus output interface
    input  logic                     monbus_ready,  // Downstream ready
    output logic                     monbus_valid,  // Interrupt valid
    output logic [63:0]              monbus_packet, // Consolidated interrupt packet

    // Statistics output
    output logic [15:0]              event_count,    // Total event count

    // Performance metrics (only used when ENABLE_PERF_PACKETS=1)
    output logic [15:0]              perf_completed_count, // Number of completed transactions
    output logic [15:0]              perf_error_count,     // Number of error transactions

    // Performance metric thresholds
    input  logic [15:0]              active_trans_threshold,
    input  logic [31:0]              latency_threshold,

    // Event reported feedback to trans_mgr (FIX-001)
    output logic [MAX_TRANSACTIONS-1:0] event_reported_flags
);

    // Local version of transaction table for processing (flopped)
    bus_transaction_t r_trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if event has been reported for each transaction (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_event_reported;
    // FIX-001: Connect internal flag to output port for trans_mgr feedback
    assign event_reported_flags = r_event_reported;

    // Localparams for address width handling
    localparam int ADDR_PAD_WIDTH = (ADDR_WIDTH <= 38) ? (38 - ADDR_WIDTH) : 0;
    localparam bit ADDR_NEEDS_TRUNCATE = (ADDR_WIDTH > 38);

    // Helper function to safely pad/truncate address for packet data field
    function automatic logic [37:0] pad_address(input logic [ADDR_WIDTH-1:0] addr);
        if (ADDR_NEEDS_TRUNCATE) begin
            return addr[37:0];
        end else begin
            return {{ADDR_PAD_WIDTH{1'b0}}, addr};
        end
    endfunction

    // Threshold crossing flags (flopped)
    logic r_active_threshold_crossed;
    logic r_latency_threshold_crossed;

    // Event count (flopped)
    logic [15:0] r_event_count;
    assign event_count = r_event_count;

    // Performance metrics counters (flopped)
    logic [15:0] r_perf_completed_count;
    logic [15:0] r_perf_error_count;

    // Assign performance metrics outputs
    assign perf_completed_count = r_perf_completed_count;
    assign perf_error_count = r_perf_error_count;

    // Performance report state machine (flopped)
    logic [2:0] r_perf_report_state;

    // Interrupt FIFO entry type - Updated with new packet format
    typedef struct packed {
        logic [3:0]            packet_type;  // Packet type (updated bit allocation)
        logic [3:0]            event_code;   // Event code or metric type
        logic [5:0]            channel;      // Channel information
        logic [37:0]           data;         // Address or metric value (updated to 38 bits)
    } monbus_entry_t;

    // FIFO signals (combinational)
    logic                                 w_fifo_wr_valid;
    logic                                 w_fifo_wr_ready;
    monbus_entry_t                        w_fifo_wr_data;
    logic                                 w_fifo_rd_valid;
    logic                                 w_fifo_rd_ready;
    monbus_entry_t                        w_fifo_rd_data;
    logic [$clog2(INTR_FIFO_DEPTH):0]     w_fifo_count;  // Proper width calculation

    // Use gaxi_fifo_sync for the interrupt packet FIFO
    gaxi_fifo_sync #(
        .REGISTERED      (1),
        .DATA_WIDTH      ($bits(monbus_entry_t)),
        .DEPTH           (INTR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME   ("INTR_FIFO")
    ) intr_fifo(
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_fifo_wr_valid),
        .wr_ready      (w_fifo_wr_ready),
        .wr_data       (w_fifo_wr_data),
        .rd_ready      (w_fifo_rd_ready),
        .count        (w_fifo_count),
        .rd_valid      (w_fifo_rd_valid),
        .rd_data       (w_fifo_rd_data)
    );

    // Output registers (flopped)
    logic [3:0]  r_packet_type;
    logic [3:0]  r_event_code;
    logic [37:0] r_event_data;  // Updated to 38 bits to match new packet format
    logic [5:0]  r_event_channel;

    // Event detection signals - One for each type of event to report (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_error_events_detected;
    logic [MAX_TRANSACTIONS-1:0] w_timeout_events_detected;
    logic [MAX_TRANSACTIONS-1:0] w_completion_events_detected;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_error_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_timeout_idx;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_completion_idx;
    logic w_has_error_event;
    logic w_has_timeout_event;
    logic w_has_completion_event;

    // Event marking signals (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_events_to_mark;
    logic [MAX_TRANSACTIONS-1:0] w_error_events;
    logic [MAX_TRANSACTIONS-1:0] w_completion_events;

    // Active transaction count for threshold detection (combinational)
    logic [7:0] w_active_count_current;
    logic w_active_threshold_detection;

    // Latency threshold detection signals (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_latency_threshold_events;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_latency_idx;
    logic w_has_latency_event;

    // Pre-declare latency calculation variables to avoid latch inference
    logic [31:0] w_total_latency;
    logic [31:0] w_selected_latency_value;

    // Performance packet state and selection (combinational)
    logic w_generate_perf_packet_completed;
    logic w_generate_perf_packet_errors;
    logic [2:0] w_next_perf_report_state;

    // Error event detection - Updated to use unified event codes
    always_comb begin
        w_error_events_detected = '0;
        w_selected_error_idx = '0;
        w_has_error_event = 1'b0;

        // Scan for error events (exclude timeouts, include orphans)
        // Use timeout_detected signal to distinguish errors from timeouts
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] && cfg_error_enable &&
                    ((r_trans_table_local[idx].state == TRANS_ERROR && !timeout_detected[idx]) ||  // Error but not timeout
                     (r_trans_table_local[idx].state == TRANS_ORPHANED))) begin  // Orphaned transaction
                w_error_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected error
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_error_events_detected[idx] && !w_has_error_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_error_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_error_event = 1'b1;
            end
        end
    end

    // Timeout event detection - Updated to use unified event codes
    always_comb begin
        w_timeout_events_detected = '0;
        w_selected_timeout_idx = '0;
        w_has_timeout_event = 1'b0;

        // Scan for timeout events
        // Use timeout_detected signal from timeout module
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                r_trans_table_local[idx].state == TRANS_ERROR && cfg_timeout_enable &&
                timeout_detected[idx]) begin  // Is a timeout
                w_timeout_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected timeout
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_timeout_events_detected[idx] && !w_has_timeout_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_timeout_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_timeout_event = 1'b1;
            end
        end
    end

    // Completion event detection
    always_comb begin
        w_completion_events_detected = '0;
        w_selected_completion_idx = '0;
        w_has_completion_event = 1'b0;

        // Scan for completion events
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                r_trans_table_local[idx].state == TRANS_COMPLETE && cfg_compl_enable) begin
                w_completion_events_detected[idx] = 1'b1;
            end
        end

        // Priority encoder to select the first detected completion
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_completion_events_detected[idx] && !w_has_completion_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_selected_completion_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_completion_event = 1'b1;
            end
        end
    end

    // FIFO write interface - combines all event detections - Updated to use unified event codes
    always_comb begin
        w_fifo_wr_valid = 1'b0;
        w_fifo_wr_data = '{default: '0};

        // Priority: Error > Timeout > Completion
        if (w_has_error_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeError;
            w_fifo_wr_data.event_code = r_trans_table_local[w_selected_error_idx].event_code.raw_code;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_error_idx].channel[5:0];
            w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_error_idx].addr);
        end else if (w_has_timeout_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeTimeout;
            w_fifo_wr_data.event_code = r_trans_table_local[w_selected_timeout_idx].event_code.raw_code;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_timeout_idx].channel[5:0];
            w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_timeout_idx].addr);
        end else if (w_has_completion_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeCompletion;
            w_fifo_wr_data.event_code = EVT_TRANS_COMPLETE;
            w_fifo_wr_data.channel = r_trans_table_local[w_selected_completion_idx].channel[5:0];
            w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_completion_idx].addr);
        end
    end

    // FIFO read interface and event processing
    assign w_fifo_rd_ready = monbus_ready && monbus_valid;

    // Detect events that need to be marked as reported
    always_comb begin
        w_events_to_mark = '0;
        w_error_events = '0;
        w_completion_events = '0;

        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid) begin
                if ((r_trans_table_local[idx].state == TRANS_ERROR ||
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
    end

    // Active transaction count calculation
    always_comb begin
        w_active_count_current = '0;

        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table_local[idx].valid &&
                r_trans_table_local[idx].state != TRANS_COMPLETE &&
                r_trans_table_local[idx].state != TRANS_ERROR) begin
                w_active_count_current = w_active_count_current + 1'b1;
            end
        end

        /* verilator lint_off WIDTHEXPAND */
        w_active_threshold_detection = (({8'h0, w_active_count_current} > active_trans_threshold) &&
                                        !r_active_threshold_crossed &&
                                        !monbus_valid &&
                                        (w_fifo_rd_valid == 0));
        /* verilator lint_on WIDTHEXPAND */
    end

    // Latency threshold detection
    always_comb begin
        w_latency_threshold_events = '0;
        w_selected_latency_idx = '0;
        w_has_latency_event = 1'b0;
        w_total_latency = '0;

        if (ENABLE_PERF_PACKETS && cfg_perf_enable && cfg_threshold_enable) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (r_trans_table_local[idx].valid && r_trans_table_local[idx].state == TRANS_COMPLETE) begin
                    if (IS_READ) begin
                        w_total_latency = r_trans_table_local[idx].data_timestamp - r_trans_table_local[idx].addr_timestamp;
                    end else begin
                        w_total_latency = r_trans_table_local[idx].resp_timestamp - r_trans_table_local[idx].addr_timestamp;
                    end

                    if (w_total_latency > latency_threshold && !r_latency_threshold_crossed) begin
                        w_latency_threshold_events[idx] = 1'b1;
                    end
                end
            end

            // Priority encoder to select the first latency threshold event
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_latency_threshold_events[idx] && !w_has_latency_event) begin
                    /* verilator lint_off WIDTHTRUNC */
                    w_selected_latency_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                    /* verilator lint_on WIDTHTRUNC */
                    w_has_latency_event = 1'b1;
                end
            end
        end
    end

    // Calculate latency value for selected transaction (combinational)
    always_comb begin
        w_selected_latency_value = '0;

        if (w_has_latency_event) begin
            if (IS_READ) begin
                w_selected_latency_value = r_trans_table_local[w_selected_latency_idx].data_timestamp -
                                            r_trans_table_local[w_selected_latency_idx].addr_timestamp;
            end else begin
                w_selected_latency_value = r_trans_table_local[w_selected_latency_idx].resp_timestamp -
                                            r_trans_table_local[w_selected_latency_idx].addr_timestamp;
            end
        end
    end

    // Performance packet state and selection (combinational)
    always_comb begin
        w_next_perf_report_state = 3'h0;
        w_generate_perf_packet_completed = 1'b0;
        w_generate_perf_packet_errors = 1'b0;

        if (ENABLE_PERF_PACKETS && cfg_perf_enable && !monbus_valid && w_fifo_rd_valid == 0) begin
            case (r_perf_report_state)
                3'h0: begin // ADDR_LATENCY
                    w_next_perf_report_state = 3'h1;
                end
                3'h1: begin // DATA_LATENCY
                    w_next_perf_report_state = 3'h2;
                end
                3'h2: begin // TOTAL_LATENCY
                    w_next_perf_report_state = 3'h3;
                end
                3'h3: begin // COMPLETED_COUNT
                    w_next_perf_report_state = 3'h4;
                    if (r_perf_completed_count > 0) begin
                        w_generate_perf_packet_completed = 1'b1;
                    end
                end
                3'h4: begin // ERROR_COUNT
                    w_next_perf_report_state = 3'h0;
                    if (r_perf_error_count > 0) begin
                        w_generate_perf_packet_errors = 1'b1;
                    end
                end
                default: w_next_perf_report_state = 3'h0;
            endcase
        end
    end

    // Event reporting logic - sequential logic only
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            // Reset local table and reporting state
            r_trans_table_local <= '{default: '0};
            monbus_valid <= 1'b0;
            r_event_count <= '0;
            r_event_reported <= '0;

            // Reset performance counters
            r_perf_completed_count <= '0;
            r_perf_error_count <= '0;

            // Reset threshold flags
            r_active_threshold_crossed <= 1'b0;
            r_latency_threshold_crossed <= 1'b0;

            // Initialize packet construction registers
            r_packet_type <= PktTypeError;
            r_event_code <= EVT_NONE;
            r_event_data <= '0;
            r_event_channel <= '0;

            // Initialize performance report state
            r_perf_report_state <= 3'h0;
        end else begin
            // Update local transaction table element by element to avoid width issues
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= trans_table[idx];
            end

            // Handle packet output
            if (monbus_valid && monbus_ready) begin
                monbus_valid <= 1'b0;
            end

            // Present next packet from FIFO
            if (!monbus_valid && w_fifo_rd_valid) begin
                monbus_valid <= 1'b1;
                r_packet_type <= w_fifo_rd_data.packet_type;
                r_event_code <= w_fifo_rd_data.event_code;
                r_event_data <= w_fifo_rd_data.data;
                r_event_channel <= w_fifo_rd_data.channel;
            end

            // Mark events as reported and update counters
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                // FIX-001: Clear event_reported flag when transaction becomes invalid
                // This allows the flag to be reused when the transaction slot is reused
                if (!r_trans_table_local[idx].valid) begin
                    r_event_reported[idx] <= 1'b0;
                end else if (w_events_to_mark[idx]) begin
                    r_event_reported[idx] <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                end

                // Update performance counters
                if (ENABLE_PERF_PACKETS) begin
                    if (w_error_events[idx]) begin
                        r_perf_error_count <= r_perf_error_count + 1'b1;
                    end
                    if (w_completion_events[idx]) begin
                        r_perf_completed_count <= r_perf_completed_count + 1'b1;
                    end
                end
            end

            // Generate threshold packets if enabled
            if (cfg_threshold_enable) begin
                // Active transaction count threshold
                if (w_active_threshold_detection) begin
                    monbus_valid <= 1'b1;
                    r_packet_type <= PktTypeThreshold;
                    r_event_code <= AXI_THRESH_ACTIVE_COUNT;
                    r_event_data <= {6'h0, {24'h0, w_active_count_current}};  // Zero-extend to 38 bits
                    r_event_channel <= '0;
                    r_active_threshold_crossed <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                /* verilator lint_off WIDTHEXPAND */
                end else if (({8'h0, w_active_count_current} <= active_trans_threshold)) begin
                /* verilator lint_on WIDTHEXPAND */
                    r_active_threshold_crossed <= 1'b0;
                end

                // Latency threshold
                if (w_has_latency_event && !monbus_valid && w_fifo_rd_valid == 0) begin
                    monbus_valid <= 1'b1;
                    r_packet_type <= PktTypeThreshold;
                    r_event_code <= AXI_THRESH_LATENCY;
                    r_event_data <= pad_address(w_selected_latency_value);
                    r_event_channel <= r_trans_table_local[w_selected_latency_idx].channel[5:0];
                    r_latency_threshold_crossed <= 1'b1;
                    r_event_count <= r_event_count + 1'b1;
                end
            end

            // Generate performance packets if enabled
            if (w_generate_perf_packet_completed) begin
                monbus_valid <= 1'b1;
                r_packet_type <= PktTypePerf;
                r_event_code <= AXI_PERF_COMPLETED_COUNT;
                r_event_data <= {6'h0, {16'h0, r_perf_completed_count}};  // Zero-extend to 38 bits
                r_event_channel <= '0;
            end

            if (w_generate_perf_packet_errors) begin
                monbus_valid <= 1'b1;
                r_packet_type <= PktTypePerf;
                r_event_code <= AXI_PERF_ERROR_COUNT;
                r_event_data <= {6'h0, {16'h0, r_perf_error_count}};     // Zero-extend to 38 bits
                r_event_channel <= '0;
            end

            // Update performance report state
            r_perf_report_state <= w_next_perf_report_state;
        end
    )


    // Construct the 64-bit monitor bus packet - UPDATED for modern monitor_pkg format
    always_comb begin
        // MODERN 64-bit packet format from monitor_pkg.sv:
        // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
        // - protocol:    3 bits  [59:57] (AXI/AXIS/APB/ARB/CORE)
        // - event_code:  4 bits  [56:53] (specific error or event code)
        // - channel_id:  6 bits  [52:47] (channel ID and AXI ID)
        // - unit_id:     4 bits  [46:43] (subsystem identifier)
        // - agent_id:    8 bits  [42:35] (module identifier)
        // - event_data:  35 bits [34:0]  (event-specific data)

        monbus_packet[63:60] = r_packet_type;
        monbus_packet[59:57] = PROTOCOL_AXI;        // Always AXI protocol for this monitor (3 bits)
        monbus_packet[56:53] = r_event_code;
        monbus_packet[52:47] = r_event_channel;
        monbus_packet[46:43] = UNIT_ID[3:0];        // 4-bit Unit ID
        monbus_packet[42:35] = AGENT_ID[7:0];       // 8-bit Agent ID

        // Event data field (35 bits in modern format)
        monbus_packet[34:0] = r_event_data[34:0];
    end

endmodule : axi_monitor_reporter
