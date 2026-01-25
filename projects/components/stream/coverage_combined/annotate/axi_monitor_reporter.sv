//      // verilator_coverage annotation
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
            import monitor_common_pkg::*;
            import monitor_amba4_pkg::*;
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
 002282     input  logic                     aclk,
%000002     input  logic                     aresetn,
        
            // Transaction table (read-only access) - Fixed: Use unpacked array
            input  bus_transaction_t         trans_table[MAX_TRANSACTIONS],
        
            // Timeout detection flags from timeout module
%000000     input  logic [MAX_TRANSACTIONS-1:0] timeout_detected,
        
            // Configuration enables for different packet types
%000000     input  logic                     cfg_error_enable,    // Enable error packets
%000000     input  logic                     cfg_compl_enable,    // Enable completion packets
%000000     input  logic                     cfg_threshold_enable,// Enable threshold packets
%000000     input  logic                     cfg_timeout_enable,  // Enable timeout packets
%000000     input  logic                     cfg_perf_enable,     // Enable performance packets
%000000     input  logic                     cfg_debug_enable,    // Enable debug packets
        
            // Interrupt bus output interface
%000002     input  logic                     monbus_ready,  // Downstream ready
%000000     output logic                     monbus_valid,  // Interrupt valid
%000000     output logic [63:0]              monbus_packet, // Consolidated interrupt packet
        
            // Statistics output
%000000     output logic [15:0]              event_count,    // Total event count
        
            // Performance metrics (only used when ENABLE_PERF_PACKETS=1)
%000000     output logic [15:0]              perf_completed_count, // Number of completed transactions
%000000     output logic [15:0]              perf_error_count,     // Number of error transactions
        
            // Performance metric thresholds
%000000     input  logic [15:0]              active_trans_threshold,
%000000     input  logic [31:0]              latency_threshold,
        
            // Event reported feedback to trans_mgr (FIX-001)
%000000     output logic [MAX_TRANSACTIONS-1:0] event_reported_flags
        );
        
            // Local version of transaction table for processing (flopped)
            bus_transaction_t r_trans_table_local[MAX_TRANSACTIONS];
        
            // Flag to track if event has been reported for each transaction (flopped)
%000000     logic [MAX_TRANSACTIONS-1:0] r_event_reported;
            // FIX-001: Connect internal flag to output port for trans_mgr feedback
            assign event_reported_flags = r_event_reported;
        
            // Localparams for address width handling
            localparam int ADDR_PAD_WIDTH = (ADDR_WIDTH <= 38) ? (38 - ADDR_WIDTH) : 0;
            localparam bit ADDR_NEEDS_TRUNCATE = (ADDR_WIDTH > 38);
        
            // Helper function to safely pad/truncate address for packet data field
%000000     function automatic logic [37:0] pad_address(input logic [ADDR_WIDTH-1:0] addr);
%000000         if (ADDR_NEEDS_TRUNCATE) begin
%000000             return addr[37:0];
%000000         end else begin
%000000             return {{ADDR_PAD_WIDTH{1'b0}}, addr};
                end
            endfunction
        
            // Threshold crossing flags (flopped)
%000000     logic r_active_threshold_crossed;
%000000     logic r_latency_threshold_crossed;
        
            // Event count (flopped)
%000000     logic [15:0] r_event_count;
            assign event_count = r_event_count;
        
            // Performance metrics counters (flopped)
%000000     logic [15:0] r_perf_completed_count;
%000000     logic [15:0] r_perf_error_count;
        
            // Assign performance metrics outputs
            assign perf_completed_count = r_perf_completed_count;
            assign perf_error_count = r_perf_error_count;
        
            // Performance report state machine (flopped)
%000000     logic [2:0] r_perf_report_state;
        
            // Interrupt FIFO entry type - Updated with new packet format
            typedef struct packed {
                logic [3:0]            packet_type;  // Packet type (updated bit allocation)
                logic [3:0]            event_code;   // Event code or metric type
                logic [5:0]            channel;      // Channel information
                logic [37:0]           data;         // Address or metric value (updated to 38 bits)
            } monbus_entry_t;
        
            // FIFO signals (combinational)
%000000     logic                                 w_fifo_wr_valid;
%000002     logic                                 w_fifo_wr_ready;
%000000     monbus_entry_t                        w_fifo_wr_data;
%000004     logic                                 w_fifo_rd_valid;
%000000     logic                                 w_fifo_rd_ready;
%000000     monbus_entry_t                        w_fifo_rd_data;
%000000     logic [$clog2(INTR_FIFO_DEPTH):0]     w_fifo_count;  // Proper width calculation
        
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
%000000     logic [3:0]  r_packet_type;
%000000     logic [3:0]  r_event_code;
%000000     logic [37:0] r_event_data;  // Updated to 38 bits to match new packet format
%000000     logic [5:0]  r_event_channel;
        
            // Event detection signals - One for each type of event to report (combinational)
%000000     logic [MAX_TRANSACTIONS-1:0] w_error_events_detected;
%000000     logic [MAX_TRANSACTIONS-1:0] w_timeout_events_detected;
%000000     logic [MAX_TRANSACTIONS-1:0] w_completion_events_detected;
%000000     logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_error_idx;
%000000     logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_timeout_idx;
%000000     logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_completion_idx;
%000000     logic w_has_error_event;
%000000     logic w_has_timeout_event;
%000000     logic w_has_completion_event;
        
            // Event marking signals (combinational)
%000000     logic [MAX_TRANSACTIONS-1:0] w_events_to_mark;
%000000     logic [MAX_TRANSACTIONS-1:0] w_error_events;
%000000     logic [MAX_TRANSACTIONS-1:0] w_completion_events;
        
            // Active transaction count for threshold detection (combinational)
%000000     logic [7:0] w_active_count_current;
%000000     logic w_active_threshold_detection;
        
            // Latency threshold detection signals (combinational)
%000000     logic [MAX_TRANSACTIONS-1:0] w_latency_threshold_events;
%000000     logic [$clog2(MAX_TRANSACTIONS)-1:0] w_selected_latency_idx;
%000000     logic w_has_latency_event;
        
            // Pre-declare latency calculation variables to avoid latch inference
%000000     logic [31:0] w_total_latency;
%000000     logic [31:0] w_selected_latency_value;
        
            // Performance packet state and selection (combinational)
%000000     logic w_generate_perf_packet_completed;
%000000     logic w_generate_perf_packet_errors;
%000000     logic [2:0] w_next_perf_report_state;
        
            // Error event detection - Updated to use unified event codes
 007896     always_comb begin
 007896         w_error_events_detected = '0;
 007896         w_selected_error_idx = '0;
 007896         w_has_error_event = 1'b0;
        
                // Scan for error events (exclude timeouts, include orphans)
                // Use timeout_detected signal to distinguish errors from timeouts
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (r_trans_table_local[idx].valid && !r_event_reported[idx] && cfg_error_enable &&
                            ((r_trans_table_local[idx].state == TRANS_ERROR && !timeout_detected[idx]) ||  // Error but not timeout
%000000                      (r_trans_table_local[idx].state == TRANS_ORPHANED))) begin  // Orphaned transaction
%000000                 w_error_events_detected[idx] = 1'b1;
                    end
                end
        
                // Priority encoder to select the first detected error
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (w_error_events_detected[idx] && !w_has_error_event) begin
                        /* verilator lint_off WIDTHTRUNC */
%000000                 w_selected_error_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                        /* verilator lint_on WIDTHTRUNC */
%000000                 w_has_error_event = 1'b1;
                    end
                end
            end
        
            // Timeout event detection - Updated to use unified event codes
 007896     always_comb begin
 007896         w_timeout_events_detected = '0;
 007896         w_selected_timeout_idx = '0;
 007896         w_has_timeout_event = 1'b0;
        
                // Scan for timeout events
                // Use timeout_detected signal from timeout module
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
                        r_trans_table_local[idx].state == TRANS_ERROR && cfg_timeout_enable &&
%000000                 timeout_detected[idx]) begin  // Is a timeout
%000000                 w_timeout_events_detected[idx] = 1'b1;
                    end
                end
        
                // Priority encoder to select the first detected timeout
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (w_timeout_events_detected[idx] && !w_has_timeout_event) begin
                        /* verilator lint_off WIDTHTRUNC */
%000000                 w_selected_timeout_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                        /* verilator lint_on WIDTHTRUNC */
%000000                 w_has_timeout_event = 1'b1;
                    end
                end
            end
        
            // Completion event detection
 007896     always_comb begin
 007896         w_completion_events_detected = '0;
 007896         w_selected_completion_idx = '0;
 007896         w_has_completion_event = 1'b0;
        
                // Scan for completion events
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (r_trans_table_local[idx].valid && !r_event_reported[idx] &&
%000000                 r_trans_table_local[idx].state == TRANS_COMPLETE && cfg_compl_enable) begin
%000000                 w_completion_events_detected[idx] = 1'b1;
                    end
                end
        
                // Priority encoder to select the first detected completion
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000             if (w_completion_events_detected[idx] && !w_has_completion_event) begin
                        /* verilator lint_off WIDTHTRUNC */
%000000                 w_selected_completion_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                        /* verilator lint_on WIDTHTRUNC */
%000000                 w_has_completion_event = 1'b1;
                    end
                end
            end
        
            // FIFO write interface - combines all event detections - Updated to use unified event codes
 007896     always_comb begin
 007896         w_fifo_wr_valid = 1'b0;
 007896         w_fifo_wr_data = '{default: '0};
        
                // Priority: Error > Timeout > Completion
%000000         if (w_has_error_event) begin
%000000             w_fifo_wr_valid = 1'b1;
%000000             w_fifo_wr_data.packet_type = PktTypeError;
%000000             w_fifo_wr_data.event_code = r_trans_table_local[w_selected_error_idx].event_code.raw_code;
%000000             w_fifo_wr_data.channel = r_trans_table_local[w_selected_error_idx].channel[5:0];
%000000             w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_error_idx].addr);
%000000         end else if (w_has_timeout_event) begin
%000000             w_fifo_wr_valid = 1'b1;
%000000             w_fifo_wr_data.packet_type = PktTypeTimeout;
%000000             w_fifo_wr_data.event_code = r_trans_table_local[w_selected_timeout_idx].event_code.raw_code;
%000000             w_fifo_wr_data.channel = r_trans_table_local[w_selected_timeout_idx].channel[5:0];
%000000             w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_timeout_idx].addr);
%000000         end else if (w_has_completion_event) begin
%000000             w_fifo_wr_valid = 1'b1;
%000000             w_fifo_wr_data.packet_type = PktTypeCompletion;
%000000             w_fifo_wr_data.event_code = EVT_TRANS_COMPLETE;
%000000             w_fifo_wr_data.channel = r_trans_table_local[w_selected_completion_idx].channel[5:0];
%000000             w_fifo_wr_data.data = pad_address(r_trans_table_local[w_selected_completion_idx].addr);
                end
            end
        
            // FIFO read interface and event processing
            assign w_fifo_rd_ready = monbus_ready && monbus_valid;
        
            // Detect events that need to be marked as reported
 007896     always_comb begin
 007896         w_events_to_mark = '0;
 007896         w_error_events = '0;
 007896         w_completion_events = '0;
        
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
 007601             if (r_trans_table_local[idx].valid) begin
%000000                 if ((r_trans_table_local[idx].state == TRANS_ERROR ||
                                r_trans_table_local[idx].state == TRANS_ORPHANED ||
                                r_trans_table_local[idx].state == TRANS_COMPLETE) &&
%000000                         !r_event_reported[idx] && w_fifo_wr_valid && w_fifo_wr_ready) begin
        
%000000                     w_events_to_mark[idx] = 1'b1;
        
%000000                     if (r_trans_table_local[idx].state == TRANS_ERROR ||
%000000                         r_trans_table_local[idx].state == TRANS_ORPHANED) begin
%000000                         w_error_events[idx] = 1'b1;
%000000                     end else if (r_trans_table_local[idx].state == TRANS_COMPLETE) begin
%000000                         w_completion_events[idx] = 1'b1;
                            end
                        end
                    end
                end
            end
        
            // Active transaction count calculation
 007896     always_comb begin
 007896         w_active_count_current = '0;
        
 007896         for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
 000053             if (r_trans_table_local[idx].valid &&
                        r_trans_table_local[idx].state != TRANS_COMPLETE &&
 000053                 r_trans_table_local[idx].state != TRANS_ERROR) begin
 000053                 w_active_count_current = w_active_count_current + 1'b1;
                    end
                end
        
                /* verilator lint_off WIDTHEXPAND */
 007896         w_active_threshold_detection = (({8'h0, w_active_count_current} > active_trans_threshold) &&
 007896                                         !r_active_threshold_crossed &&
 007896                                         !monbus_valid &&
 007896                                         (w_fifo_rd_valid == 0));
                /* verilator lint_on WIDTHEXPAND */
            end
        
            // Latency threshold detection
 007896     always_comb begin
 007896         w_latency_threshold_events = '0;
 007896         w_selected_latency_idx = '0;
 007896         w_has_latency_event = 1'b0;
 007896         w_total_latency = '0;
        
%000000         if (ENABLE_PERF_PACKETS && cfg_perf_enable && cfg_threshold_enable) begin
%000000             for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000                 if (r_trans_table_local[idx].valid && r_trans_table_local[idx].state == TRANS_COMPLETE) begin
%000000                     if (IS_READ) begin
%000000                         w_total_latency = r_trans_table_local[idx].data_timestamp - r_trans_table_local[idx].addr_timestamp;
%000000                     end else begin
%000000                         w_total_latency = r_trans_table_local[idx].resp_timestamp - r_trans_table_local[idx].addr_timestamp;
                            end
        
%000000                     if (w_total_latency > latency_threshold && !r_latency_threshold_crossed) begin
%000000                         w_latency_threshold_events[idx] = 1'b1;
                            end
                        end
                    end
        
                    // Priority encoder to select the first latency threshold event
%000000             for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
%000000                 if (w_latency_threshold_events[idx] && !w_has_latency_event) begin
                            /* verilator lint_off WIDTHTRUNC */
%000000                     w_selected_latency_idx = idx[$clog2(MAX_TRANSACTIONS)-1:0];
                            /* verilator lint_on WIDTHTRUNC */
%000000                     w_has_latency_event = 1'b1;
                        end
                    end
                end
            end
        
            // Calculate latency value for selected transaction (combinational)
 007896     always_comb begin
 007896         w_selected_latency_value = '0;
        
%000000         if (w_has_latency_event) begin
%000000             if (IS_READ) begin
%000000                 w_selected_latency_value = r_trans_table_local[w_selected_latency_idx].data_timestamp -
%000000                                             r_trans_table_local[w_selected_latency_idx].addr_timestamp;
%000000             end else begin
%000000                 w_selected_latency_value = r_trans_table_local[w_selected_latency_idx].resp_timestamp -
%000000                                             r_trans_table_local[w_selected_latency_idx].addr_timestamp;
                    end
                end
            end
        
            // Performance packet state and selection (combinational)
 007896     always_comb begin
 007896         w_next_perf_report_state = 3'h0;
 007896         w_generate_perf_packet_completed = 1'b0;
 007896         w_generate_perf_packet_errors = 1'b0;
        
%000000         if (ENABLE_PERF_PACKETS && cfg_perf_enable && !monbus_valid && w_fifo_rd_valid == 0) begin
%000000             case (r_perf_report_state)
%000000                 3'h0: begin // ADDR_LATENCY
%000000                     w_next_perf_report_state = 3'h1;
                        end
%000000                 3'h1: begin // DATA_LATENCY
%000000                     w_next_perf_report_state = 3'h2;
                        end
%000000                 3'h2: begin // TOTAL_LATENCY
%000000                     w_next_perf_report_state = 3'h3;
                        end
%000000                 3'h3: begin // COMPLETED_COUNT
%000000                     w_next_perf_report_state = 3'h4;
%000000                     if (r_perf_completed_count > 0) begin
%000000                         w_generate_perf_packet_completed = 1'b1;
                            end
                        end
%000000                 3'h4: begin // ERROR_COUNT
%000000                     w_next_perf_report_state = 3'h0;
%000000                     if (r_perf_error_count > 0) begin
%000000                         w_generate_perf_packet_errors = 1'b1;
                            end
                        end
%000000                 default: w_next_perf_report_state = 3'h0;
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
%000000     )
        
        
            // Construct the 64-bit monitor bus packet - UPDATED for modern monitor_pkg format
%000002     always_comb begin
                // MODERN 64-bit packet format from monitor_pkg.sv:
                // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
                // - protocol:    3 bits  [59:57] (AXI/AXIS/APB/ARB/CORE)
                // - event_code:  4 bits  [56:53] (specific error or event code)
                // - channel_id:  6 bits  [52:47] (channel ID and AXI ID)
                // - unit_id:     4 bits  [46:43] (subsystem identifier)
                // - agent_id:    8 bits  [42:35] (module identifier)
                // - event_data:  35 bits [34:0]  (event-specific data)
        
%000002         monbus_packet[63:60] = r_packet_type;
%000002         monbus_packet[59:57] = PROTOCOL_AXI;        // Always AXI protocol for this monitor (3 bits)
%000002         monbus_packet[56:53] = r_event_code;
%000002         monbus_packet[52:47] = r_event_channel;
%000002         monbus_packet[46:43] = UNIT_ID[3:0];        // 4-bit Unit ID
%000002         monbus_packet[42:35] = AGENT_ID[7:0];       // 8-bit Agent ID
        
                // Event data field (35 bits in modern format)
%000002         monbus_packet[34:0] = r_event_data[34:0];
            end
        
        endmodule : axi_monitor_reporter
        
