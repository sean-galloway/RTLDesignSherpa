// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_monitor
// Purpose: Apb Monitor module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * APB Monitor - Configurable Performance, Debug and Error Monitoring
 *
 * This module monitors APB transactions via cmd/rsp interfaces for errors,
 * performance metrics, and debug events. It integrates with the monitor bus
 * system and supports configurable event reporting.
 *
 * Designed to attach to the cmd/rsp interfaces which are timing-convenient
 * proxies for the actual APB signals.
 */

`include "reset_defs.svh"
module apb_monitor
    import monitor_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int UNIT_ID             = 1,     // 4-bit Unit ID
    parameter int AGENT_ID            = 10,    // 8-bit Agent ID
    parameter int MAX_TRANSACTIONS    = 4,     // APB is typically single outstanding
    parameter int MONITOR_FIFO_DEPTH  = 8,    // Monitor packet FIFO depth

    // Short params
    parameter int AW                  = ADDR_WIDTH,
    parameter int DW                  = DATA_WIDTH,
    parameter int SW                  = DW/8
)
(
    // Clock and Reset (aclk domain - matches cmd/rsp interfaces)
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command Interface Monitoring (aclk domain)
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic                     cmd_pwrite,
    input  logic [AW-1:0]            cmd_paddr,
    input  logic [DW-1:0]            cmd_pwdata,
    input  logic [SW-1:0]            cmd_pstrb,
    input  logic [2:0]               cmd_pprot,

    // Response Interface Monitoring (aclk domain)
    input  logic                     rsp_valid,
    input  logic                     rsp_ready,
    input  logic [DW-1:0]            rsp_prdata,
    input  logic                     rsp_pslverr,

    // Configuration - Error Detection
    input  logic                     cfg_error_enable,        // Enable error event packets
    input  logic                     cfg_timeout_enable,      // Enable timeout event packets
    input  logic                     cfg_protocol_enable,     // Enable protocol violation detection
    input  logic                     cfg_slverr_enable,       // Enable slave error detection

    // Configuration - Performance Monitoring
    input  logic                     cfg_perf_enable,         // Enable performance packets
    input  logic                     cfg_latency_enable,      // Enable latency tracking
    input  logic                     cfg_throughput_enable,   // Enable throughput tracking

    // Configuration - Debug
    input  logic                     cfg_debug_enable,        // Enable debug packets
    input  logic                     cfg_trans_debug_enable,  // Enable transaction debug
    input  logic [3:0]               cfg_debug_level,         // Debug verbosity level

    // Configuration - Thresholds and Timeouts
    input  logic [15:0]              cfg_cmd_timeout_cnt,     // Command timeout (cycles)
    input  logic [15:0]              cfg_rsp_timeout_cnt,     // Response timeout (cycles)
    input  logic [31:0]              cfg_latency_threshold,   // Latency threshold (cycles)
    input  logic [15:0]              cfg_throughput_threshold, // Throughput threshold

    // Consolidated 64-bit event packet interface (monitor bus)
    output logic                     monbus_valid,            // Monitor bus valid
    input  logic                     monbus_ready,            // Monitor bus ready
    output logic [63:0]              monbus_packet,           // Consolidated monitor packet

    // Status outputs
    output logic [7:0]               active_count,            // Number of active transactions
    output logic [15:0]              error_count,             // Total error count
    output logic [31:0]              transaction_count        // Total transaction count
);

    // -------------------------------------------------------------------------
    // Internal Signals
    // -------------------------------------------------------------------------

    // Transaction tracking
    bus_transaction_t r_trans_table[MAX_TRANSACTIONS];
    logic [7:0] r_active_count;
    logic [15:0] r_error_count;
    logic [31:0] r_transaction_count;

    // Transaction state tracking
    typedef enum logic [1:0] {
        CMD_RSP_IDLE     = 2'b00,  // No active transaction
        CMD_RSP_CMD_SENT = 2'b01,  // Command sent, waiting for response
        CMD_RSP_COMPLETE = 2'b10   // Transaction completed
    } cmd_rsp_state_t;

    cmd_rsp_state_t r_trans_state;
    cmd_rsp_state_t w_next_trans_state;
    logic w_state_change;

    // Timing tracking
    logic [31:0] r_timestamp;
    logic [31:0] r_cmd_start_time;
    logic [15:0] r_cmd_timeout_timer;
    logic [15:0] r_rsp_timeout_timer;

    // Transaction management
    logic [MAX_TRANSACTIONS-1:0] w_free_slot;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_free_idx;
    logic w_has_free_slot;
    logic [MAX_TRANSACTIONS-1:0] w_active_trans;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_active_idx;
    logic w_has_active_trans;
    logic [MAX_TRANSACTIONS-1:0] w_completed_trans;

    // Command/Response handshake detection
    logic w_cmd_handshake;
    logic w_rsp_handshake;

    // Error detection
    logic w_cmd_timeout;
    logic w_rsp_timeout;
    logic w_protocol_violation;
    logic w_latency_threshold_exceeded;

    // Performance metrics
    logic [31:0] w_current_latency;
    logic [15:0] r_throughput_counter;
    logic [31:0] r_throughput_timer;

    // Event generation
    logic w_generate_error_event;
    logic w_generate_timeout_event;
    logic w_generate_perf_event;
    logic w_generate_debug_event;
    logic w_generate_completion_event;
    apb_error_code_t w_error_event_code;
    apb_timeout_code_t w_timeout_event_code;

    // Monitor packet FIFO
    typedef struct packed {
        logic [3:0]  packet_type;
        logic [3:0]  event_code;
        logic [31:0] event_data;
        logic [7:0]  aux_data;
    } monitor_entry_t;

    logic w_fifo_wr_valid;
    logic w_fifo_wr_ready;
    monitor_entry_t w_fifo_wr_data;
    logic w_fifo_rd_valid;
    logic w_fifo_rd_ready;
    monitor_entry_t w_fifo_rd_data;
    logic [7:0] w_fifo_count; // Connect unused count port

    // -------------------------------------------------------------------------
    // Assign Outputs
    // -------------------------------------------------------------------------
    assign active_count = r_active_count;
    assign error_count = r_error_count;
    assign transaction_count = r_transaction_count;

    // -------------------------------------------------------------------------
    // Handshake Detection
    // -------------------------------------------------------------------------
    assign w_cmd_handshake = cmd_valid && cmd_ready;
    assign w_rsp_handshake = rsp_valid && rsp_ready;

    // -------------------------------------------------------------------------
    // Timestamp Counter
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            r_timestamp <= '0;
        end else begin
            r_timestamp <= r_timestamp + 1'b1;
        end
    )


    // -------------------------------------------------------------------------
    // Transaction State Machine
    // -------------------------------------------------------------------------
    always_comb begin
        w_next_trans_state = r_trans_state;

        case (r_trans_state)
            CMD_RSP_IDLE: begin
                if (w_cmd_handshake) begin
                    w_next_trans_state = CMD_RSP_CMD_SENT;
                end
            end

            CMD_RSP_CMD_SENT: begin
                if (w_rsp_handshake) begin
                    w_next_trans_state = CMD_RSP_COMPLETE;
                end
            end

            CMD_RSP_COMPLETE: begin
                w_next_trans_state = CMD_RSP_IDLE;
            end

            default: begin
                w_next_trans_state = CMD_RSP_IDLE;
            end
        endcase
    end

    assign w_state_change = (w_next_trans_state != r_trans_state);

    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            r_trans_state <= CMD_RSP_IDLE;
        end else begin
            r_trans_state <= w_next_trans_state;
        end
    )


    // -------------------------------------------------------------------------
    // Transaction Table Management
    // -------------------------------------------------------------------------

    // Find free slot
    always_comb begin
        w_free_slot = '0;
        w_free_idx = '0;
        w_has_free_slot = 1'b0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (!r_trans_table[i].valid && !w_has_free_slot) begin
                w_free_slot[i] = 1'b1;
                w_free_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                w_has_free_slot = 1'b1;
            end
        end
    end

    // Find active transaction
    always_comb begin
        w_active_trans = '0;
        w_active_idx = '0;
        w_has_active_trans = 1'b0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (r_trans_table[i].valid &&
                (r_trans_table[i].state == TRANS_ADDR_PHASE ||
                    r_trans_table[i].state == TRANS_DATA_PHASE) &&
                !w_has_active_trans) begin
                w_active_trans[i] = 1'b1;
                w_active_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                w_has_active_trans = 1'b1;
            end
        end
    end

    // Find completed transactions to clean up
    always_comb begin
        w_completed_trans = '0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (r_trans_table[i].valid &&
                (r_trans_table[i].state == TRANS_COMPLETE ||
                    r_trans_table[i].state == TRANS_ERROR) &&
                r_trans_table[i].event_reported) begin
                w_completed_trans[i] = 1'b1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Transaction Lifecycle Management
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                r_trans_table[i] <= '0;
            end
            r_active_count <= '0;
            r_transaction_count <= '0;
            r_cmd_start_time <= '0;
        end else begin

            // Command handshake - start new transaction
            if (w_cmd_handshake && w_has_free_slot) begin
                r_trans_table[w_free_idx].valid <= 1'b1;
                // Protocol is handled at packet construction time
                r_trans_table[w_free_idx].state <= TRANS_ADDR_PHASE;
                r_trans_table[w_free_idx].addr <= {{(64-AW){1'b0}}, cmd_paddr};
                r_trans_table[w_free_idx].burst <= {{1'b0}, cmd_pwrite};
                // APB-specific fields stored in burst and channel fields
                r_trans_table[w_free_idx].channel <= {cmd_pprot, cmd_pstrb[2:0]};
                r_trans_table[w_free_idx].cmd_received <= 1'b1;
                r_trans_table[w_free_idx].data_started <= cmd_pwrite; // For writes, data is with command
                r_trans_table[w_free_idx].addr_timestamp <= r_timestamp;
                r_trans_table[w_free_idx].event_code <= '0;
                r_trans_table[w_free_idx].event_reported <= 1'b0;
                r_trans_table[w_free_idx].addr_timer <= '0;
                r_trans_table[w_free_idx].resp_timer <= '0;

                r_active_count <= r_active_count + 1'b1;
                r_cmd_start_time <= r_timestamp;

                // Transition to data phase immediately for APB
                r_trans_table[w_free_idx].state <= TRANS_DATA_PHASE;
                r_trans_table[w_free_idx].data_timestamp <= r_timestamp;
            end

            // Response handshake - complete transaction
            if (w_rsp_handshake && w_has_active_trans) begin
                r_trans_table[w_active_idx].data_completed <= 1'b1;
                r_trans_table[w_active_idx].resp_received <= 1'b1;
                r_trans_table[w_active_idx].resp_timestamp <= r_timestamp;
                // APB slave error stored in channel field MSB
                if (rsp_pslverr) r_trans_table[w_active_idx].channel[5] <= 1'b1;

                if (rsp_pslverr && cfg_slverr_enable) begin
                    r_trans_table[w_active_idx].state <= TRANS_ERROR;
                    r_trans_table[w_active_idx].event_code <= APB_ERR_PSLVERR;
                    r_error_count <= r_error_count + 1'b1;
                end else begin
                    r_trans_table[w_active_idx].state <= TRANS_COMPLETE;
                    r_trans_table[w_active_idx].event_code <= APB_COMPL_TRANS_COMPLETE;
                end

                r_transaction_count <= r_transaction_count + 1'b1;
            end

            // Clean up completed transactions
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (w_completed_trans[i]) begin
                    r_trans_table[i].valid <= 1'b0;
                    r_active_count <= r_active_count - 1'b1;
                end
            end
        end
    )


    // -------------------------------------------------------------------------
    // Timeout Detection
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            r_cmd_timeout_timer <= '0;
            r_rsp_timeout_timer <= '0;
        end else begin
            // Command timeout - waiting for cmd handshake
            if (r_trans_state == CMD_RSP_IDLE && cmd_valid && !cmd_ready) begin
                r_cmd_timeout_timer <= r_cmd_timeout_timer + 1'b1;
            end else begin
                r_cmd_timeout_timer <= '0;
            end

            // Response timeout - waiting for rsp handshake
            if (r_trans_state == CMD_RSP_CMD_SENT && (!rsp_valid || !rsp_ready)) begin
                r_rsp_timeout_timer <= r_rsp_timeout_timer + 1'b1;
            end else begin
                r_rsp_timeout_timer <= '0;
            end
        end
    )


    // Timeout detection
    assign w_cmd_timeout = cfg_timeout_enable &&
                            (r_cmd_timeout_timer >= cfg_cmd_timeout_cnt) &&
                            (r_cmd_timeout_timer != '0);

    assign w_rsp_timeout = cfg_timeout_enable &&
                            (r_rsp_timeout_timer >= cfg_rsp_timeout_cnt) &&
                            (r_rsp_timeout_timer != '0);

    // -------------------------------------------------------------------------
    // Error Detection
    // -------------------------------------------------------------------------
    always_comb begin
        w_protocol_violation = 1'b0;

        if (cfg_protocol_enable) begin
            // Detect protocol violations
            // Example: Response without command
            if (rsp_valid && r_trans_state == CMD_RSP_IDLE) begin
                w_protocol_violation = 1'b1;
            end
            // Example: Multiple commands without response
            if (cmd_valid && r_trans_state == CMD_RSP_CMD_SENT) begin
                w_protocol_violation = 1'b1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Performance Monitoring
    // -------------------------------------------------------------------------
    always_comb begin
        w_current_latency = '0;
        w_latency_threshold_exceeded = 1'b0;

        if (w_has_active_trans && r_trans_table[w_active_idx].valid) begin
            w_current_latency = r_timestamp - r_trans_table[w_active_idx].addr_timestamp;
            w_latency_threshold_exceeded = cfg_perf_enable && cfg_latency_enable &&
                                            (w_current_latency > cfg_latency_threshold);
        end
    end

    // Throughput tracking
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            r_throughput_counter <= '0;
            r_throughput_timer <= '0;
        end else begin
            r_throughput_timer <= r_throughput_timer + 1'b1;

            if (w_rsp_handshake) begin
                r_throughput_counter <= r_throughput_counter + 1'b1;
            end

            // Reset every 65536 cycles for throughput calculation
            if (r_throughput_timer[15:0] == 16'hFFFF) begin
                r_throughput_counter <= '0;
            end
        end
    )


    // -------------------------------------------------------------------------
    // Event Generation Logic
    // -------------------------------------------------------------------------
    always_comb begin
        w_generate_error_event = 1'b0;
        w_generate_timeout_event = 1'b0;
        w_generate_perf_event = 1'b0;
        w_generate_debug_event = 1'b0;
        w_generate_completion_event = 1'b0;
        w_error_event_code = APB_ERR_PSLVERR;
        w_timeout_event_code = APB_TIMEOUT_SETUP;

        // Error events
        if (cfg_error_enable) begin
            if (w_protocol_violation) begin
                w_generate_error_event = 1'b1;
                w_error_event_code = APB_ERR_SETUP_VIOLATION;
            end else if (rsp_pslverr && w_rsp_handshake && cfg_slverr_enable) begin
                w_generate_error_event = 1'b1;
                w_error_event_code = APB_ERR_PSLVERR;
            end
        end

        // Timeout events
        if (cfg_timeout_enable) begin
            if (w_cmd_timeout) begin
                w_generate_timeout_event = 1'b1;
                w_timeout_event_code = APB_TIMEOUT_SETUP;
            end else if (w_rsp_timeout) begin
                w_generate_timeout_event = 1'b1;
                w_timeout_event_code = APB_TIMEOUT_ACCESS;
            end
        end

        // Performance events
        if (cfg_perf_enable && w_latency_threshold_exceeded) begin
            w_generate_perf_event = 1'b1;
        end

        // Debug events
        if (cfg_debug_enable) begin
            if (cfg_trans_debug_enable && w_state_change) begin
                w_generate_debug_event = 1'b1;
            end
        end

        // Completion events
        if (w_rsp_handshake && !rsp_pslverr) begin
            w_generate_completion_event = 1'b1;
        end
    end

    // -------------------------------------------------------------------------
    // Monitor Packet FIFO
    // -------------------------------------------------------------------------
    gaxi_fifo_sync #(
        .REGISTERED      (1),
        .DATA_WIDTH      ($bits(monitor_entry_t)),
        .DEPTH           (MONITOR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME   ("APB_MONITOR_FIFO")
    ) monitor_fifo (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_fifo_wr_valid),
        .wr_ready      (w_fifo_wr_ready),
        .wr_data       (w_fifo_wr_data),
        .rd_ready      (w_fifo_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid      (w_fifo_rd_valid),
        .rd_data       (w_fifo_rd_data)
    );

    // FIFO write logic - priority: Error > Timeout > Performance > Debug > Completion
    always_comb begin
        w_fifo_wr_valid = 1'b0;
        w_fifo_wr_data = '0;

        if (w_generate_error_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeError;
            w_fifo_wr_data.event_code = w_error_event_code;
            w_fifo_wr_data.event_data = cmd_paddr;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end else if (w_generate_timeout_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeTimeout;
            w_fifo_wr_data.event_code = w_timeout_event_code;
            w_fifo_wr_data.event_data = w_has_active_trans ? r_trans_table[w_active_idx].addr[31:0] : cmd_paddr;
            w_fifo_wr_data.aux_data = {r_cmd_timeout_timer[7:0]};
        end else if (w_generate_perf_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypePerf;
            w_fifo_wr_data.event_code = cmd_pwrite ? APB_PERF_WRITE_LATENCY : APB_PERF_READ_LATENCY;
            w_fifo_wr_data.event_data = w_current_latency;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end else if (w_generate_debug_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeDebug;
            w_fifo_wr_data.event_code = APB_DEBUG_SETUP_PHASE;
            w_fifo_wr_data.event_data = {28'h0, r_trans_state, w_next_trans_state};
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end else if (w_generate_completion_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeCompletion;
            w_fifo_wr_data.event_code = APB_COMPL_TRANS_COMPLETE;
            w_fifo_wr_data.event_data = cmd_paddr;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end
    end

    // Mark events as reported when they're written to FIFO
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            // Reset handled in transaction management
        end else begin
            // Mark events as reported when packets are generated
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (r_trans_table[i].valid &&
                    (r_trans_table[i].state == TRANS_COMPLETE || r_trans_table[i].state == TRANS_ERROR) &&
                    !r_trans_table[i].event_reported && w_fifo_wr_valid && w_fifo_wr_ready) begin
                    r_trans_table[i].event_reported <= 1'b1;
                end
            end
        end
    )


    // -------------------------------------------------------------------------
    // Monitor Bus Packet Construction and Skid Buffer Output
    // -------------------------------------------------------------------------

    // Monitor bus packet construction and buffering
    logic                w_monbus_pkt_valid;
    logic                w_monbus_pkt_ready;
    logic [63:0]         w_monbus_pkt_data;

    // Construct monitor packet when FIFO has data
    assign w_monbus_pkt_valid = w_fifo_rd_valid;
    assign w_fifo_rd_ready = w_monbus_pkt_ready;

    // Construct 64-bit monitor packet according to modern monitor_pkg format
    assign w_monbus_pkt_data[63:60] = w_fifo_rd_data.packet_type;    // packet_type
    assign w_monbus_pkt_data[59:57] = PROTOCOL_APB;                  // protocol (3-bit, modern format)
    assign w_monbus_pkt_data[56:53] = w_fifo_rd_data.event_code;     // event_code (shifted due to 3-bit protocol)
    assign w_monbus_pkt_data[52:47] = 6'h0;                          // channel_id (not used for APB, shifted)
    assign w_monbus_pkt_data[46:43] = UNIT_ID[3:0];                  // unit_id (shifted)
    assign w_monbus_pkt_data[42:35] = AGENT_ID[7:0];                 // agent_id (shifted)
    assign w_monbus_pkt_data[34:3]  = w_fifo_rd_data.event_data;     // event_data[31:0] (shifted)
    assign w_monbus_pkt_data[2:0]   = w_fifo_rd_data.aux_data[2:0];  // aux_data[2:0] (reduced due to shifts)

    // Monitor bus output skid buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH    (64),
        .DEPTH         (2),
        .INSTANCE_NAME ("APB_MONITOR_MONBUS_SKB")
    ) monbus_skid_buffer (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_monbus_pkt_valid),
        .wr_ready      (w_monbus_pkt_ready),
        .wr_data       (w_monbus_pkt_data),
        .rd_valid      (monbus_valid),
        .rd_ready      (monbus_ready),
        .rd_data       (monbus_packet),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        .rd_count      ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : apb_monitor
