// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_monbus_common
// Purpose: Arbiter Monbus Common module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/*
================================================================================
Arbiter Monitor Bus Common - Silicon Debug Monitor (UPDATED FOR 3-BIT PROTOCOL)
================================================================================

This arbiter monitor provides comprehensive monitoring and debug capabilities
for both RR and WRR arbiters with optional ACK protocol support using the
updated PROTOCOL_ARB event definitions.

UPDATED FOR NEW MONITOR PACKAGE:
- Protocol field INCREASED to 3 bits [59:57] (was 2 bits [59:58])
- Event code at [56:53] (4 bits) (was [57:54])
- Channel ID at [52:47] (6 bits) (unchanged)
- Unit ID at [46:43] (4 bits) (unchanged)
- Agent ID at [42:35] (8 bits) (unchanged)
- Event data REDUCED to 35 bits [34:0] (was 36 bits [35:0])
- Updated ARB event code names to match monitor_pkg.sv

Monitor Events Generated:
1. ARB Error Events: Starvation, ACK timeout, protocol violations, etc.
2. ARB Timeout Events: Grant ACK timeout, request hold timeout, etc.
3. ARB Completion Events: Grant issued, ACK received, transactions complete
4. ARB Threshold Events: Latency, fairness, efficiency thresholds
5. ARB Performance Events: Throughput, efficiency, fairness metrics
6. ARB Debug Events: State changes, weight updates, queue status

Silicon Debug Features:
- Per-client ACK timeout tracking with configurable thresholds
- Protocol violation detection (spurious ACKs, overlapping grants)
- Fairness deviation monitoring for weighted arbiters
- Grant efficiency tracking (issued vs completed)
- Comprehensive state machine monitoring
- Credit system violation detection
- Request starvation detection with precise timing
*/

`include "reset_defs.svh"

module arbiter_monbus_common #(
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,                    // ACK enable parameter
    parameter int WEIGHTED_MODE = 0,
    /* verilator lint_off WIDTHTRUNC */
    parameter logic [7:0] MON_AGENT_ID = 8'h10,
    parameter logic [3:0] MON_UNIT_ID = 4'h0,
    /* verilator lint_on WIDTHTRUNC */
    parameter int MON_FIFO_DEPTH = 8,
    parameter int MON_FIFO_ALMOST_MARGIN = 1,
    parameter int FAIRNESS_REPORT_CYCLES = 256,
    parameter int MIN_GRANTS_FOR_FAIRNESS = 100,
    parameter int DEFAULT_ACK_TIMEOUT = 64,            // Default ACK timeout cycles

    // Calculated parameters
    parameter int MON_FIFO_COUNT_WIDTH = $clog2(MON_FIFO_DEPTH + 1),
    parameter int N = $clog2(CLIENTS),
    parameter int MFCW = MON_FIFO_COUNT_WIDTH,
    parameter int MAX_LEVELS = 16,
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    parameter int MTW = MAX_LEVELS_WIDTH,
    parameter int CXMTW = CLIENTS*MAX_LEVELS_WIDTH
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Arbiter interface - connect to any arbiter type
    input  logic [CXMTW-1:0]              cfg_max_thresh,    // Client Weights
    input  logic [CLIENTS-1:0]            request,           // Client requests
    input  logic                          grant_valid,       // Grant is valid this cycle
    input  logic [CLIENTS-1:0]            grant,             // One-hot grant vector
    input  logic [N-1:0]                  grant_id,          // Binary encoded grant ID
    input  logic [CLIENTS-1:0]            grant_ack,         // Grant ACK signals
    input  logic                          block_arb,         // Arbiter is blocked (optional)

    // Monitor bus configuration
    input  logic                          cfg_mon_enable,
    input  logic [15:0]                   cfg_mon_pkt_type_enable,
    input  logic [15:0]                   cfg_mon_latency_thresh,
    input  logic [15:0]                   cfg_mon_starvation_thresh,
    input  logic [15:0]                   cfg_mon_fairness_thresh,
    input  logic [15:0]                   cfg_mon_active_thresh,
    input  logic [15:0]                   cfg_mon_ack_timeout_thresh,   // ACK timeout threshold
    input  logic [15:0]                   cfg_mon_efficiency_thresh,    // Grant efficiency threshold
    input  logic [7:0]                    cfg_mon_sample_period,

    // Monitor bus output - 64-bit event packet interface
    output logic                          monbus_valid,
    input  logic                          monbus_ready,
    output logic [63:0]                   monbus_packet,

    // Enhanced debug outputs for silicon debug
    output logic [$clog2(MON_FIFO_DEPTH):0] debug_fifo_count,
    output logic [15:0]                     debug_packet_count,
    output logic [CLIENTS-1:0]              debug_ack_timeout,         // Per-client ACK timeout status
    output logic [15:0]                     debug_protocol_violations, // Protocol violation count
    output logic [15:0]                     debug_grant_efficiency,    // Grant efficiency percentage
    output logic [CLIENTS-1:0]              debug_client_starvation,   // Per-client starvation flags
    output logic [15:0]                     debug_fairness_deviation,  // Fairness deviation metric
    output logic [2:0]                      debug_monitor_state        // Monitor internal state
);

    // Import monitor package for event types and helper functions
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    import monitor_arbiter_pkg::*;
    import monitor_pkg::*;

    // =========================================================================
    // ALL WIRE AND SIGNAL DECLARATIONS - DECLARED FIRST BEFORE ANY USAGE
    // =========================================================================
    localparam int ACTIVE_COUNT_WIDTH = $clog2(CLIENTS+1);

    // Event detection combinational logic wires
    logic                           w_starvation_detected;
    logic [N-1:0]                   w_starvation_client;
    logic                           w_latency_threshold_detected;
    logic [N-1:0]                   w_latency_threshold_client;
    logic                           w_active_threshold_detected;
    logic [$clog2(CLIENTS+1)-1:0]   w_active_request_count;
    logic                           w_grant_event_detected;
    logic [N-1:0]                   w_grant_client_id;
    logic                           w_ack_timeout_event_detected;
    logic [N-1:0]                   w_ack_timeout_client;
    logic                           w_protocol_violation_detected;
    logic                           w_fairness_violation_detected;
    logic                           w_efficiency_threshold_detected;
    logic [15:0]                    w_current_efficiency;
    logic                           w_completion_event_detected;
    logic [N-1:0]                   w_completion_client;
    logic [34-ACTIVE_COUNT_WIDTH:0] w_evt_pad0;  // ✅ UPDATED: Padding to make exactly 35 bits total

    // Sample timing
    logic                            w_sample_event;

    // FIFO and packet management
    logic [63:0]                     w_event_packet;
    logic                            w_event_valid;
    logic                            w_fifo_wr_valid;
    logic                            w_fifo_wr_ready;
    logic                            w_fifo_rd_ready;
    logic                            w_fifo_rd_valid;
    logic                            w_fifo_write_transfer;
    logic                            w_fifo_read_transfer;
    logic [$clog2(MON_FIFO_DEPTH):0] w_fifo_count;
    logic [63:0]                     w_fifo_data_out;

    // Raw debug wires for packet fields - w_packet_* prefix
    logic [3:0]  w_packet_pkt_type;
    logic [2:0]  w_packet_protocol;  // ✅ CORRECT: 3 bits [59:57]
    logic [3:0]  w_packet_event_code;
    logic [5:0]  w_packet_channel_id;
    logic [3:0]  w_packet_unit_id;
    logic [7:0]  w_packet_agent_id;
    logic [34:0] w_packet_data;      // ✅ CORRECT: 35 bits [34:0]

    // Enum versions for human-readable waveforms - w_packet_enum_* prefix
    protocol_type_t         w_packet_enum_protocol;
    arb_error_code_t        w_packet_enum_arb_error;
    arb_timeout_code_t      w_packet_enum_arb_timeout;
    arb_completion_code_t   w_packet_enum_arb_completion;
    arb_threshold_code_t    w_packet_enum_arb_threshold;
    arb_performance_code_t  w_packet_enum_arb_performance;

    // Event priority and selection logic - w_packet_* prefix for consistency
    logic w_packet_starvation_pkt_en;
    logic w_packet_ack_timeout_pkt_en;
    logic w_packet_latency_thresh_pkt_en;
    logic w_packet_fairness_violation_pkt_en;
    logic w_packet_efficiency_thresh_pkt_en;
    logic w_packet_active_thresh_pkt_en;
    logic w_packet_completion_pkt_en;
    logic w_packet_grant_perf_pkt_en;

    // Debug enable mask for waveform visibility
    logic [7:0] w_packet_enable_mask;

    // Optional: Additional debug wires to see packet breakdown in waveforms
    logic [63:0] w_packet_debug_fields;

    // =========================================================================
    // Client Weights - Use CLIENTS parameter
    // =========================================================================
    logic [MTW-1:0] client_weight [CLIENTS];

    // Extract client weights for easier access
    generate
        for (genvar j = 0; j < CLIENTS; j++) begin : gen_weights
            assign client_weight[j] = cfg_max_thresh[(j+1)*MTW-1 -: MTW];
        end
    endgenerate

    // =========================================================================
    // Monitor State and Counters (Registered)
    // =========================================================================

    // Original counters
    logic [15:0]                          r_total_grants;
    logic [15:0]                          r_total_completed_grants;
    logic [15:0]                          r_grant_counters [CLIENTS];
    logic [15:0]                          r_completed_grants [CLIENTS];
    logic [15:0]                          r_latency_counters [CLIENTS];
    logic [15:0]                          r_starvation_counters [CLIENTS];
    logic [CLIENTS-1:0]                   r_starvation_detected;
    logic [15:0]                          r_protocol_violation_count;
    logic [15:0]                          r_debug_packet_count;

    // Sample timing
    logic [7:0]                           r_sample_timer;

    // Fairness tracking
    logic [15:0]                          r_fairness_timer;
    logic [15:0]                          r_expected_weights [CLIENTS];
    logic [15:0]                          r_actual_weights [CLIENTS];
    logic [15:0]                          r_max_fairness_deviation;

    // ACK timeout tracking (per-client)
    logic [15:0]                          r_ack_timers [CLIENTS];
    logic [CLIENTS-1:0]                   r_ack_pending;
    logic [CLIENTS-1:0]                   r_ack_timeout_detected;

    // Monitor state machine
    typedef enum logic [2:0] {
        MON_IDLE      = 3'b000,  // Monitoring disabled
        MON_ACTIVE    = 3'b001,  // Normal monitoring
        MON_SAMPLE    = 3'b010,  // Sample period active
        MON_ANALYZE   = 3'b011,  // Analysis phase
        MON_FAIRNESS  = 3'b100,  // Fairness analysis
        MON_ERROR     = 3'b101   // Error state
    } monitor_state_t;

    monitor_state_t r_monitor_state;

    // Event detection pipeline registers
    logic                                 r_starvation_event;
    logic [N-1:0]                         r_starvation_client;
    logic                                 r_latency_threshold_event;
    logic [N-1:0]                         r_latency_client;
    logic                                 r_active_threshold_event;
    logic                                 r_grant_event;
    logic [N-1:0]                         r_grant_client_id;
    logic                                 r_ack_timeout_event;
    logic [N-1:0]                         r_ack_timeout_client;
    logic                                 r_protocol_violation_event;
    logic                                 r_fairness_violation_event;
    logic                                 r_efficiency_threshold_event;
    logic                                 r_completion_event;
    logic [N-1:0]                         r_completion_client;

    // =========================================================================
    // Event Detection Combinational Logic - WITH MONITOR ENABLE GATING
    // =========================================================================

    // Initialize the padding to zero
    assign w_evt_pad0 = '0;

    // Gate all event detection with cfg_mon_enable
    assign w_starvation_detected = cfg_mon_enable && (|r_starvation_detected);

    // Find first starved client (priority encoder)
    always_comb begin
        w_starvation_client = {N{1'b0}};
        if (cfg_mon_enable) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (r_starvation_detected[i]) begin
                    w_starvation_client = N'(i);
                    break;
                end
            end
        end
    end

    // Latency threshold detection
    always_comb begin
        w_latency_threshold_detected = 1'b0;
        w_latency_threshold_client = {N{1'b0}};
        if (cfg_mon_enable) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (r_latency_counters[i] >= cfg_mon_latency_thresh) begin
                    w_latency_threshold_detected = 1'b1;
                    w_latency_threshold_client = N'(i);
                    break;
                end
            end
        end
    end

    // Active request threshold detection
    assign w_active_request_count = $countones(request);
    assign w_active_threshold_detected = cfg_mon_enable && (w_active_request_count >= cfg_mon_active_thresh[$clog2(CLIENTS+1)-1:0]);

    // Grant event detection
    assign w_grant_event_detected = cfg_mon_enable && grant_valid && (|grant);
    assign w_grant_client_id = grant_id;

    // ACK timeout detection
    assign w_ack_timeout_event_detected = cfg_mon_enable && (|r_ack_timeout_detected);

    // Find first timeout client
    always_comb begin
        w_ack_timeout_client = {N{1'b0}};
        if (cfg_mon_enable) begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (r_ack_timeout_detected[i]) begin
                    w_ack_timeout_client = N'(i);
                    break;
                end
            end
        end
    end

    // Protocol violation intermediate signals
    logic w_multiple_grants;       // Multiple grants issued simultaneously
    logic w_spurious_ack;          // ACK without pending grant
    logic w_grant_without_request; // Grant to client without request

    // Multiple grants detection (should be one-hot)
    assign w_multiple_grants = grant_valid && ($countones(grant) > 1);

    // Spurious ACK detection (ACK without pending grant) - only if ACK mode enabled
    assign w_spurious_ack = (WAIT_GNT_ACK == 1) ?
                            ((|grant_ack) && ((grant_ack & r_ack_pending) != grant_ack)) : 1'b0;

    // Grant without request detection
    assign w_grant_without_request = grant_valid && ((grant & request) != grant);

    // Combined protocol violation with monitor enable gating
    assign w_protocol_violation_detected = cfg_mon_enable &&
                            (w_multiple_grants || w_spurious_ack || w_grant_without_request);

    // Fairness violation detection
    assign w_fairness_violation_detected = cfg_mon_enable && (r_max_fairness_deviation >= cfg_mon_fairness_thresh);

    // Efficiency calculation and threshold detection
    logic [31:0] w_efficiency_raw_calc;

    // Calculate raw efficiency percentage
    assign w_efficiency_raw_calc = (r_total_grants > 0) ?
        (32'(r_total_completed_grants) * 32'd100 / 32'(r_total_grants)) : 32'd100;

    // Clamp to valid range (0-100%)
    assign w_current_efficiency = (w_efficiency_raw_calc > 32'd100) ? 16'd100 : 16'(w_efficiency_raw_calc);

    assign w_efficiency_threshold_detected = cfg_mon_enable && (w_current_efficiency < cfg_mon_efficiency_thresh);

    // Completion event detection with monitor enable gating
    assign w_completion_event_detected = cfg_mon_enable &&
                                        ((WAIT_GNT_ACK == 0) ? (grant_valid && (|grant)) : (|grant_ack));

    always_comb begin
        w_completion_client = {N{1'b0}};
        if (cfg_mon_enable) begin
            if (WAIT_GNT_ACK == 0) begin
                w_completion_client = grant_id;
            end else begin
                for (int i = 0; i < CLIENTS; i++) begin
                    if (grant_ack[i]) begin
                        w_completion_client = N'(i);
                        break;
                    end
                end
            end
        end
    end

    // =========================================================================
    // ACK Timeout Management (Per-Client)
    // =========================================================================

    generate
        if (WAIT_GNT_ACK == 1) begin : gen_ack_monitoring

            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    for (int i = 0; i < CLIENTS; i++) begin
                        r_ack_timers[i] <= 16'h0;
                        r_ack_pending[i] <= 1'b0;
                        r_ack_timeout_detected[i] <= 1'b0;
                    end
                end else begin
                    for (int i = 0; i < CLIENTS; i++) begin
                        if (grant_valid && grant[i]) begin
                            // Grant issued - start ACK timer
                            r_ack_pending[i] <= 1'b1;
                            r_ack_timers[i] <= 16'h0;
                            r_ack_timeout_detected[i] <= 1'b0;
                        end else if (r_ack_pending[i] && grant_ack[i]) begin
                            // ACK received - clear timer
                            r_ack_pending[i] <= 1'b0;
                            r_ack_timers[i] <= 16'h0;
                            r_ack_timeout_detected[i] <= 1'b0;
                        end else if (r_ack_pending[i]) begin
                            // Timer running
                            r_ack_timers[i] <= r_ack_timers[i] + 16'h1;
                            if (r_ack_timers[i] >= cfg_mon_ack_timeout_thresh) begin
                                r_ack_timeout_detected[i] <= 1'b1;
                                r_ack_pending[i] <= 1'b0;  // Clear pending to avoid multiple events
                            end
                        end
                    end
                end
            )


        end else begin : gen_no_ack_monitoring
            // No ACK monitoring - tie off signals
            always_comb begin
                for (int i = 0; i < CLIENTS; i++) begin
                    r_ack_timers[i] = 16'h0;
                    r_ack_pending[i] = 1'b0;
                    r_ack_timeout_detected[i] = 1'b0;
                end
            end
        end
    endgenerate

    // =========================================================================
    // Monitor State Machine
    // =========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_monitor_state <= MON_IDLE;
        end else begin
            case (r_monitor_state)
                MON_IDLE: begin
                    if (cfg_mon_enable) begin
                        r_monitor_state <= MON_ACTIVE;
                    end
                end

                MON_ACTIVE: begin
                    if (!cfg_mon_enable) begin
                        r_monitor_state <= MON_IDLE;
                    end else if (w_sample_event) begin
                        r_monitor_state <= MON_SAMPLE;
                    end
                end

                MON_SAMPLE: begin
                    r_monitor_state <= MON_ANALYZE;
                end

                MON_ANALYZE: begin
                    r_monitor_state <= MON_FAIRNESS;
                end

                MON_FAIRNESS: begin
                    r_monitor_state <= MON_ACTIVE;
                end

                MON_ERROR: begin
                    if (cfg_mon_enable) begin
                        r_monitor_state <= MON_ACTIVE;
                    end else begin
                        r_monitor_state <= MON_IDLE;
                    end
                end

                default: r_monitor_state <= MON_IDLE;
            endcase
        end
    )


    // =========================================================================
    // Grant and Completion Tracking
    // =========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_total_grants <= 16'h0;
            r_total_completed_grants <= 16'h0;
            for (int i = 0; i < CLIENTS; i++) begin
                r_grant_counters[i] <= 16'h0;
                r_completed_grants[i] <= 16'h0;
            end
        end else begin
            // Track grants
            if (grant_valid && (|grant)) begin
                r_total_grants <= r_total_grants + 16'h1;
                for (int i = 0; i < CLIENTS; i++) begin
                    if (grant[i]) begin
                        r_grant_counters[i] <= r_grant_counters[i] + 16'h1;
                    end
                end
            end

            // Track completions (ACK received or immediate completion if no ACK required)
            if (WAIT_GNT_ACK == 0) begin
                // Immediate completion
                if (grant_valid && (|grant)) begin
                    r_total_completed_grants <= r_total_completed_grants + 16'h1;
                    for (int i = 0; i < CLIENTS; i++) begin
                        if (grant[i]) begin
                            r_completed_grants[i] <= r_completed_grants[i] + 16'h1;
                        end
                    end
                end
            end else begin
                // Completion on ACK
                if (|grant_ack) begin
                    r_total_completed_grants <= r_total_completed_grants + 16'h1;
                    for (int i = 0; i < CLIENTS; i++) begin
                        if (grant_ack[i]) begin
                            r_completed_grants[i] <= r_completed_grants[i] + 16'h1;
                        end
                    end
                end
            end
        end
    )


    // =========================================================================
    // Fairness Tracking (Weighted Arbiter Support)
    // =========================================================================
    logic [15:0] max_deviation_temp;
    logic [15:0] total_weight;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_fairness_timer <= 16'h0;
            r_max_fairness_deviation <= 16'h0;
            for (int i = 0; i < CLIENTS; i++) begin
                r_expected_weights[i] <= 16'(client_weight[i]);
                r_actual_weights[i] <= 16'h0;
            end
        end else begin
            r_fairness_timer <= r_fairness_timer + 16'h1;

            if (r_fairness_timer >= 16'(FAIRNESS_REPORT_CYCLES)) begin
                // Calculate fairness metrics
                r_fairness_timer <= 16'h0;

                // Update expected weights from current configuration
                for (int i = 0; i < CLIENTS; i++) begin
                    r_expected_weights[i] <= 16'(client_weight[i]);
                end

                // Calculate actual weights based on grant distribution
                if (r_total_grants >= 16'(MIN_GRANTS_FOR_FAIRNESS)) begin
                    for (int i = 0; i < CLIENTS; i++) begin
                        r_actual_weights[i] <= (r_grant_counters[i] * 16) / r_total_grants;
                    end

                    // Calculate maximum deviation
                    if (r_total_grants >= 16'(MIN_GRANTS_FOR_FAIRNESS)) begin
                        // Calculate actual weights based on grant distribution
                        for (int i = 0; i < CLIENTS; i++) begin
                            r_actual_weights[i] <= (r_grant_counters[i] * 16) / r_total_grants;
                        end

                        // Calculate maximum fairness deviation
                        max_deviation_temp = 16'h0;
                        total_weight = 16'h0;

                        // Calculate total weight
                        for (int j = 0; j < CLIENTS; j++) begin
                            if (client_weight[j] > 0) begin
                                total_weight = total_weight + 16'(client_weight[j]);
                            end
                        end

                        // Calculate deviations for each client
                        for (int i = 0; i < CLIENTS; i++) begin
                            if (total_weight > 0 && client_weight[i] > 0) begin
                                logic [15:0] expected_percentage;
                                logic [15:0] actual_percentage;
                                logic [15:0] deviation;

                                // Expected percentage = (client_weight / total_weight) * 100
                                expected_percentage = (16'(client_weight[i]) * 100) / total_weight;

                                // Actual percentage = (client_grants / total_grants) * 100
                                actual_percentage = (r_grant_counters[i] * 100) / r_total_grants;

                                // Calculate absolute deviation
                                if (actual_percentage >= expected_percentage) begin
                                    deviation = actual_percentage - expected_percentage;
                                end else begin
                                    deviation = expected_percentage - actual_percentage;
                                end

                                // Track maximum deviation
                                if (deviation > max_deviation_temp) begin
                                    max_deviation_temp = deviation;
                                end
                            end
                        end

                        r_max_fairness_deviation <= max_deviation_temp;
                    end
                end
            end
        end
    )


    // =========================================================================
    // Latency and Starvation Tracking
    // =========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < CLIENTS; i++) begin
                r_latency_counters[i] <= 16'h0;
                r_starvation_counters[i] <= 16'h0;
            end
            r_starvation_detected <= {CLIENTS{1'b0}};
        end else begin
            for (int i = 0; i < CLIENTS; i++) begin
                if (request[i] && !grant[i]) begin
                    // Request pending - increment counters
                    r_latency_counters[i] <= r_latency_counters[i] + 16'h1;
                    r_starvation_counters[i] <= r_starvation_counters[i] + 16'h1;

                    // Check for starvation
                    if (r_starvation_counters[i] >= cfg_mon_starvation_thresh) begin
                        r_starvation_detected[i] <= 1'b1;
                    end
                end else if (grant[i]) begin
                    // Grant received - reset counters
                    r_latency_counters[i] <= 16'h0;
                    r_starvation_counters[i] <= 16'h0;
                    r_starvation_detected[i] <= 1'b0;
                end
            end
        end
    )


    // =========================================================================
    // Sample Timer
    // =========================================================================

    assign w_sample_event = (r_sample_timer == cfg_mon_sample_period);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sample_timer <= 8'h0;
        end else begin
            if (w_sample_event) begin
                r_sample_timer <= 8'h0;
            end else begin
                r_sample_timer <= r_sample_timer + 8'h1;
            end
        end
    )


    // =========================================================================
    // Event Detection Pipeline Register
    // =========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_starvation_event <= 1'b0;
            r_starvation_client <= {N{1'b0}};
            r_latency_threshold_event <= 1'b0;
            r_latency_client <= {N{1'b0}};
            r_active_threshold_event <= 1'b0;
            r_grant_event <= 1'b0;
            r_grant_client_id <= {N{1'b0}};
            r_ack_timeout_event <= 1'b0;
            r_ack_timeout_client <= {N{1'b0}};
            r_protocol_violation_event <= 1'b0;
            r_fairness_violation_event <= 1'b0;
            r_efficiency_threshold_event <= 1'b0;
            r_completion_event <= 1'b0;
            r_completion_client <= {N{1'b0}};
        end else begin
            // Register the event detection results
            r_starvation_event <= w_starvation_detected;
            r_starvation_client <= w_starvation_client;
            r_latency_threshold_event <= w_latency_threshold_detected;
            r_latency_client <= w_latency_threshold_client;
            r_active_threshold_event <= w_active_threshold_detected;
            r_grant_event <= w_grant_event_detected;
            r_grant_client_id <= w_grant_client_id;
            r_ack_timeout_event <= w_ack_timeout_event_detected;
            r_ack_timeout_client <= w_ack_timeout_client;
            r_protocol_violation_event <= w_protocol_violation_detected;
            r_fairness_violation_event <= w_fairness_violation_detected;
            r_efficiency_threshold_event <= w_efficiency_threshold_detected;
            r_completion_event <= w_completion_event_detected;
            r_completion_client <= w_completion_client;
        end
    )


    // =========================================================================
    // Event Packet Generation with Debug Wires and Enum Names
    // Using consistent naming conventions for easy signal location
    // =========================================================================

    // Convert raw values to enums for waveform display
    assign w_packet_enum_protocol = protocol_type_t'(w_packet_protocol);

    // Conditional enum assignments based on packet type
    always_comb begin
        // Default enum values
        w_packet_enum_arb_error = arb_error_code_t'(4'h0);
        w_packet_enum_arb_timeout = arb_timeout_code_t'(4'h0);
        w_packet_enum_arb_completion = arb_completion_code_t'(4'h0);
        w_packet_enum_arb_threshold = arb_threshold_code_t'(4'h0);
        w_packet_enum_arb_performance = arb_performance_code_t'(4'h0);

        case (w_packet_pkt_type)
            PktTypeError: begin
                w_packet_enum_arb_error = arb_error_code_t'(w_packet_event_code);
            end
            PktTypeTimeout: begin
                w_packet_enum_arb_timeout = arb_timeout_code_t'(w_packet_event_code);
            end
            PktTypeCompletion: begin
                w_packet_enum_arb_completion = arb_completion_code_t'(w_packet_event_code);
            end
            PktTypeThreshold: begin
                w_packet_enum_arb_threshold = arb_threshold_code_t'(w_packet_event_code);
            end
            PktTypePerf: begin
                w_packet_enum_arb_performance = arb_performance_code_t'(w_packet_event_code);
            end
            default: begin
                // Keep default values
            end
        endcase
    end

    // =========================================================================
    // Enable signals for each packet type (makes debugging easier)
    // =========================================================================

    assign w_packet_starvation_pkt_en      = r_starvation_event && cfg_mon_pkt_type_enable[PktTypeError];
    assign w_packet_ack_timeout_pkt_en     = r_ack_timeout_event && cfg_mon_pkt_type_enable[PktTypeTimeout];
    assign w_packet_latency_thresh_pkt_en  = r_latency_threshold_event && cfg_mon_pkt_type_enable[PktTypeThreshold];
    assign w_packet_fairness_violation_pkt_en = r_fairness_violation_event && cfg_mon_pkt_type_enable[PktTypeThreshold];
    assign w_packet_efficiency_thresh_pkt_en = r_efficiency_threshold_event && cfg_mon_pkt_type_enable[PktTypeThreshold];
    assign w_packet_active_thresh_pkt_en   = r_active_threshold_event && cfg_mon_pkt_type_enable[PktTypeThreshold];
    assign w_packet_completion_pkt_en      = r_completion_event && cfg_mon_pkt_type_enable[PktTypeCompletion];
    assign w_packet_grant_perf_pkt_en      = r_grant_event && cfg_mon_pkt_type_enable[PktTypePerf];

    // Event valid signal (any packet enabled) - determines if packets are generated
    assign w_event_valid = w_packet_starvation_pkt_en || w_packet_ack_timeout_pkt_en || w_packet_latency_thresh_pkt_en ||
                          w_packet_fairness_violation_pkt_en || w_packet_efficiency_thresh_pkt_en || w_packet_active_thresh_pkt_en ||
                          w_packet_completion_pkt_en || w_packet_grant_perf_pkt_en;

    // Packet field assignments (priority-encoded)
    always_comb begin
        // Default values
        w_packet_pkt_type    = 4'h0;
        w_packet_protocol    = PROTOCOL_ARB;  // Always ARB protocol for this monitor
        w_packet_event_code  = 4'h0;
        w_packet_channel_id  = 6'h0;
        w_packet_unit_id     = MON_UNIT_ID;   // Always use module's unit ID
        w_packet_agent_id    = MON_AGENT_ID;  // Always use module's agent ID
        w_packet_data        = 35'h0;         // ✅ CORRECT: 35 bits

        // Priority-encoded packet type selection
        if (w_packet_starvation_pkt_en) begin
            // ARB starvation error packet
            w_packet_pkt_type   = PktTypeError;
            w_packet_event_code = ARB_ERR_STARVATION;
            w_packet_channel_id = 6'(r_starvation_client);
            w_packet_data       = {19'h0, r_starvation_counters[r_starvation_client]};  // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_ack_timeout_pkt_en) begin
            // ARB ACK timeout packet
            w_packet_pkt_type   = PktTypeTimeout;
            w_packet_event_code = ARB_TIMEOUT_GRANT_ACK;
            w_packet_channel_id = 6'(r_ack_timeout_client);
            w_packet_data       = {19'h0, r_ack_timers[r_ack_timeout_client]};         // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_latency_thresh_pkt_en) begin
            // ARB latency threshold packet
            w_packet_pkt_type   = PktTypeThreshold;
            w_packet_event_code = ARB_THRESH_REQUEST_LATENCY;
            w_packet_channel_id = 6'(r_latency_client);
            w_packet_data       = {19'h0, r_latency_counters[r_latency_client]};       // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_fairness_violation_pkt_en) begin
            // ARB fairness violation packet
            w_packet_pkt_type   = PktTypeThreshold;
            w_packet_event_code = ARB_THRESH_FAIRNESS_DEV;
            w_packet_channel_id = 6'h0;
            w_packet_data       = {19'h0, r_max_fairness_deviation};                   // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_efficiency_thresh_pkt_en) begin
            // ARB efficiency threshold packet
            w_packet_pkt_type   = PktTypeThreshold;
            w_packet_event_code = ARB_THRESH_EFFICIENCY;
            w_packet_channel_id = 6'h0;
            w_packet_data       = {19'h0, w_current_efficiency};                       // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_active_thresh_pkt_en) begin
            // ARB active request threshold packet
            w_packet_pkt_type   = PktTypeThreshold;
            w_packet_event_code = ARB_THRESH_ACTIVE_REQUESTS;
            w_packet_channel_id = 6'h0;
            w_packet_data       = {w_evt_pad0, w_active_request_count};                // ✅ CORRECT: Total 35 bits

        end else if (w_packet_completion_pkt_en) begin
            // ARB transaction completion packet
            w_packet_pkt_type   = PktTypeCompletion;
            w_packet_event_code = ARB_COMPL_TRANSACTION;
            w_packet_channel_id = 6'(r_completion_client);
            w_packet_data       = {19'h0, r_completed_grants[r_completion_client]};    // ✅ CORRECT: 19+16=35 bits

        end else if (w_packet_grant_perf_pkt_en) begin
            // ARB grant issued performance packet
            w_packet_pkt_type   = PktTypePerf;
            w_packet_event_code = ARB_PERF_GRANT_ISSUED;
            w_packet_channel_id = 6'(r_grant_client_id);
            w_packet_data       = {19'h0, r_grant_counters[r_grant_client_id]};        // ✅ CORRECT: 19+16=35 bits
        end
    end

    // Single line to create the final packet using the debug wires
    assign w_event_packet = create_monitor_packet(
        w_packet_pkt_type,
        protocol_type_t'(w_packet_protocol),
        w_packet_event_code,
        w_packet_channel_id,
        w_packet_unit_id,
        w_packet_agent_id,
        w_packet_data
    );

    // Optional: Additional debug wires to see packet breakdown in waveforms
    assign w_packet_debug_fields = {
        w_packet_pkt_type,    // [63:60]
        w_packet_protocol,    // [59:57] ✅ CORRECT: 3 bits
        w_packet_event_code,  // [56:53]
        w_packet_channel_id,  // [52:47]
        w_packet_unit_id,     // [46:43]
        w_packet_agent_id,    // [42:35]
        w_packet_data         // [34:0] ✅ CORRECT: 35 bits
    };

    // Debug enable mask for waveform visibility
    assign w_packet_enable_mask = {
        w_packet_grant_perf_pkt_en,        // [7]
        w_packet_completion_pkt_en,        // [6]
        w_packet_active_thresh_pkt_en,     // [5]
        w_packet_efficiency_thresh_pkt_en, // [4]
        w_packet_fairness_violation_pkt_en,// [3]
        w_packet_latency_thresh_pkt_en,    // [2]
        w_packet_ack_timeout_pkt_en,       // [1]
        w_packet_starvation_pkt_en         // [0]
    };

    // =========================================================================
    // Event FIFO Instance
    // =========================================================================

    assign w_fifo_wr_valid = w_event_valid;
    assign w_fifo_rd_ready = monbus_ready;
    assign w_fifo_write_transfer = w_fifo_wr_valid & w_fifo_wr_ready;
    assign w_fifo_read_transfer = w_fifo_rd_valid & w_fifo_rd_ready;

    gaxi_fifo_sync #(
        .REGISTERED         (0),                    // 0 = mux mode
        .DATA_WIDTH         (64),                   // 64-bit monitor packets
        .DEPTH              (MON_FIFO_DEPTH),       // Configurable FIFO depth
        .ALMOST_WR_MARGIN   (MON_FIFO_ALMOST_MARGIN),
        .ALMOST_RD_MARGIN   (MON_FIFO_ALMOST_MARGIN),
        .INSTANCE_NAME      ("MONBUS_EVENT_FIFO")
    ) u_event_fifo (
        .axi_aclk           (clk),
        .axi_aresetn        (rst_n),
        .wr_valid           (w_fifo_wr_valid),
        .wr_ready           (w_fifo_wr_ready),
        .wr_data            (w_event_packet),
        .rd_ready           (w_fifo_rd_ready),
        .rd_valid           (w_fifo_rd_valid),
        .rd_data            (w_fifo_data_out),
        .count              (w_fifo_count)
    );

    // =========================================================================
    // Monitor Bus Output Interface
    // =========================================================================

    assign monbus_valid = w_fifo_rd_valid;
    assign monbus_packet = w_fifo_data_out;

    // =========================================================================
    // Debug Output Generation
    // =========================================================================

    assign debug_fifo_count = w_fifo_count;

    // Packet counter
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_debug_packet_count <= 16'h0;
        end else if (w_fifo_write_transfer) begin
            r_debug_packet_count <= r_debug_packet_count + 16'h1;
        end
    )

    assign debug_packet_count = r_debug_packet_count;

    // debug outputs
    assign debug_ack_timeout = r_ack_timeout_detected;
    assign debug_protocol_violations = r_protocol_violation_count;
    assign debug_grant_efficiency = w_current_efficiency;
    assign debug_client_starvation = r_starvation_detected;
    assign debug_fairness_deviation = r_max_fairness_deviation;
    assign debug_monitor_state = r_monitor_state;

    // Additional debug wires for fairness monitoring
    logic [15:0] w_debug_total_weight;
    logic [15:0] w_debug_expected_percentage [CLIENTS];
    logic [15:0] w_debug_actual_percentage [CLIENTS];

    // Calculate total weight for debug
    always_comb begin
        w_debug_total_weight = 16'h0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (client_weight[i] > 0) begin
                w_debug_total_weight = w_debug_total_weight + 16'(client_weight[i]);
            end
        end
    end

    // Calculate expected vs actual percentages for debug
    generate
        for (genvar i = 0; i < CLIENTS; i++) begin : gen_debug_percentages
            always_comb begin
                if (w_debug_total_weight > 0 && client_weight[i] > 0) begin
                    w_debug_expected_percentage[i] = (16'(client_weight[i]) * 100) / w_debug_total_weight;
                end else begin
                    w_debug_expected_percentage[i] = 16'h0;
                end

                if (r_total_grants > 0) begin
                    w_debug_actual_percentage[i] = (r_grant_counters[i] * 100) / r_total_grants;
                end else begin
                    w_debug_actual_percentage[i] = 16'h0;
                end
            end
        end
    endgenerate

endmodule : arbiter_monbus_common
