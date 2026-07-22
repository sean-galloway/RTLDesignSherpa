// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: arbiter_wrr_pwm_monbus
// Purpose: Arbiter Wrr Pwm Monbus module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/*
================================================================================
WEIGHTED ROUND-ROBIN ARBITER WITH PWM AND MONITOR BUS (VERSION 2 - STANDARDIZED)
================================================================================

This module combines a weighted round-robin arbiter with PWM control and
comprehensive monitoring capabilities. It uses the common arbiter_monbus_common
component for reusable monitoring functionality.

STANDARDIZED FIXED INTERNAL CONFIGURATIONS:
- PWM_WIDTH: Fixed to 16 (adequate resolution for most use cases)
- MON_FIFO_DEPTH: Fixed to 16 (optimal for most monitoring scenarios)
- MON_FIFO_ALMOST_MARGIN: Fixed to 2 (safety margin)
- FAIRNESS_REPORT_CYCLES: Fixed to 256 (power-of-2 efficient)
- MIN_GRANTS_FOR_FAIRNESS: Fixed to 64 (statistical significance)

USER-CONFIGURABLE PARAMETERS:
- MAX_LEVELS: Maximum weight levels per client (1-64)
- CLIENTS: Number of arbitration clients (1-64)
- WAIT_GNT_ACK: Acknowledge protocol enable (0 or 1)
- MON_AGENT_ID: Monitor agent identifier (8-bit, default 8'h10)
- MON_UNIT_ID: Monitor unit identifier (4-bit, default 4'h0)

Key Features:
- Weighted round-robin arbitration with configurable client priorities
- PWM-based arbiter blocking for periodic control (16-bit resolution)
- Comprehensive monitoring via shared monitor bus component
- Configurable weight thresholds per client
- Real-time performance and fairness tracking
- Fixed internal sizing for consistency and predictability

Architecture:
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│  Weighted RR    │    │  PWM Generator  │    │  Monitor Bus    │
│  Arbiter        │    │                 │    │  Common         │
│                 │◄───│  block_arb      │    │                 │
│  • Weight-based │    │  • 16-bit res   │    │  • Event detect │
│  • ACK support  │    │  • Duty cycle   │    │  • Performance  │
│  • Client reqs  │    │  • Period ctrl  │    │  • Fairness     │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
                        ┌─────────────────┐
                        │  64-bit Monitor │
                        │  Bus Output     │
                        └─────────────────┘

Weight Configuration:
- Per-client weight thresholds define priority levels
- Higher weights = higher priority in arbitration
- Supports up to MAX_LEVELS priority levels per client
- Fair rotation within same weight level
*/

module arbiter_wrr_pwm_monbus #(
    // Monitor enable: 1 = telemetry on, 0 = omit monbus block (arbiter+PWM stay).
    parameter bit USE_MONITOR = 1'b1,

    // User-configurable arbiter parameters
    parameter int MAX_LEVELS = 16,                  // Maximum weight levels per client (1-64)
    parameter int CLIENTS = 4,                      // Number of arbitration clients (1-64)
    parameter int WAIT_GNT_ACK = 0,                 // Acknowledge protocol: 0=disable, 1=enable

    // User-configurable monitor identification (widened for 128-bit packet)
    /* verilator lint_off WIDTHTRUNC */
    parameter logic [15:0] MON_AGENT_ID = 16'h0010, // Agent ID (16-bit per monitor bus protocol)
    parameter logic [7:0]  MON_UNIT_ID  = 8'h00,    // Unit ID (8-bit per monitor bus protocol)
    /* verilator lint_on WIDTHTRUNC */

    // STANDARDIZED FIXED INTERNAL CONFIGURATION (not user-configurable)
    // These are set to optimal values based on documentation and analysis
    localparam int PWM_WIDTH = 16,                  // 16-bit PWM resolution (standardized)
    localparam int MON_FIFO_DEPTH = 16,             // Monitor FIFO depth (power-of-2, standardized)
    localparam int MON_FIFO_ALMOST_MARGIN = 2,      // FIFO safety margin (standardized)
    localparam int FAIRNESS_REPORT_CYCLES = 256,    // Fairness reporting interval (standardized)
    localparam int MIN_GRANTS_FOR_FAIRNESS = 64,    // Minimum grants for fairness calc (standardized)

    // Calculated parameters
    parameter int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    parameter int N = $clog2(CLIENTS),
    parameter int CXMTW = CLIENTS * MAX_LEVELS_WIDTH
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Arbiter configuration and interface
    input  logic [CXMTW-1:0]              cfg_arb_max_thresh,  // Per-client weight thresholds
    input  logic [CLIENTS-1:0]            request,             // Client requests (standardized name)
    output logic                          grant_valid,
    output logic [CLIENTS-1:0]            grant,
    output logic [N-1:0]                  grant_id,
    input  logic [CLIENTS-1:0]            grant_ack,

    // PWM configuration (single channel for arbiter control, 16-bit resolution)
    input  logic                          cfg_pwm_sync_rst_n,
    input  logic                          cfg_pwm_start,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_duty,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_period,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_repeat_count,
    output logic                          cfg_pwm_sts_done,
    output logic                          pwm_out,

    // Monitor bus configuration (updated to match modern interface)
    input  logic                          cfg_mon_enable,
    input  logic [15:0]                   cfg_mon_pkt_type_enable,
    input  logic [15:0]                   cfg_mon_latency_thresh,
    input  logic [15:0]                   cfg_mon_starvation_thresh,
    input  logic [15:0]                   cfg_mon_fairness_thresh,
    input  logic [15:0]                   cfg_mon_active_thresh,
    input  logic [15:0]                   cfg_mon_ack_timeout_thresh,
    input  logic [15:0]                   cfg_mon_efficiency_thresh,
    input  logic [7:0]                    cfg_mon_sample_period,

    // Free-running monitor-time broadcast from the monbus_group family
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor bus output - 128-bit packet + 64-bit side-band timestamp
    output logic                                    monbus_valid,
    input  logic                                    monbus_ready,
    output monitor_common_pkg::monitor_packet_t     monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,

    // Enhanced debug outputs for silicon debug (matching modern interface)
    output logic [$clog2(MON_FIFO_DEPTH):0] debug_fifo_count,
    output logic [15:0]                     debug_packet_count,
    output logic [CLIENTS-1:0]              debug_ack_timeout,
    output logic [15:0]                     debug_protocol_violations,
    output logic [15:0]                     debug_grant_efficiency,
    output logic [CLIENTS-1:0]              debug_client_starvation,
    output logic [15:0]                     debug_fairness_deviation,
    output logic [2:0]                      debug_monitor_state
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    logic block_arb_internal;  // PWM output controls arbiter blocking

    // Connect PWM output directly to arbiter block_arb input
    assign block_arb_internal = pwm_out;

    // =========================================================================
    // Weighted Round-Robin Arbiter Instance
    // =========================================================================

    arbiter_round_robin_weighted #(
        .MAX_LEVELS      (MAX_LEVELS),
        .CLIENTS         (CLIENTS),
        .WAIT_GNT_ACK    (WAIT_GNT_ACK)
    ) u_arbiter (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (block_arb_internal),
        .max_thresh  (cfg_arb_max_thresh),
        .request     (request),                  // Standardized signal name
        .grant_valid (grant_valid),
        .grant       (grant),
        .grant_id    (grant_id),
        .grant_ack   (grant_ack)
    );

    // =========================================================================
    // PWM Generator Instance (Single Channel, Standardized 16-bit Width)
    // =========================================================================

    pwm #(
        .WIDTH    (PWM_WIDTH),  // Standardized to 16-bit
        .CHANNELS (1)           // Single channel for arbiter control
    ) u_pwm (
        .clk          (clk),
        .rst_n        (rst_n),
        .sync_rst_n   (cfg_pwm_sync_rst_n),
        .start        (cfg_pwm_start),
        .duty         (cfg_pwm_duty),
        .period       (cfg_pwm_period),
        .repeat_count (cfg_pwm_repeat_count),
        .done         (cfg_pwm_sts_done),
        .pwm_out      (pwm_out)
    );

    // =========================================================================
    // Common Monitor Bus Instance (Standardized Fixed Configuration, optional)
    // =========================================================================
    // USE_MONITOR=1: arbiter_monbus_common synthesised. USE_MONITOR=0: omitted;
    //   arbiter+PWM unchanged (monitor is pure snooper; block_arb is PWM-driven
    //   only). Telemetry and debug outputs tied to non-blocking defaults.
    if (USE_MONITOR) begin : gen_monitor
        arbiter_monbus_common #(
            .CLIENTS                 (CLIENTS),                    // User configurable
            .WAIT_GNT_ACK            (WAIT_GNT_ACK),              // ACK protocol support
            .WEIGHTED_MODE           (1),                          // Enable weighted mode
            .MAX_LEVELS              (MAX_LEVELS),                 // Pass WRR MAX_LEVELS parameter
            .MON_AGENT_ID            (MON_AGENT_ID),              // User configurable (default 8'h10)
            .MON_UNIT_ID             (MON_UNIT_ID),               // User configurable (default 4'h0)
            .MON_FIFO_DEPTH          (MON_FIFO_DEPTH),            // Standardized to 16
            .MON_FIFO_ALMOST_MARGIN  (MON_FIFO_ALMOST_MARGIN),   // Standardized to 2
            .FAIRNESS_REPORT_CYCLES  (FAIRNESS_REPORT_CYCLES),    // Standardized to 256
            .MIN_GRANTS_FOR_FAIRNESS (MIN_GRANTS_FOR_FAIRNESS)    // Standardized to 64
        ) u_monitor (
            .clk                     (clk),
            .rst_n                   (rst_n),

            // Arbiter interface - using standardized signal names
            .cfg_max_thresh          (cfg_arb_max_thresh),        // Weight thresholds
            .request                 (request),
            .grant_valid             (grant_valid),
            .grant                   (grant),
            .grant_id                (grant_id),
            .grant_ack               (grant_ack),                 // ACK signals
            .block_arb               (block_arb_internal),

            // Monitor configuration - modern interface names
            .cfg_mon_enable          (cfg_mon_enable),
            .cfg_mon_pkt_type_enable (cfg_mon_pkt_type_enable),
            .cfg_mon_latency_thresh  (cfg_mon_latency_thresh),
            .cfg_mon_starvation_thresh (cfg_mon_starvation_thresh),
            .cfg_mon_fairness_thresh (cfg_mon_fairness_thresh),
            .cfg_mon_active_thresh   (cfg_mon_active_thresh),
            .cfg_mon_ack_timeout_thresh (cfg_mon_ack_timeout_thresh),
            .cfg_mon_efficiency_thresh (cfg_mon_efficiency_thresh),
            .cfg_mon_sample_period   (cfg_mon_sample_period),

            // Time + Monitor bus output (128-bit packet + 64-bit side-band)
            .i_mon_time              (i_mon_time),
            .monbus_valid            (monbus_valid),
            .monbus_ready            (monbus_ready),
            .monbus_packet           (monbus_packet),
            .monbus_timestamp        (monbus_timestamp),

            // Enhanced debug outputs
            .debug_fifo_count        (debug_fifo_count),
            .debug_packet_count      (debug_packet_count),
            .debug_ack_timeout       (debug_ack_timeout),
            .debug_protocol_violations (debug_protocol_violations),
            .debug_grant_efficiency  (debug_grant_efficiency),
            .debug_client_starvation (debug_client_starvation),
            .debug_fairness_deviation (debug_fairness_deviation),
            .debug_monitor_state     (debug_monitor_state)
        );
    end else begin : gen_no_monitor
        assign monbus_valid              = 1'b0;
        assign monbus_packet             = '0;
        assign monbus_timestamp          = '0;
        assign debug_fifo_count          = '0;
        assign debug_packet_count        = 16'h0;
        assign debug_ack_timeout         = '0;
        assign debug_protocol_violations = 16'h0;
        assign debug_grant_efficiency    = 16'h0;
        assign debug_client_starvation   = '0;
        assign debug_fairness_deviation  = 16'h0;
        assign debug_monitor_state       = 3'h0;
    end

    // =========================================================================
    // Assertions For Parameter Validation
    // =========================================================================

    initial begin
        assert (CLIENTS > 0) else $fatal(1, "CLIENTS must be > 0");
        assert (CLIENTS <= 64) else $fatal(1, "CLIENTS should be <= 64 for reasonable resource usage");
        assert (MAX_LEVELS > 0) else $fatal(1, "MAX_LEVELS must be > 0");
        assert (MAX_LEVELS <= 64) else $fatal(1, "MAX_LEVELS should be <= 64 for reasonable resource usage");
        assert (WAIT_GNT_ACK == 0 || WAIT_GNT_ACK == 1) else $fatal(1, "WAIT_GNT_ACK must be 0 or 1");
    end

endmodule : arbiter_wrr_pwm_monbus
