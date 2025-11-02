// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_mon_cg
// Purpose: Axi4 Master Wr Mon Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Write with Integrated Filtered Monitoring and Clock Gating
 *
 * This module extends axi4_master_wr_mon with comprehensive clock gating capabilities
 * for power optimization. Features include:
 *
 * - Instantiates axi4_master_wr_mon for core functionality with filtering
 * - Activity-based clock gating for the monitor subsystem
 * - Configurable clock gating policies and thresholds
 * - Independent gating for different monitor functions
 * - Performance monitoring with clock gating statistics
 * - Fine-grained power management controls
 */

`include "reset_defs.svh"
module axi4_master_wr_mon_cg
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (passed through to axi4_master_wr_mon)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters
    parameter int UNIT_ID           = 1,     // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 11,    // 8-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

    // Clock gating parameters
    parameter bit ENABLE_CLOCK_GATING = 1,   // Enable clock gating
    parameter int CG_IDLE_CYCLES    = 8,     // Cycles to wait before gating clocks
    parameter bit CG_GATE_MONITOR   = 1,     // Gate monitor clocks when idle
    parameter bit CG_GATE_REPORTER  = 1,     // Gate reporter clocks when no packets
    parameter bit CG_GATE_TIMERS    = 1,     // Gate timer clocks when no timeouts enabled

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_axi_awid,
    input  logic [AW-1:0]              fub_axi_awaddr,
    input  logic [7:0]                 fub_axi_awlen,
    input  logic [2:0]                 fub_axi_awsize,
    input  logic [1:0]                 fub_axi_awburst,
    input  logic                       fub_axi_awlock,
    input  logic [3:0]                 fub_axi_awcache,
    input  logic [2:0]                 fub_axi_awprot,
    input  logic [3:0]                 fub_axi_awqos,
    input  logic [3:0]                 fub_axi_awregion,
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Monitor Configuration
    input  logic                       cfg_monitor_enable,      // Enable monitoring
    input  logic                       cfg_error_enable,        // Enable error detection
    input  logic                       cfg_timeout_enable,      // Enable timeout detection
    input  logic                       cfg_perf_enable,         // Enable performance monitoring
    input  logic [15:0]                cfg_timeout_cycles,      // Timeout threshold in cycles
    input  logic [31:0]                cfg_latency_threshold,   // Latency threshold for alerts

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types (for future routing)
    input  logic [15:0]                cfg_axi_error_mask,      // Individual error event mask
    input  logic [15:0]                cfg_axi_timeout_mask,    // Individual timeout event mask
    input  logic [15:0]                cfg_axi_compl_mask,      // Individual completion event mask
    input  logic [15:0]                cfg_axi_thresh_mask,     // Individual threshold event mask
    input  logic [15:0]                cfg_axi_perf_mask,       // Individual performance event mask
    input  logic [15:0]                cfg_axi_addr_mask,       // Individual address match event mask
    input  logic [15:0]                cfg_axi_debug_mask,      // Individual debug event mask

    // Clock Gating Configuration
    input  logic                       cfg_cg_enable,           // Enable clock gating
    input  logic [7:0]                 cfg_cg_idle_threshold,   // Idle cycles before gating
    input  logic                       cfg_cg_force_on,         // Force clocks on (debug mode)
    input  logic                       cfg_cg_gate_monitor,     // Enable monitor clock gating
    input  logic                       cfg_cg_gate_reporter,    // Enable reporter clock gating
    input  logic                       cfg_cg_gate_timers,      // Enable timer clock gating

    // Monitor Bus Output
    output logic                       monbus_valid,            // Monitor bus valid
    input  logic                       monbus_ready,            // Monitor bus ready
    output logic [63:0]                monbus_packet,           // Monitor packet

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Clock gating status
    output logic                       cg_monitor_gated,        // Monitor clock is gated
    output logic                       cg_reporter_gated,       // Reporter clock is gated
    output logic                       cg_timers_gated,         // Timer clocks are gated
    output logic [31:0]                cg_cycles_saved,         // Estimated cycles saved by gating

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // =========================================================================
    // Clock Gating Logic (identical to read version)
    // =========================================================================

    // Activity detection signals
    logic                    axi_activity;
    logic                    monitor_activity;
    logic                    reporter_activity;
    logic                    timer_activity;

    // Gated clocks
    logic                    aclk_monitor;
    logic                    aclk_reporter;
    logic                    aclk_timers;

    // Clock gating control
    logic                    cg_monitor_en;
    logic                    cg_reporter_en;
    logic                    cg_timers_en;

    // Activity counters
    logic [7:0]              monitor_idle_count;
    logic [7:0]              reporter_idle_count;
    logic [7:0]              timer_idle_count;

    // Cycle counting for power savings estimation
    logic [31:0]             total_cycles;
    logic [31:0]             gated_cycles;

    // Detect AXI activity (write channels)
    assign axi_activity = (fub_axi_awvalid && fub_axi_awready) ||
                         (fub_axi_wvalid && fub_axi_wready) ||
                         (fub_axi_bvalid && fub_axi_bready) ||
                         (m_axi_awvalid && m_axi_awready) ||
                         (m_axi_wvalid && m_axi_wready) ||
                         (m_axi_bvalid && m_axi_bready);

    // Detect monitor activity
    assign monitor_activity = cfg_monitor_enable && (axi_activity || (active_transactions > 0));

    // Detect reporter activity
    assign reporter_activity = monbus_valid || cfg_error_enable || cfg_perf_enable;

    // Detect timer activity
    assign timer_activity = cfg_timeout_enable || cfg_perf_enable;

    // Clock gating enable decisions
    assign cg_monitor_en = ENABLE_CLOCK_GATING && cfg_cg_enable && cfg_cg_gate_monitor &&
                          !cfg_cg_force_on && (monitor_idle_count >= cfg_cg_idle_threshold);

    assign cg_reporter_en = ENABLE_CLOCK_GATING && cfg_cg_enable && cfg_cg_gate_reporter &&
                           !cfg_cg_force_on && (reporter_idle_count >= cfg_cg_idle_threshold);

    assign cg_timers_en = ENABLE_CLOCK_GATING && cfg_cg_enable && cfg_cg_gate_timers &&
                         !cfg_cg_force_on && (timer_idle_count >= cfg_cg_idle_threshold);

    // Activity counters
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            monitor_idle_count <= '0;
            reporter_idle_count <= '0;
            timer_idle_count <= '0;
        end else begin
            // Monitor idle counter
            if (monitor_activity) begin
                monitor_idle_count <= '0;
            end else if (monitor_idle_count < 8'hFF) begin
                monitor_idle_count <= monitor_idle_count + 1'b1;
            end

            // Reporter idle counter
            if (reporter_activity) begin
                reporter_idle_count <= '0;
            end else if (reporter_idle_count < 8'hFF) begin
                reporter_idle_count <= reporter_idle_count + 1'b1;
            end

            // Timer idle counter
            if (timer_activity) begin
                timer_idle_count <= '0;
            end else if (timer_idle_count < 8'hFF) begin
                timer_idle_count <= timer_idle_count + 1'b1;
            end
        end
    )


    // Power savings tracking
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            total_cycles <= '0;
            gated_cycles <= '0;
        end else begin
            total_cycles <= total_cycles + 1'b1;
            if (cg_monitor_gated || cg_reporter_gated || cg_timers_gated) begin
                gated_cycles <= gated_cycles + 1'b1;
            end
        end
    )


    // Clock gating cells (simplified model - in real design these would be ICG cells)
    generate
        if (ENABLE_CLOCK_GATING) begin : gen_clock_gating

            // Monitor clock gating
            always_comb begin
                if (cg_monitor_en && !monitor_activity) begin
                    aclk_monitor = 1'b0;
                    cg_monitor_gated = 1'b1;
                end else begin
                    aclk_monitor = aclk;
                    cg_monitor_gated = 1'b0;
                end
            end

            // Reporter clock gating
            always_comb begin
                if (cg_reporter_en && !reporter_activity) begin
                    aclk_reporter = 1'b0;
                    cg_reporter_gated = 1'b1;
                end else begin
                    aclk_reporter = aclk;
                    cg_reporter_gated = 1'b0;
                end
            end

            // Timer clock gating
            always_comb begin
                if (cg_timers_en && !timer_activity) begin
                    aclk_timers = 1'b0;
                    cg_timers_gated = 1'b1;
                end else begin
                    aclk_timers = aclk;
                    cg_timers_gated = 1'b0;
                end
            end

        end else begin : gen_no_clock_gating

            // No clock gating - pass through
            assign aclk_monitor = aclk;
            assign aclk_reporter = aclk;
            assign aclk_timers = aclk;
            assign cg_monitor_gated = 1'b0;
            assign cg_reporter_gated = 1'b0;
            assign cg_timers_gated = 1'b0;

        end
    endgenerate

    assign cg_cycles_saved = gated_cycles;

    // =========================================================================
    // Instantiate AXI4 Master Write Monitor with Filtering
    // =========================================================================
    axi4_master_wr_mon #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH),
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) axi4_master_wr_mon_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXI Interface (Input Side)
        .fub_axi_awid            (fub_axi_awid),
        .fub_axi_awaddr          (fub_axi_awaddr),
        .fub_axi_awlen           (fub_axi_awlen),
        .fub_axi_awsize          (fub_axi_awsize),
        .fub_axi_awburst         (fub_axi_awburst),
        .fub_axi_awlock          (fub_axi_awlock),
        .fub_axi_awcache         (fub_axi_awcache),
        .fub_axi_awprot          (fub_axi_awprot),
        .fub_axi_awqos           (fub_axi_awqos),
        .fub_axi_awregion        (fub_axi_awregion),
        .fub_axi_awuser          (fub_axi_awuser),
        .fub_axi_awvalid         (fub_axi_awvalid),
        .fub_axi_awready         (fub_axi_awready),

        .fub_axi_wdata           (fub_axi_wdata),
        .fub_axi_wstrb           (fub_axi_wstrb),
        .fub_axi_wlast           (fub_axi_wlast),
        .fub_axi_wuser           (fub_axi_wuser),
        .fub_axi_wvalid          (fub_axi_wvalid),
        .fub_axi_wready          (fub_axi_wready),

        .fub_axi_bid             (fub_axi_bid),
        .fub_axi_bresp           (fub_axi_bresp),
        .fub_axi_buser           (fub_axi_buser),
        .fub_axi_bvalid          (fub_axi_bvalid),
        .fub_axi_bready          (fub_axi_bready),

        // Master AXI Interface (Output Side)
        .m_axi_awid              (m_axi_awid),
        .m_axi_awaddr            (m_axi_awaddr),
        .m_axi_awlen             (m_axi_awlen),
        .m_axi_awsize            (m_axi_awsize),
        .m_axi_awburst           (m_axi_awburst),
        .m_axi_awlock            (m_axi_awlock),
        .m_axi_awcache           (m_axi_awcache),
        .m_axi_awprot            (m_axi_awprot),
        .m_axi_awqos             (m_axi_awqos),
        .m_axi_awregion          (m_axi_awregion),
        .m_axi_awuser            (m_axi_awuser),
        .m_axi_awvalid           (m_axi_awvalid),
        .m_axi_awready           (m_axi_awready),

        .m_axi_wdata             (m_axi_wdata),
        .m_axi_wstrb             (m_axi_wstrb),
        .m_axi_wlast             (m_axi_wlast),
        .m_axi_wuser             (m_axi_wuser),
        .m_axi_wvalid            (m_axi_wvalid),
        .m_axi_wready            (m_axi_wready),

        .m_axi_bid               (m_axi_bid),
        .m_axi_bresp             (m_axi_bresp),
        .m_axi_buser             (m_axi_buser),
        .m_axi_bvalid            (m_axi_bvalid),
        .m_axi_bready            (m_axi_bready),

        // Monitor Configuration
        .cfg_monitor_enable      (cfg_monitor_enable),
        .cfg_error_enable        (cfg_error_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_timeout_cycles      (cfg_timeout_cycles),
        .cfg_latency_threshold   (cfg_latency_threshold),

        // AXI Protocol Filtering Configuration
        .cfg_axi_pkt_mask        (cfg_axi_pkt_mask),
        .cfg_axi_err_select      (cfg_axi_err_select),
        .cfg_axi_error_mask      (cfg_axi_error_mask),
        .cfg_axi_timeout_mask    (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask      (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask     (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask       (cfg_axi_perf_mask),
        .cfg_axi_addr_mask       (cfg_axi_addr_mask),
        .cfg_axi_debug_mask      (cfg_axi_debug_mask),

        // Monitor Bus Output
        .monbus_valid            (monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),

        // Status outputs
        .busy                    (busy),
        .active_transactions     (active_transactions),
        .error_count             (error_count),
        .transaction_count       (transaction_count),

        // Configuration error flags
        .cfg_conflict_error      (cfg_conflict_error)
    );

endmodule : axi4_master_wr_mon_cg
