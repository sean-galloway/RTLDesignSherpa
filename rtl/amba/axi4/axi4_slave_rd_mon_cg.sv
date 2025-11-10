// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_rd_mon_cg
// Purpose: Axi4 Slave Rd Mon Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Slave Read with Integrated Filtered Monitoring and Clock Gating
 *
 * This module extends axi4_slave_rd_mon with comprehensive clock gating capabilities
 * for power optimization. Features include:
 *
 * - Instantiates axi4_slave_rd_mon for core functionality with filtering
 * - Activity-based clock gating for the monitor subsystem
 * - Configurable clock gating policies and thresholds
 * - Independent gating for different monitor functions
 * - Performance monitoring with clock gating statistics
 * - Fine-grained power management controls
 */

`include "reset_defs.svh"
module axi4_slave_rd_mon_cg
    import monitor_pkg::*;
#(
    // AXI4 Slave parameters (passed through to axi4_slave_rd_mon)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters
    parameter int UNIT_ID           = 2,     // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 20,    // 8-bit Agent ID for monitor packets
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
    // Read address channel (AR)
    input  logic [IW-1:0]              s_axi_arid,
    input  logic [AW-1:0]              s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [UW-1:0]              s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              s_axi_rid,
    output logic [DW-1:0]              s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [UW-1:0]              s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Master AXI Interface (Output Side to backend/memory)
    // Read address channel (AR)
    output logic [IW-1:0]              fub_axi_arid,
    output logic [AW-1:0]              fub_axi_araddr,
    output logic [7:0]                 fub_axi_arlen,
    output logic [2:0]                 fub_axi_arsize,
    output logic [1:0]                 fub_axi_arburst,
    output logic                       fub_axi_arlock,
    output logic [3:0]                 fub_axi_arcache,
    output logic [2:0]                 fub_axi_arprot,
    output logic [3:0]                 fub_axi_arqos,
    output logic [3:0]                 fub_axi_arregion,
    output logic [UW-1:0]              fub_axi_aruser,
    output logic                       fub_axi_arvalid,
    input  logic                       fub_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              fub_axi_rid,
    input  logic [DW-1:0]              fub_axi_rdata,
    input  logic [1:0]                 fub_axi_rresp,
    input  logic                       fub_axi_rlast,
    input  logic [UW-1:0]              fub_axi_ruser,
    input  logic                       fub_axi_rvalid,
    output logic                       fub_axi_rready,

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
    // Clock Gating Logic
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

    // Detect AXI activity (slave side interfaces)
    assign axi_activity = (s_axi_arvalid && s_axi_arready) ||
                         (s_axi_rvalid && s_axi_rready) ||
                         (fub_axi_arvalid && fub_axi_arready) ||
                         (fub_axi_rvalid && fub_axi_rready);

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
    // Instantiate AXI4 Slave Read Monitor with Filtering
    // =========================================================================
    axi4_slave_rd_mon #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
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
    ) axi4_slave_rd_mon_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXI Interface (Input Side)
        .s_axi_arid              (s_axi_arid),
        .s_axi_araddr            (s_axi_araddr),
        .s_axi_arlen             (s_axi_arlen),
        .s_axi_arsize            (s_axi_arsize),
        .s_axi_arburst           (s_axi_arburst),
        .s_axi_arlock            (s_axi_arlock),
        .s_axi_arcache           (s_axi_arcache),
        .s_axi_arprot            (s_axi_arprot),
        .s_axi_arqos             (s_axi_arqos),
        .s_axi_arregion          (s_axi_arregion),
        .s_axi_aruser            (s_axi_aruser),
        .s_axi_arvalid           (s_axi_arvalid),
        .s_axi_arready           (s_axi_arready),

        .s_axi_rid               (s_axi_rid),
        .s_axi_rdata             (s_axi_rdata),
        .s_axi_rresp             (s_axi_rresp),
        .s_axi_rlast             (s_axi_rlast),
        .s_axi_ruser             (s_axi_ruser),
        .s_axi_rvalid            (s_axi_rvalid),
        .s_axi_rready            (s_axi_rready),

        // Master AXI Interface (Output Side)
        .fub_axi_arid            (fub_axi_arid),
        .fub_axi_araddr          (fub_axi_araddr),
        .fub_axi_arlen           (fub_axi_arlen),
        .fub_axi_arsize          (fub_axi_arsize),
        .fub_axi_arburst         (fub_axi_arburst),
        .fub_axi_arlock          (fub_axi_arlock),
        .fub_axi_arcache         (fub_axi_arcache),
        .fub_axi_arprot          (fub_axi_arprot),
        .fub_axi_arqos           (fub_axi_arqos),
        .fub_axi_arregion        (fub_axi_arregion),
        .fub_axi_aruser          (fub_axi_aruser),
        .fub_axi_arvalid         (fub_axi_arvalid),
        .fub_axi_arready         (fub_axi_arready),

        .fub_axi_rid             (fub_axi_rid),
        .fub_axi_rdata           (fub_axi_rdata),
        .fub_axi_rresp           (fub_axi_rresp),
        .fub_axi_rlast           (fub_axi_rlast),
        .fub_axi_ruser           (fub_axi_ruser),
        .fub_axi_rvalid          (fub_axi_rvalid),
        .fub_axi_rready          (fub_axi_rready),

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

endmodule : axi4_slave_rd_mon_cg
