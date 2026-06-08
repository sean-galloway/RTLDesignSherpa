// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_slave_wr_mon_cg
// Purpose: Axil4 Slave Wr Mon Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXIL4 Slave Write with Integrated Filtered Monitoring and Clock Gating
 *
 * This module extends axil4_slave_wr_mon with comprehensive clock gating capabilities
 * for power optimization. This is a simple pass-through wrapper as the base monitor
 * already includes activity-based power management.
 *
 * Features:
 * - Instantiates axil4_slave_wr_mon for core functionality with filtering
 * - Activity-based clock gating for the monitor subsystem
 * - Simplified for AXIL4-Lite (lower activity than full AXI4)
 * - Fine-grained power management controls
 */

`include "reset_defs.svh"
module axil4_slave_wr_mon_cg
    import monitor_pkg::*;
#(
    // AXIL4 Slave parameters (passed through to axil4_slave_wr_mon)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXIL_ADDR_WIDTH   = 32,
    parameter int AXIL_DATA_WIDTH   = 32,

    // Monitor parameters
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor in inner mon; outputs tied
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h02,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h0015,    // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 8,     // Maximum outstanding transactions (reduced for AXIL)

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

    // Reporter sub-block enables (default 1'b1 = legacy behavior). Set to 0
    // to drop the detection cone at synthesis via generate-if.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

    // Clock gating parameters (for AXIL)
    parameter bit ENABLE_CLOCK_GATING = 1,   // Enable clock gating
    parameter int CG_IDLE_CYCLES    = 4,     // Cycles to wait before gating (lower for AXIL)

    // Short params
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXIL Interface (Input Side)
    // Write address channel (AW)
    input  logic [AW-1:0]              s_axil_awaddr,
    input  logic [2:0]                 s_axil_awprot,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              s_axil_wdata,
    input  logic [DW/8-1:0]            s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,

    // Write response channel (B)
    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    // Master AXIL Interface (Output Side to backend/memory)
    // Write address channel (AW)
    output logic [AW-1:0]              fub_axil_awaddr,
    output logic [2:0]                 fub_axil_awprot,
    output logic                       fub_axil_awvalid,
    input  logic                       fub_axil_awready,

    // Write data channel (W)
    output logic [DW-1:0]              fub_axil_wdata,
    output logic [DW/8-1:0]            fub_axil_wstrb,
    output logic                       fub_axil_wvalid,
    input  logic                       fub_axil_wready,

    // Write response channel (B)
    input  logic [1:0]                 fub_axil_bresp,
    input  logic                       fub_axil_bvalid,
    output logic                       fub_axil_bready,

    // Monitor Configuration
    input  logic                       cfg_monitor_enable,      // Enable monitoring
    input  logic                       cfg_error_enable,        // Enable error detection
    input  logic                       cfg_timeout_enable,      // Enable timeout detection
    input  logic                       cfg_perf_enable,         // Enable performance monitoring
    input  logic                       cfg_compl_enable,     // Enable completion packets
    input  logic                       cfg_threshold_enable, // Enable threshold packets
    input  logic                       cfg_debug_enable,     // Enable debug packets
    input  logic [15:0]                cfg_timeout_cycles,      // Timeout threshold in cycles
    input  logic [31:0]                cfg_latency_threshold,   // Latency threshold for alerts

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types
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

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Free-running monitor-time broadcast from monbus_axil_group
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Output
    output logic                                    monbus_valid,            // Monitor bus valid
    input  logic                                    monbus_ready,            // Monitor bus ready
    output monitor_common_pkg::monitor_packet_t     monbus_packet,           // Monitor packet (128-bit)
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,        // Side-band sampled time

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Clock gating status
    output logic [31:0]                cg_cycles_saved,         // Estimated cycles saved by gating

    // Configuration error flags
    output logic                       cfg_conflict_error,       // Configuration conflict detected

    // Performance window control (Stage A) + status (A) + buckets (B).
    input  logic [2:0]                 cfg_start_event_sel,
    input  logic [2:0]                 cfg_end_event_sel,
    input  logic                       cfg_start_trigger,
    input  logic                       cfg_end_trigger,
    input  logic                       cfg_window_force_close,
    output logic                       window_active,
    output logic [31:0]                window_cycles,
    output logic [31:0]                perf_prod_cycles,
    output logic [31:0]                perf_bp_cycles,
    output logic [31:0]                perf_starv_cycles,
    output logic [31:0]                perf_idle_cycles,
    output logic [31:0]                perf_beat_count,
    output logic [63:0]                perf_byte_count,
    output logic [31:0]                perf_burst_count
);

    // -------------------------------------------------------------------------
    // Instantiate AXIL4 Slave Write Monitor
    // -------------------------------------------------------------------------
    axil4_slave_wr_mon #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXIL_ADDR_WIDTH         (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH         (AXIL_DATA_WIDTH),
        .USE_MONITOR             (USE_MONITOR),
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
        .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
        .N_ADDR_RANGES           (N_ADDR_RANGES)
    ) axil4_slave_wr_mon_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),
        .i_mon_time              (i_mon_time),

        // Slave AXIL Interface
        .s_axil_awaddr           (s_axil_awaddr),
        .s_axil_awprot           (s_axil_awprot),
        .s_axil_awvalid          (s_axil_awvalid),
        .s_axil_awready          (s_axil_awready),

        .s_axil_wdata            (s_axil_wdata),
        .s_axil_wstrb            (s_axil_wstrb),
        .s_axil_wvalid           (s_axil_wvalid),
        .s_axil_wready           (s_axil_wready),

        .s_axil_bresp            (s_axil_bresp),
        .s_axil_bvalid           (s_axil_bvalid),
        .s_axil_bready           (s_axil_bready),

        // Master AXIL Interface
        .fub_axil_awaddr         (fub_axil_awaddr),
        .fub_axil_awprot         (fub_axil_awprot),
        .fub_axil_awvalid        (fub_axil_awvalid),
        .fub_axil_awready        (fub_axil_awready),

        .fub_axil_wdata          (fub_axil_wdata),
        .fub_axil_wstrb          (fub_axil_wstrb),
        .fub_axil_wvalid         (fub_axil_wvalid),
        .fub_axil_wready         (fub_axil_wready),

        .fub_axil_bresp          (fub_axil_bresp),
        .fub_axil_bvalid         (fub_axil_bvalid),
        .fub_axil_bready         (fub_axil_bready),

        // Monitor Configuration
        .cfg_monitor_enable      (cfg_monitor_enable & cfg_cg_enable),
        .cfg_error_enable        (cfg_error_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_compl_enable         (cfg_compl_enable),
        .cfg_threshold_enable         (cfg_threshold_enable),
        .cfg_debug_enable         (cfg_debug_enable),
        .cfg_timeout_cycles      (cfg_timeout_cycles),
        .cfg_latency_threshold   (cfg_latency_threshold),

        // Filtering Configuration
        .cfg_axi_pkt_mask        (cfg_axi_pkt_mask),
        .cfg_axi_err_select      (cfg_axi_err_select),
        .cfg_axi_error_mask      (cfg_axi_error_mask),
        .cfg_axi_timeout_mask    (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask      (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask     (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask       (cfg_axi_perf_mask),
        .cfg_axi_addr_mask       (cfg_axi_addr_mask),
        .cfg_axi_debug_mask      (cfg_axi_debug_mask),

        // Address-range checker configuration
        .cfg_addr_check_enable   (cfg_addr_check_enable),
        .cfg_addr_range_enable   (cfg_addr_range_enable),
        .cfg_addr_range_low      (cfg_addr_range_low),
        .cfg_addr_range_high     (cfg_addr_range_high),

        // Monitor Bus
        .monbus_valid            (monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),
        .monbus_timestamp        (monbus_timestamp),

        // Status
        .busy                    (busy),
        .active_transactions     (active_transactions),
        .error_count             (error_count),
        .transaction_count       (transaction_count),
        .cfg_conflict_error      (cfg_conflict_error),

        // Performance window control + status (Stage A) + buckets (Stage B).
        .cfg_start_event_sel     (cfg_start_event_sel),
        .cfg_end_event_sel       (cfg_end_event_sel),
        .cfg_start_trigger       (cfg_start_trigger),
        .cfg_end_trigger         (cfg_end_trigger),
        .cfg_window_force_close  (cfg_window_force_close),
        .window_active           (window_active),
        .window_cycles           (window_cycles),
        .perf_prod_cycles        (perf_prod_cycles),
        .perf_bp_cycles          (perf_bp_cycles),
        .perf_starv_cycles       (perf_starv_cycles),
        .perf_idle_cycles        (perf_idle_cycles),
        .perf_beat_count         (perf_beat_count),
        .perf_byte_count         (perf_byte_count),
        .perf_burst_count        (perf_burst_count)

    );

    // -------------------------------------------------------------------------
    // Clock Gating Statistics (Placeholder)
    // -------------------------------------------------------------------------
    logic [31:0] idle_cycles;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            idle_cycles <= '0;
        end else if (cfg_cg_enable && !busy) begin
            idle_cycles <= idle_cycles + 1'b1;
        end
    )


    assign cg_cycles_saved = idle_cycles;

endmodule : axil4_slave_wr_mon_cg
