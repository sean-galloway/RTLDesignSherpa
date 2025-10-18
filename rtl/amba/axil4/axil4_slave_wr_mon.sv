// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_slave_wr_mon
// Purpose: Axil4 Slave Wr Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXIL4 Slave Write with Integrated Filtered Monitoring
 *
 * This module combines the standard axil4_slave_wr module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring for AXI4-Lite slave write operations.
 *
 * Features:
 * - Instantiates axil4_slave_wr for core AXIL4 slave functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - Simplified monitoring for AXI4-Lite (single-beat, no burst, no ID reordering)
 * - Monitor bus output for system-level monitoring
 * - Error detection and timeout monitoring
 * - Configuration validation with error flagging
 *
 * Key Simplifications vs AXI4:
 * - No burst support (all transactions are single-beat)
 * - Fixed ID=0 (no ID reordering)
 * - Reduced MAX_TRANSACTIONS (typically 4-8 vs 16-32)
 * - No AWID, AWLEN, AWSIZE, AWBURST, BID, WLAST signals
 */
module axil4_slave_wr_mon
    import monitor_pkg::*;
#(
    // AXIL4 Slave parameters (passed through to axil4_slave_wr)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXIL_ADDR_WIDTH   = 32,
    parameter int AXIL_DATA_WIDTH   = 32,

    // Monitor parameters
    parameter int UNIT_ID           = 2,     // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 21,    // 8-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 8,     // Maximum outstanding transactions (reduced for AXIL)

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

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

    // Monitor Bus Output
    output logic                       monbus_valid,            // Monitor bus valid
    input  logic                       monbus_ready,            // Monitor bus ready
    output logic [63:0]                monbus_packet,           // Monitor packet

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // -------------------------------------------------------------------------
    // Instantiate AXIL4 Slave Write Core
    // -------------------------------------------------------------------------
    axil4_slave_wr #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXIL_ADDR_WIDTH         (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH         (AXIL_DATA_WIDTH)
    ) axil4_slave_wr_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXIL Interface (Input Side)
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

        // Master AXIL Interface (Output Side)
        .fub_awaddr              (fub_axil_awaddr),
        .fub_awprot              (fub_axil_awprot),
        .fub_awvalid             (fub_axil_awvalid),
        .fub_awready             (fub_axil_awready),

        .fub_wdata               (fub_axil_wdata),
        .fub_wstrb               (fub_axil_wstrb),
        .fub_wvalid              (fub_axil_wvalid),
        .fub_wready              (fub_axil_wready),

        .fub_bresp               (fub_axil_bresp),
        .fub_bvalid              (fub_axil_bvalid),
        .fub_bready              (fub_axil_bready),

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (Monitoring slave side - s_axil_* interface)
    // -------------------------------------------------------------------------
    axi_monitor_filtered #(
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ADDR_WIDTH              (AW),
        .ID_WIDTH                (1),                // Fixed ID width for AXIL
        .IS_READ                 (0),                // This is a write monitor
        .IS_AXI                  (1),                // AXI protocol (AXIL is subset)
        .ENABLE_PERF_PACKETS     (1),
        .ENABLE_DEBUG_MODULE     (0),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) axi_monitor_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Command interface (AW channel - monitoring slave side) - AXIL simplified
        .cmd_addr                (s_axil_awaddr),
        .cmd_id                  (1'b0),             // Fixed ID=0 for AXIL
        .cmd_len                 (8'h00),            // Single-beat: len=0
        .cmd_size                (3'b010),           // 4 bytes (32-bit)
        .cmd_burst               (2'b01),            // INCR burst type
        .cmd_valid               (s_axil_awvalid),
        .cmd_ready               (s_axil_awready),

        // Data interface (W channel - monitoring slave side) - AXIL simplified
        .data_id                 (1'b0),             // Fixed ID=0 for AXIL
        .data_last               (1'b1),             // Always last for AXIL
        .data_resp               (2'b00),            // Write data doesn't have response
        .data_valid              (s_axil_wvalid),
        .data_ready              (s_axil_wready),

        // Response interface (B channel - monitoring slave side)
        .resp_id                 (1'b0),             // Fixed ID=0 for AXIL
        .resp_code               (s_axil_bresp),
        .resp_valid              (s_axil_bvalid),
        .resp_ready              (s_axil_bready),

        // Configuration
        .cfg_freq_sel            (4'b0001),          // Use aclk frequency
        .cfg_addr_cnt            (4'd15),            // Count 16 address events
        .cfg_data_cnt            (4'd15),            // Count 16 data events
        .cfg_resp_cnt            (4'd15),            // Count 16 response events
        .cfg_error_enable        (cfg_error_enable),
        .cfg_compl_enable        (cfg_monitor_enable),
        .cfg_threshold_enable    (cfg_perf_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_debug_enable        (1'b0),            // Disable debug by default
        .cfg_debug_level         (4'h0),
        .cfg_debug_mask          (16'h0),
        .cfg_active_trans_threshold(16'd4),         // Alert if >4 active transactions (AXIL)
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

        // Monitor bus output
        .monbus_valid            (monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),

        // Status outputs
        /* verilator lint_off PINCONNECTEMPTY */
        .block_ready             (),                 // Unused
        .busy                    (),                 // Unused (using slave busy)
        /* verilator lint_on PINCONNECTEMPTY */
        .active_count            (active_transactions),

        // Configuration error flags
        .cfg_conflict_error      (cfg_conflict_error)
    );

    // Note: error_count and transaction_count are not directly available from axi_monitor_filtered
    // These would need to be implemented separately or the monitor would need enhancement
    assign error_count = 16'h0;         // Placeholder - not available from filtered monitor
    assign transaction_count = 32'h0;   // Placeholder - not available from filtered monitor

endmodule : axil4_slave_wr_mon
