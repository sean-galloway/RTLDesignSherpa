// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_slave_rd_mon
// Purpose: Axil4 Slave Rd Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXIL4 Slave Read with Integrated Filtered Monitoring
 *
 * This module combines the standard axil4_slave_rd module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring for AXI4-Lite slave read operations.
 *
 * Features:
 * - Instantiates axil4_slave_rd for core AXIL4 slave functionality
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
 * - No ARID, ARLEN, ARSIZE, ARBURST, RID, RLAST signals
 */
module axil4_slave_rd_mon
    import monitor_pkg::*;
#(
    // AXIL4 Slave parameters (passed through to axil4_slave_rd)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXIL_ADDR_WIDTH   = 32,
    parameter int AXIL_DATA_WIDTH   = 32,

    // Monitor parameters
    parameter int UNIT_ID           = 2,     // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 20,    // 8-bit Agent ID for monitor packets
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
    // Read address channel (AR)
    input  logic [AW-1:0]              s_axil_araddr,
    input  logic [2:0]                 s_axil_arprot,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,

    // Read data channel (R)
    output logic [DW-1:0]              s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // Master AXIL Interface (Output Side to backend/memory)
    // Read address channel (AR)
    output logic [AW-1:0]              fub_axil_araddr,
    output logic [2:0]                 fub_axil_arprot,
    output logic                       fub_axil_arvalid,
    input  logic                       fub_axil_arready,

    // Read data channel (R)
    input  logic [DW-1:0]              fub_axil_rdata,
    input  logic [1:0]                 fub_axil_rresp,
    input  logic                       fub_axil_rvalid,
    output logic                       fub_axil_rready,

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
    // Instantiate AXIL4 Slave Read Core
    // -------------------------------------------------------------------------
    axil4_slave_rd #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXIL_ADDR_WIDTH         (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH         (AXIL_DATA_WIDTH)
    ) axil4_slave_rd_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXIL Interface (Input Side)
        .s_axil_araddr           (s_axil_araddr),
        .s_axil_arprot           (s_axil_arprot),
        .s_axil_arvalid          (s_axil_arvalid),
        .s_axil_arready          (s_axil_arready),

        .s_axil_rdata            (s_axil_rdata),
        .s_axil_rresp            (s_axil_rresp),
        .s_axil_rvalid           (s_axil_rvalid),
        .s_axil_rready           (s_axil_rready),

        // Master AXIL Interface (Output Side)
        .fub_araddr              (fub_axil_araddr),
        .fub_arprot              (fub_axil_arprot),
        .fub_arvalid             (fub_axil_arvalid),
        .fub_arready             (fub_axil_arready),

        .fub_rdata               (fub_axil_rdata),
        .fub_rresp               (fub_axil_rresp),
        .fub_rvalid              (fub_axil_rvalid),
        .fub_rready              (fub_axil_rready),

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
        .IS_READ                 (1),                // This is a read monitor
        .IS_AXI                  (1),                // AXI protocol (AXIL is subset)
        .ENABLE_PERF_PACKETS     (1),
        .ENABLE_DEBUG_MODULE     (0),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) axi_monitor_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Command interface (AR channel - monitoring slave side) - AXIL simplified
        .cmd_addr                (s_axil_araddr),
        .cmd_id                  (1'b0),             // Fixed ID=0 for AXIL
        .cmd_len                 (8'h00),            // Single-beat: len=0
        .cmd_size                (3'b010),           // 4 bytes (32-bit)
        .cmd_burst               (2'b01),            // INCR burst type
        .cmd_valid               (s_axil_arvalid),
        .cmd_ready               (s_axil_arready),

        // Data interface (R channel - monitoring slave side) - AXIL simplified
        .data_id                 (1'b0),             // Fixed ID=0 for AXIL
        .data_last               (1'b1),             // Always last for AXIL
        .data_resp               (s_axil_rresp),
        .data_valid              (s_axil_rvalid),
        .data_ready              (s_axil_rready),

        // Response interface (same as data for AXIL reads)
        .resp_id                 (1'b0),             // Fixed ID=0 for AXIL
        .resp_code               (s_axil_rresp),
        .resp_valid              (s_axil_rvalid),    // Every data is also completion for AXIL
        .resp_ready              (s_axil_rready),

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

endmodule : axil4_slave_rd_mon
