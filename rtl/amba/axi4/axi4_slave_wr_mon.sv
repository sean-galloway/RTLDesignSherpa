// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_wr_mon
// Purpose: Axi4 Slave Wr Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Slave Write with Integrated Filtered Monitoring
 *
 * This module combines the standard axi4_slave_wr module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring with configurable packet filtering
 * for slave write operations.
 *
 * Features:
 * - Instantiates axi4_slave_wr for core AXI4 slave functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - 3-level filtering hierarchy: packet type, error routing, individual event masking
 * - Monitor bus output for system-level monitoring
 * - Configurable monitoring and filtering parameters
 * - Error detection and timeout monitoring
 * - Performance metrics collection
 * - Configuration validation with error flagging
 */
module axi4_slave_wr_mon
    import monitor_pkg::*;
#(
    // AXI4 Slave parameters (passed through to axi4_slave_wr)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters
    parameter int UNIT_ID           = 2,     // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 21,    // 8-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

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
    input  logic [IW-1:0]              s_axi_awid,
    input  logic [AW-1:0]              s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [UW-1:0]              s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              s_axi_wdata,
    input  logic [SW-1:0]              s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [UW-1:0]              s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [UW-1:0]              s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Master AXI Interface (Output Side to backend/memory)
    // Write address channel (AW)
    output logic [IW-1:0]              fub_axi_awid,
    output logic [AW-1:0]              fub_axi_awaddr,
    output logic [7:0]                 fub_axi_awlen,
    output logic [2:0]                 fub_axi_awsize,
    output logic [1:0]                 fub_axi_awburst,
    output logic                       fub_axi_awlock,
    output logic [3:0]                 fub_axi_awcache,
    output logic [2:0]                 fub_axi_awprot,
    output logic [3:0]                 fub_axi_awqos,
    output logic [3:0]                 fub_axi_awregion,
    output logic [UW-1:0]              fub_axi_awuser,
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              fub_axi_wdata,
    output logic [SW-1:0]              fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [UW-1:0]              fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [UW-1:0]              fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,

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

    // Monitor Bus Output
    output logic                       monbus_valid,            // Monitor bus valid
    input  logic                       monbus_ready,            // Monitor bus ready
    output logic [63:0]                monbus_packet,           // Monitor packet

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count (not available from base monitor)
    output logic [31:0]                transaction_count,       // Total transaction count (not available from base monitor)

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // -------------------------------------------------------------------------
    // Instantiate AXI4 Slave Write Core
    // -------------------------------------------------------------------------
    axi4_slave_wr #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH)
    ) axi4_slave_wr_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXI Interface (Input Side)
        .s_axi_awid              (s_axi_awid),
        .s_axi_awaddr            (s_axi_awaddr),
        .s_axi_awlen             (s_axi_awlen),
        .s_axi_awsize            (s_axi_awsize),
        .s_axi_awburst           (s_axi_awburst),
        .s_axi_awlock            (s_axi_awlock),
        .s_axi_awcache           (s_axi_awcache),
        .s_axi_awprot            (s_axi_awprot),
        .s_axi_awqos             (s_axi_awqos),
        .s_axi_awregion          (s_axi_awregion),
        .s_axi_awuser            (s_axi_awuser),
        .s_axi_awvalid           (s_axi_awvalid),
        .s_axi_awready           (s_axi_awready),

        .s_axi_wdata             (s_axi_wdata),
        .s_axi_wstrb             (s_axi_wstrb),
        .s_axi_wlast             (s_axi_wlast),
        .s_axi_wuser             (s_axi_wuser),
        .s_axi_wvalid            (s_axi_wvalid),
        .s_axi_wready            (s_axi_wready),

        .s_axi_bid               (s_axi_bid),
        .s_axi_bresp             (s_axi_bresp),
        .s_axi_buser             (s_axi_buser),
        .s_axi_bvalid            (s_axi_bvalid),
        .s_axi_bready            (s_axi_bready),

        // Master AXI Interface (Output Side)
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

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (Monitoring slave side - s_axi_* interface)
    // -------------------------------------------------------------------------
    axi_monitor_filtered #(
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ADDR_WIDTH              (AW),
        .ID_WIDTH                (IW),
        .IS_READ                 (0),                // This is a write monitor
        .IS_AXI                  (1),                // AXI4 protocol
        .ENABLE_PERF_PACKETS     (1),
        .ENABLE_DEBUG_MODULE     (0),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) axi_monitor_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Command interface (AW channel - monitoring slave side)
        .cmd_addr                (s_axi_awaddr),
        .cmd_id                  (s_axi_awid),
        .cmd_len                 (s_axi_awlen),
        .cmd_size                (s_axi_awsize),
        .cmd_burst               (s_axi_awburst),
        .cmd_valid               (s_axi_awvalid),
        .cmd_ready               (s_axi_awready),

        // Data interface (W channel - monitoring slave side)
        .data_id                 (s_axi_awid),       // Use AW ID for write data
        .data_last               (s_axi_wlast),
        .data_resp               (2'b00),            // Write data doesn't have response
        .data_valid              (s_axi_wvalid),
        .data_ready              (s_axi_wready),

        // Response interface (B channel - monitoring slave side)
        .resp_id                 (s_axi_bid),
        .resp_code               (s_axi_bresp),
        .resp_valid              (s_axi_bvalid),
        .resp_ready              (s_axi_bready),

        // Configuration
        .cfg_freq_sel            (4'b0001),            // Use aclk frequency
        .cfg_addr_cnt            (4'd15),              // Count 16 address events
        .cfg_data_cnt            (4'd15),              // Count 16 data events
        .cfg_resp_cnt            (4'd15),              // Count 16 response events
        .cfg_error_enable        (cfg_error_enable),
        .cfg_compl_enable        (cfg_monitor_enable),
        .cfg_threshold_enable    (cfg_perf_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_debug_enable        (1'b0),              // Disable debug by default
        .cfg_debug_level         (4'h0),
        .cfg_debug_mask          (16'h0),
        .cfg_active_trans_threshold(16'd8),           // Alert if >8 active transactions
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
        .block_ready             (),                    // Unused
        .busy                    (),                    // Unused (using slave busy)
        /* verilator lint_on PINCONNECTEMPTY */
        .active_count            (active_transactions),

        // Configuration error flags
        .cfg_conflict_error      (cfg_conflict_error)
    );

    // Note: error_count and transaction_count are not directly available from axi_monitor_filtered
    // These would need to be implemented separately or the monitor would need enhancement
    assign error_count = 16'h0;         // Placeholder - not available from filtered monitor
    assign transaction_count = 32'h0;   // Placeholder - not available from filtered monitor

endmodule : axi4_slave_wr_mon

