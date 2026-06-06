// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_rd_mon
// Purpose: Axi4 Slave Rd Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Slave Read with Integrated Filtered Monitoring
 *
 * This module combines the standard axi4_slave_rd module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring with configurable packet filtering
 * for slave read operations.
 *
 * Features:
 * - Instantiates axi4_slave_rd for core AXI4 slave functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - 3-level filtering hierarchy: packet type, error routing, individual event masking
 * - Monitor bus output for system-level monitoring
 * - Configurable monitoring and filtering parameters
 * - Error detection and timeout monitoring
 * - Performance metrics collection
 * - Configuration validation with error flagging
 */
module axi4_slave_rd_mon
    import monitor_pkg::*;
#(
    // AXI4 Slave parameters (passed through to axi4_slave_rd)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters (literals sized to 32 bits for Verilator int-parameter width check)
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h02,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h0014,    // 16-bit Agent ID for monitor packets
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

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Performance window control (Stage A of perfmon RFC). Wire to the
    // integrating block's perfmon CSR; tie 3'b111 + 1'b0 if perfmon is
    // unused at this instance.
    input  logic [2:0]                              cfg_start_event_sel,
    input  logic [2:0]                              cfg_end_event_sel,
    input  logic                                    cfg_start_trigger,
    input  logic                                    cfg_end_trigger,
    input  logic                                    cfg_window_force_close,

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
    output logic [15:0]                error_count,             // Total error count (not available from base monitor)
    output logic [31:0]                transaction_count,       // Total transaction count (not available from base monitor)

    // Performance window status (Stage A of perfmon RFC). Reflects the
    // internal axi_monitor_base state machine.
    output logic                       window_active,
    output logic [31:0]                window_cycles,

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // -------------------------------------------------------------------------
    // Monitor backpressure plumbing (see axi4_master_rd_mon for full rationale)
    // -------------------------------------------------------------------------
    logic w_core_s_axi_arready;
    logic w_block_ready;

    // -------------------------------------------------------------------------
    // Instantiate AXI4 Slave Read Core
    // -------------------------------------------------------------------------
    axi4_slave_rd #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH)
    ) axi4_slave_rd_inst (
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
        .s_axi_arready           (w_core_s_axi_arready),    // gated below

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

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (Monitoring slave side - s_axi_* interface)
    // -------------------------------------------------------------------------
    // USE_MONITOR=1: filtered monitor is instantiated. USE_MONITOR=0: omitted
    // and outputs tied to non-blocking defaults.
    if (USE_MONITOR) begin : gen_monitor
        axi_monitor_filtered #(
            .UNIT_ID                 (UNIT_ID),
            .AGENT_ID                (AGENT_ID),
            .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
            .ADDR_WIDTH              (AW),
            .ID_WIDTH                (IW),
            .IS_READ                 (1'b1),             // This is a read monitor
            .IS_AXI                  (1'b1),             // AXI4 protocol
            .ENABLE_PERF_PACKETS     (1'b1),
            .ENABLE_DEBUG_MODULE     (1'b0),
            .ENABLE_FILTERING        (ENABLE_FILTERING),
            .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES           (N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk                    (aclk),
            .aresetn                 (aresetn),
            .i_mon_time              (i_mon_time),

            // Command interface (AR channel - monitoring slave side)
            .cmd_addr                (s_axi_araddr),
            .cmd_id                  (s_axi_arid),
            .cmd_len                 (s_axi_arlen),
            .cmd_size                (s_axi_arsize),
            .cmd_burst               (s_axi_arburst),
            .cmd_valid               (s_axi_arvalid),
            .cmd_ready               (s_axi_arready),

            // Data interface (R channel - monitoring slave side)
            .data_id                 (s_axi_rid),
            .data_last               (s_axi_rlast),
            .data_resp               (s_axi_rresp),
            .data_valid              (s_axi_rvalid),
            .data_ready              (s_axi_rready),

            // Response interface (same as data for reads)
            .resp_id                 (s_axi_rid),
            .resp_code               (s_axi_rresp),
            .resp_valid              (s_axi_rvalid && s_axi_rlast),
            .resp_ready              (s_axi_rready),

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

            // Address-range checker configuration
            .cfg_addr_check_enable   (cfg_addr_check_enable),
            .cfg_addr_range_enable   (cfg_addr_range_enable),
            .cfg_addr_range_low      (cfg_addr_range_low),
            .cfg_addr_range_high     (cfg_addr_range_high),

            // Performance window control (Stage A of perfmon RFC).
            // Wrapper-level ports pass straight through; the integrating
            // block ties them off (3'b111 + 0s) when perfmon is unused.
            .cfg_start_event_sel     (cfg_start_event_sel),
            .cfg_end_event_sel       (cfg_end_event_sel),
            .cfg_start_trigger       (cfg_start_trigger),
            .cfg_end_trigger         (cfg_end_trigger),
            .cfg_window_force_close  (cfg_window_force_close),

            // Monitor bus output
            .monbus_valid            (monbus_valid),
            .monbus_ready            (monbus_ready),
            .monbus_packet           (monbus_packet),
            .monbus_timestamp        (monbus_timestamp),

            // Status outputs
            // block_ready stalls new ARs at s_axi_arready when the monitor
            // FIFO is full (wire ANDed into the wrapper output below).
            .block_ready             (w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy                    (),                    // Unused (using slave busy)
            /* verilator lint_on PINCONNECTEMPTY */
            .window_active           (window_active),
            .window_cycles           (window_cycles),
            .active_count            (active_transactions),

            // Configuration error flags
            .cfg_conflict_error      (cfg_conflict_error)
        );
    end else begin : gen_no_monitor
        assign monbus_valid        = 1'b0;
        assign monbus_packet       = '0;
        assign monbus_timestamp    = '0;
        assign active_transactions = 8'h0;
        assign cfg_conflict_error  = 1'b0;
        assign w_block_ready       = 1'b1;
        // Perfmon disabled when ENABLE_MONITOR=0.
        assign window_active       = 1'b0;
        assign window_cycles       = 32'h0;
    end

    // Gate the upstream AR handshake on monitor block_ready.
    assign s_axi_arready = w_core_s_axi_arready & w_block_ready;

    // error_count / transaction_count: not exposed by axi_monitor_filtered;
    // tied to 0 in both monitor-on and monitor-off cases.
    assign error_count = 16'h0;
    assign transaction_count = 32'h0;

endmodule : axi4_slave_rd_mon

