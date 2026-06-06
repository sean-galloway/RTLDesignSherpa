// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_mon
// Purpose: Axi4 Master Wr Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Write with Integrated Filtered Monitoring
 *
 * This module combines the standard axi4_master_wr module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring with configurable packet filtering.
 *
 * Features:
 * - Instantiates axi4_master_wr for core AXI4 functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - 3-level filtering hierarchy: packet type, error routing, individual event masking
 * - Monitor bus output for system-level monitoring
 * - Configurable monitoring and filtering parameters
 * - Error detection and timeout monitoring
 * - Performance metrics collection
 * - Configuration validation with error flagging
 * - USE_MONITOR: synthesis-time enable. When 0, the monitor is omitted and
 *   its outputs are tied to safe non-blocking defaults so the wrapped
 *   axi4_master_wr core runs unencumbered (for FPGA / production / PPA
 *   characterization). Upstream macro wrappers may OR a force-on signal.
 */
module axi4_master_wr_mon
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (passed through to axi4_master_wr)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters (literals sized to 32 bits for Verilator int-parameter width check)
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h01,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h000B,  // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor

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

    // Performance cycle buckets + counters (Stage B of perfmon RFC).
    // Sample at WIN_CLOSING (drive cfg_end_trigger or wait for the
    // configured end event, then read on the cycle window_active=0).
    output logic [31:0]                perf_prod_cycles,
    output logic [31:0]                perf_bp_cycles,
    output logic [31:0]                perf_starv_cycles,
    output logic [31:0]                perf_idle_cycles,
    output logic [31:0]                perf_beat_count,
    output logic [63:0]                perf_byte_count,
    output logic [31:0]                perf_burst_count,

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // -------------------------------------------------------------------------
    // Monitor backpressure plumbing (see master_rd_mon for full rationale)
    // -------------------------------------------------------------------------
    logic w_core_fub_axi_awready;
    logic w_block_ready;

    // -------------------------------------------------------------------------
    // Instantiate AXI4 Master Write Core
    // -------------------------------------------------------------------------
    axi4_master_wr #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH)
    ) axi4_master_wr_inst (
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
        .fub_axi_awready         (w_core_fub_axi_awready),  // gated below

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

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (optional, USE_MONITOR)
    // -------------------------------------------------------------------------
    if (USE_MONITOR) begin : gen_monitor
        axi_monitor_filtered #(
            .UNIT_ID                 (UNIT_ID),
            .AGENT_ID                (AGENT_ID),
            .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
            .ADDR_WIDTH              (AW),
            .ID_WIDTH                (IW),
            .IS_READ                 (1'b0),             // This is a write monitor
            .IS_AXI                  (1'b1),             // AXI4 protocol
            .ENABLE_PERF_PACKETS     (1'b1),
            .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
            .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
            .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
            .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
            .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
            .ENABLE_DEBUG_MODULE     (1'b0),
            .ENABLE_FILTERING        (ENABLE_FILTERING),
            .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES           (N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk                    (aclk),
            .aresetn                 (aresetn),
            .i_mon_time              (i_mon_time),

            // Command interface (AW channel)
            .cmd_addr                (m_axi_awaddr),
            .cmd_id                  (m_axi_awid),
            .cmd_len                 (m_axi_awlen),
            .cmd_size                (m_axi_awsize),
            .cmd_burst               (m_axi_awburst),
            .cmd_valid               (m_axi_awvalid),
            .cmd_ready               (m_axi_awready),

            // Data interface (W channel)
            .data_id                 (m_axi_awid),       // Use AW ID for write data
            .data_last               (m_axi_wlast),
            .data_resp               (2'b00),            // No response in W channel
            .data_valid              (m_axi_wvalid),
            .data_ready              (m_axi_wready),

            // Response interface (B channel)
            .resp_id                 (m_axi_bid),
            .resp_code               (m_axi_bresp),
            .resp_valid              (m_axi_bvalid),
            .resp_ready              (m_axi_bready),

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
            // block_ready stalls new AWs at fub_axi_awready when the monitor
            // FIFO is full (wire ANDed into the wrapper output below).
            .block_ready             (w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy                    (),                    // Unused (using master busy)
            /* verilator lint_on PINCONNECTEMPTY */
            .window_active           (window_active),
            .window_cycles           (window_cycles),
            .perf_prod_cycles        (perf_prod_cycles),
            .perf_bp_cycles          (perf_bp_cycles),
            .perf_starv_cycles       (perf_starv_cycles),
            .perf_idle_cycles        (perf_idle_cycles),
            .perf_beat_count         (perf_beat_count),
            .perf_byte_count         (perf_byte_count),
            .perf_burst_count        (perf_burst_count),
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
        assign perf_prod_cycles    = 32'h0;
        assign perf_bp_cycles      = 32'h0;
        assign perf_starv_cycles   = 32'h0;
        assign perf_idle_cycles    = 32'h0;
        assign perf_beat_count     = 32'h0;
        assign perf_byte_count     = 64'h0;
        assign perf_burst_count    = 32'h0;
    end

    // Gate the upstream AW handshake on monitor block_ready.
    assign fub_axi_awready = w_core_fub_axi_awready & w_block_ready;

    // error_count / transaction_count: not exposed by axi_monitor_filtered;
    // tied to 0 in both monitor-on and monitor-off cases.
    assign error_count = 16'h0;
    assign transaction_count = 32'h0;

endmodule : axi4_master_wr_mon

