// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd_mon
// Purpose: Axi4 Master Rd Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Read with Integrated Filtered Monitoring
 *
 * This module combines the standard axi4_master_rd module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring with configurable packet filtering.
 *
 * Features:
 * - Instantiates axi4_master_rd for core AXI4 functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - 3-level filtering hierarchy: packet type, error routing, individual event masking
 * - Monitor bus output for system-level monitoring
 * - Configurable monitoring and filtering parameters
 * - Error detection and timeout monitoring
 * - Performance metrics collection
 * - Configuration validation with error flagging
 * - USE_MONITOR: synthesis-time enable. When 0, the monitor is omitted and
 *   its outputs are tied to safe non-blocking defaults so the wrapped
 *   axi4_master_rd core runs unencumbered (for FPGA / production / PPA
 *   characterization). Upstream macro wrappers may OR a force-on signal.
 */
module axi4_master_rd_mon
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (passed through to axi4_master_rd)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters
    // Literals explicitly sized to 32 bits to satisfy Verilator's
    // int-parameter width checks.
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h01,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h000A,  // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

    // Reporter sub-block enables (default 1'b1 = legacy behavior). Setting any
    // to 0 drops the corresponding detection cone at synthesis time via
    // generate-if inside axi_monitor_reporter — area saving is real.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

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
    input  logic                       cam_clear,  // sync clear of the monitor trans CAM

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [3:0]                 fub_axi_arregion,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

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

    // Free-running monitor-time broadcast from the monbus_group family
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
    // Monitor backpressure plumbing
    // -------------------------------------------------------------------------
    // The monitor exposes block_ready: high while its internal FIFO can
    // accept a new in-flight transaction, low when it's saturated. We
    // intercept the core's fub_axi_arready and AND it with block_ready so
    // a saturated monitor stalls new ARs at the upstream handshake instead
    // of silently losing events. With USE_MONITOR=0 the no-monitor branch
    // forces w_block_ready=1 (no stall, full bandwidth).
    logic w_core_fub_axi_arready;
    logic w_block_ready;

    // -------------------------------------------------------------------------
    // Instantiate AXI4 Master Read Core
    // -------------------------------------------------------------------------
    axi4_master_rd #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH)
    ) axi4_master_rd_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXI Interface (Input Side)
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
        .fub_axi_arready         (w_core_fub_axi_arready),  // gated below

        .fub_axi_rid             (fub_axi_rid),
        .fub_axi_rdata           (fub_axi_rdata),
        .fub_axi_rresp           (fub_axi_rresp),
        .fub_axi_rlast           (fub_axi_rlast),
        .fub_axi_ruser           (fub_axi_ruser),
        .fub_axi_rvalid          (fub_axi_rvalid),
        .fub_axi_rready          (fub_axi_rready),

        // Master AXI Interface (Output Side)
        .m_axi_arid              (m_axi_arid),
        .m_axi_araddr            (m_axi_araddr),
        .m_axi_arlen             (m_axi_arlen),
        .m_axi_arsize            (m_axi_arsize),
        .m_axi_arburst           (m_axi_arburst),
        .m_axi_arlock            (m_axi_arlock),
        .m_axi_arcache           (m_axi_arcache),
        .m_axi_arprot            (m_axi_arprot),
        .m_axi_arqos             (m_axi_arqos),
        .m_axi_arregion          (m_axi_arregion),
        .m_axi_aruser            (m_axi_aruser),
        .m_axi_arvalid           (m_axi_arvalid),
        .m_axi_arready           (m_axi_arready),

        .m_axi_rid               (m_axi_rid),
        .m_axi_rdata             (m_axi_rdata),
        .m_axi_rresp             (m_axi_rresp),
        .m_axi_rlast             (m_axi_rlast),
        .m_axi_ruser             (m_axi_ruser),
        .m_axi_rvalid            (m_axi_rvalid),
        .m_axi_rready            (m_axi_rready),

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (optional)
    // -------------------------------------------------------------------------
    // USE_MONITOR=1: filtered monitor is instantiated, drives monbus_*,
    //                active_transactions, cfg_conflict_error.
    // USE_MONITOR=0: monitor omitted; outputs tied to safe defaults. The
    //                monitor here is a snooper only — it does not gate the
    //                AXI path — so disabling has no functional effect on
    //                the wrapped axi4_master_rd core.
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
            .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
            .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
            .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
            .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
            .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
            .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
            .ENABLE_FILTERING        (ENABLE_FILTERING),
            .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES           (N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk                    (aclk),
            .aresetn                 (aresetn),
            .clear                   (cam_clear),
            .i_mon_time              (i_mon_time),

            // Command interface (AR channel)
            .cmd_addr                (m_axi_araddr),
            .cmd_id                  (m_axi_arid),
            .cmd_len                 (m_axi_arlen),
            .cmd_size                (m_axi_arsize),
            .cmd_burst               (m_axi_arburst),
            .cmd_valid               (m_axi_arvalid),
            .cmd_ready               (m_axi_arready),

            // Data interface (R channel)
            .data_id                 (m_axi_rid),
            .data_last               (m_axi_rlast),
            .data_resp               (m_axi_rresp),
            .data_valid              (m_axi_rvalid),
            .data_ready              (m_axi_rready),

            // Response interface (same as data for reads)
            .resp_id                 (m_axi_rid),
            .resp_code               (m_axi_rresp),
            .resp_valid              (m_axi_rvalid && m_axi_rlast),
            .resp_ready              (m_axi_rready),

            // Configuration
            .cfg_freq_sel            (4'b0001),            // Use aclk frequency
            .cfg_addr_cnt            (4'd15),              // Count 16 address events
            .cfg_data_cnt            (4'd15),              // Count 16 data events
            .cfg_resp_cnt            (4'd15),              // Count 16 response events
            .cfg_error_enable        (cfg_error_enable),
            .cfg_compl_enable        (cfg_compl_enable),
            .cfg_threshold_enable    (cfg_threshold_enable),
            .cfg_timeout_enable      (cfg_timeout_enable),
            .cfg_perf_enable         (cfg_perf_enable),
            .cfg_debug_enable        (cfg_debug_enable),
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
            // block_ready stalls new ARs at fub_axi_arready when the
            // monitor FIFO is full (wire ANDed into the wrapper output
            // below). busy is unused (the master core provides it).
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
        // Tie monitor outputs to safe defaults so consumers see "nothing to
        // report" and never stall. monbus_ready is an input — nothing to drive.
        // w_block_ready=1 → no monitor backpressure → wrapper runs at full BW.
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

    // Gate the upstream AR handshake on monitor block_ready.
    assign fub_axi_arready = w_core_fub_axi_arready & w_block_ready;

    // Note: error_count and transaction_count are not directly available from
    // axi_monitor_filtered; they are tied to 0 in both monitor-on and
    // monitor-off cases (would need a monitor-side counter to populate).
    assign error_count = 16'h0;
    assign transaction_count = 32'h0;

endmodule : axi4_master_rd_mon
