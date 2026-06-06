// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_rd_mon
// Purpose: AXI5 Master Read with Integrated Filtered Monitoring
//
// This module combines the standard axi5_master_rd module with an axi_monitor_filtered
// to provide comprehensive transaction monitoring with configurable packet filtering.
//
// Features:
// - Instantiates axi5_master_rd for core AXI5 functionality
// - Instantiates axi_monitor_filtered for transaction monitoring with filtering
// - 3-level filtering hierarchy: packet type, error routing, individual event masking
// - Monitor bus output for system-level monitoring
// - Configurable monitoring and filtering parameters
// - Error detection and timeout monitoring
// - Performance metrics collection
// - Configuration validation with error flagging
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_rd_mon
    import monitor_pkg::*;
#(
    // AXI5 Master parameters
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,
    parameter int AXI_CHUNKNUM_WIDTH = 4,

    // Feature enables
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    // Monitor parameters
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h01,
    parameter logic [15:0] AGENT_ID = 16'h000A,
    parameter int MAX_TRANSACTIONS  = 16,

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,
    parameter bit ADD_PIPELINE_STAGE = 0,

    // Reporter sub-block enables (default 1'b1 = legacy behavior). Set to 0
    // to drop the detection cone at synthesis via generate-if.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = 1'b1,

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI5 Interface (Input Side)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // AXI5 AR signals
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_arnsaid,
    input  logic                       fub_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_armecid,
    input  logic                       fub_axi_arunique,
    input  logic                       fub_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_artagop,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // AXI5 R signals
    output logic                       fub_axi_rtrace,
    output logic                       fub_axi_rpoison,
    output logic                       fub_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0] fub_axi_rchunkstrb,
    output logic [TW-1:0]              fub_axi_rtag,
    output logic                       fub_axi_rtagmatch,

    // Master AXI5 Interface (Output Side)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // AXI5 AR signals
    output logic [AXI_NSAID_WIDTH-1:0] m_axi_arnsaid,
    output logic                       m_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]  m_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0] m_axi_armecid,
    output logic                       m_axi_arunique,
    output logic                       m_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0] m_axi_artagop,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // AXI5 R signals
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

    // Monitor Configuration
    input  logic                       cfg_monitor_enable,
    input  logic                       cfg_error_enable,
    input  logic                       cfg_timeout_enable,
    input  logic                       cfg_perf_enable,
    input  logic [15:0]                cfg_timeout_cycles,
    input  logic [31:0]                cfg_latency_threshold,

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,
    input  logic [15:0]                cfg_axi_err_select,
    input  logic [15:0]                cfg_axi_error_mask,
    input  logic [15:0]                cfg_axi_timeout_mask,
    input  logic [15:0]                cfg_axi_compl_mask,
    input  logic [15:0]                cfg_axi_thresh_mask,
    input  logic [15:0]                cfg_axi_perf_mask,
    input  logic [15:0]                cfg_axi_addr_mask,
    input  logic [15:0]                cfg_axi_debug_mask,

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

    // Status outputs
    output logic                       busy,
    output logic [7:0]                 active_transactions,
    output logic [15:0]                error_count,
    output logic [31:0]                transaction_count,

    // Configuration error flags
    output logic                       cfg_conflict_error,

    // Performance window control (Stage A of perfmon RFC). Wrapper-level
    // ports pass straight through; the integrating block ties them off
    // (3'b111 + 0s) when perfmon is unused.
    input  logic [2:0]                 cfg_start_event_sel,
    input  logic [2:0]                 cfg_end_event_sel,
    input  logic                       cfg_start_trigger,
    input  logic                       cfg_end_trigger,
    input  logic                       cfg_window_force_close,

    // Performance window status (Stage A) + cycle buckets + counters (Stage B).
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

    // Monitor backpressure plumbing (see axi4_master_rd_mon for full rationale)
    logic w_core_fub_axi_arready;
    logic w_block_ready;

    // Instantiate AXI5 Master Read Core
    axi5_master_rd #(
        .SKID_DEPTH_AR       (SKID_DEPTH_AR),
        .SKID_DEPTH_R        (SKID_DEPTH_R),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH     (AXI_WSTRB_WIDTH),
        .AXI_NSAID_WIDTH     (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH      (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH     (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH       (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH     (AXI_TAGOP_WIDTH),
        .AXI_CHUNKNUM_WIDTH  (AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID        (ENABLE_NSAID),
        .ENABLE_TRACE        (ENABLE_TRACE),
        .ENABLE_MPAM         (ENABLE_MPAM),
        .ENABLE_MECID        (ENABLE_MECID),
        .ENABLE_UNIQUE       (ENABLE_UNIQUE),
        .ENABLE_CHUNKING     (ENABLE_CHUNKING),
        .ENABLE_MTE          (ENABLE_MTE),
        .ENABLE_POISON       (ENABLE_POISON)
    ) axi5_master_rd_inst (
        .aclk                (aclk),
        .aresetn             (aresetn),

        .fub_axi_arid        (fub_axi_arid),
        .fub_axi_araddr      (fub_axi_araddr),
        .fub_axi_arlen       (fub_axi_arlen),
        .fub_axi_arsize      (fub_axi_arsize),
        .fub_axi_arburst     (fub_axi_arburst),
        .fub_axi_arlock      (fub_axi_arlock),
        .fub_axi_arcache     (fub_axi_arcache),
        .fub_axi_arprot      (fub_axi_arprot),
        .fub_axi_arqos       (fub_axi_arqos),
        .fub_axi_aruser      (fub_axi_aruser),
        .fub_axi_arvalid     (fub_axi_arvalid),
        .fub_axi_arready     (w_core_fub_axi_arready),  // gated below
        .fub_axi_arnsaid     (fub_axi_arnsaid),
        .fub_axi_artrace     (fub_axi_artrace),
        .fub_axi_armpam      (fub_axi_armpam),
        .fub_axi_armecid     (fub_axi_armecid),
        .fub_axi_arunique    (fub_axi_arunique),
        .fub_axi_archunken   (fub_axi_archunken),
        .fub_axi_artagop     (fub_axi_artagop),

        .fub_axi_rid         (fub_axi_rid),
        .fub_axi_rdata       (fub_axi_rdata),
        .fub_axi_rresp       (fub_axi_rresp),
        .fub_axi_rlast       (fub_axi_rlast),
        .fub_axi_ruser       (fub_axi_ruser),
        .fub_axi_rvalid      (fub_axi_rvalid),
        .fub_axi_rready      (fub_axi_rready),
        .fub_axi_rtrace      (fub_axi_rtrace),
        .fub_axi_rpoison     (fub_axi_rpoison),
        .fub_axi_rchunkv     (fub_axi_rchunkv),
        .fub_axi_rchunknum   (fub_axi_rchunknum),
        .fub_axi_rchunkstrb  (fub_axi_rchunkstrb),
        .fub_axi_rtag        (fub_axi_rtag),
        .fub_axi_rtagmatch   (fub_axi_rtagmatch),

        .m_axi_arid          (m_axi_arid),
        .m_axi_araddr        (m_axi_araddr),
        .m_axi_arlen         (m_axi_arlen),
        .m_axi_arsize        (m_axi_arsize),
        .m_axi_arburst       (m_axi_arburst),
        .m_axi_arlock        (m_axi_arlock),
        .m_axi_arcache       (m_axi_arcache),
        .m_axi_arprot        (m_axi_arprot),
        .m_axi_arqos         (m_axi_arqos),
        .m_axi_aruser        (m_axi_aruser),
        .m_axi_arvalid       (m_axi_arvalid),
        .m_axi_arready       (m_axi_arready),
        .m_axi_arnsaid       (m_axi_arnsaid),
        .m_axi_artrace       (m_axi_artrace),
        .m_axi_armpam        (m_axi_armpam),
        .m_axi_armecid       (m_axi_armecid),
        .m_axi_arunique      (m_axi_arunique),
        .m_axi_archunken     (m_axi_archunken),
        .m_axi_artagop       (m_axi_artagop),

        .m_axi_rid           (m_axi_rid),
        .m_axi_rdata         (m_axi_rdata),
        .m_axi_rresp         (m_axi_rresp),
        .m_axi_rlast         (m_axi_rlast),
        .m_axi_ruser         (m_axi_ruser),
        .m_axi_rvalid        (m_axi_rvalid),
        .m_axi_rready        (m_axi_rready),
        .m_axi_rtrace        (m_axi_rtrace),
        .m_axi_rpoison       (m_axi_rpoison),
        .m_axi_rchunkv       (m_axi_rchunkv),
        .m_axi_rchunknum     (m_axi_rchunknum),
        .m_axi_rchunkstrb    (m_axi_rchunkstrb),
        .m_axi_rtag          (m_axi_rtag),
        .m_axi_rtagmatch     (m_axi_rtagmatch),

        .busy                (busy)
    );

    // Instantiate AXI Monitor with Filtering (optional, USE_MONITOR)
    if (USE_MONITOR) begin : gen_monitor
        axi_monitor_filtered #(
            .UNIT_ID             (UNIT_ID),
            .AGENT_ID            (AGENT_ID),
            .MAX_TRANSACTIONS    (MAX_TRANSACTIONS),
            .ADDR_WIDTH          (AW),
            .ID_WIDTH            (IW),
            .IS_READ             (1),
            .IS_AXI              (1),
            .ENABLE_PERF_PACKETS (1),
            .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
            .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
            .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
            .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
            .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
            .ENABLE_DEBUG_MODULE (0),
            .ENABLE_FILTERING    (ENABLE_FILTERING),
            .ADD_PIPELINE_STAGE  (ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES       (N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk                (aclk),
            .aresetn             (aresetn),
            .i_mon_time              (i_mon_time),

            .cmd_addr            (m_axi_araddr),
            .cmd_id              (m_axi_arid),
            .cmd_len             (m_axi_arlen),
            .cmd_size            (m_axi_arsize),
            .cmd_burst           (m_axi_arburst),
            .cmd_valid           (m_axi_arvalid),
            .cmd_ready           (m_axi_arready),

            .data_id             (m_axi_rid),
            .data_last           (m_axi_rlast),
            .data_resp           (m_axi_rresp),
            .data_valid          (m_axi_rvalid),
            .data_ready          (m_axi_rready),

            .resp_id             (m_axi_rid),
            .resp_code           (m_axi_rresp),
            .resp_valid          (m_axi_rvalid && m_axi_rlast),
            .resp_ready          (m_axi_rready),

            .cfg_freq_sel        (4'b0001),
            .cfg_addr_cnt        (4'd15),
            .cfg_data_cnt        (4'd15),
            .cfg_resp_cnt        (4'd15),
            .cfg_error_enable    (cfg_error_enable),
            .cfg_compl_enable    (cfg_monitor_enable),
            .cfg_threshold_enable(cfg_perf_enable),
            .cfg_timeout_enable  (cfg_timeout_enable),
            .cfg_perf_enable     (cfg_perf_enable),
            .cfg_debug_enable    (1'b0),
            .cfg_debug_level     (4'h0),
            .cfg_debug_mask      (16'h0),
            .cfg_active_trans_threshold(16'd8),
            .cfg_latency_threshold(cfg_latency_threshold),

            .cfg_axi_pkt_mask    (cfg_axi_pkt_mask),
            .cfg_axi_err_select  (cfg_axi_err_select),
            .cfg_axi_error_mask  (cfg_axi_error_mask),
            .cfg_axi_timeout_mask(cfg_axi_timeout_mask),
            .cfg_axi_compl_mask  (cfg_axi_compl_mask),
            .cfg_axi_thresh_mask (cfg_axi_thresh_mask),
            .cfg_axi_perf_mask   (cfg_axi_perf_mask),
            .cfg_axi_addr_mask   (cfg_axi_addr_mask),
            .cfg_axi_debug_mask  (cfg_axi_debug_mask),

            // Address-range checker configuration
            .cfg_addr_check_enable(cfg_addr_check_enable),
            .cfg_addr_range_enable(cfg_addr_range_enable),
            .cfg_addr_range_low  (cfg_addr_range_low),
            .cfg_addr_range_high (cfg_addr_range_high),

            .monbus_valid        (monbus_valid),
            .monbus_ready        (monbus_ready),
            .monbus_packet       (monbus_packet),
            .monbus_timestamp        (monbus_timestamp),

            // block_ready stalls new ARs at fub_axi_arready when the monitor
            // FIFO is full (wire ANDed into the wrapper output below).
            .block_ready         (w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy                (),
            /* verilator lint_on PINCONNECTEMPTY */
            .active_count        (active_transactions),

            .cfg_conflict_error  (cfg_conflict_error),

            // Performance window control + status (Stage A) + buckets (Stage B).
            .cfg_start_event_sel (cfg_start_event_sel),
            .cfg_end_event_sel   (cfg_end_event_sel),
            .cfg_start_trigger   (cfg_start_trigger),
            .cfg_end_trigger     (cfg_end_trigger),
            .cfg_window_force_close (cfg_window_force_close),
            .window_active       (window_active),
            .window_cycles       (window_cycles),
            .perf_prod_cycles    (perf_prod_cycles),
            .perf_bp_cycles      (perf_bp_cycles),
            .perf_starv_cycles   (perf_starv_cycles),
            .perf_idle_cycles    (perf_idle_cycles),
            .perf_beat_count     (perf_beat_count),
            .perf_byte_count     (perf_byte_count),
            .perf_burst_count    (perf_burst_count)

        );
    end else begin : gen_no_monitor
        assign monbus_valid        = 1'b0;
        assign monbus_packet       = '0;
        assign monbus_timestamp    = '0;
        assign active_transactions = 8'h0;
        assign cfg_conflict_error  = 1'b0;
        assign w_block_ready       = 1'b1;

        // Stage A/B perfmon outputs — tied to 0 when monitor disabled.
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

    // Placeholder counters (tied to 0 in both monitor-on and monitor-off cases)
    assign error_count = 16'h0;
    assign transaction_count = 32'h0;

endmodule : axi5_master_rd_mon
