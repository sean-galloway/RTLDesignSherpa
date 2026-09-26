// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_wr_monlite
// Purpose: AXI5 Master Write with the lite monitor (axi_monitor_lite) -- axi5_master_wr plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/axi5/axi5_master_wr_monlite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axi5_master_wr_mon (amba/monitor-lite TASK-001). Same
// core, same taps, same 128-bit packets on the same monbus with the same
// UNIT/AGENT ids, so the arbiter, group and host tooling cannot tell the two
// apart. Different interface: only what the lite can honour is on the port
// list -- no perf window, no debug, no address-range checker, no ID/address
// filters, no per-event masks -- and two status outputs the full monitor
// does not have (dropped_count, refused_count). The lite never stalls the
// port: an event it cannot deliver is dropped and counted, and a command
// that finds no free table entry is counted and left untracked (its beats
// then report as ORPHAN errors). There is no block_ready and no gating of
// the command handshake; the core's ready goes straight to the port.
//
// Every core parameter and port is declared here verbatim from axi5_master_wr
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axi5_master_wr_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h01,
    parameter logic [15:0] AGENT_ID               = 16'h000B,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          N_ADDR_RANGES          = 0,      // address-range checker windows; 0 = not built
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,  // per range: 1 = miss is an error, 0 = hit is a match
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi5_master_wr) ----

    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_ATOP_WIDTH    = 6,      // Atomic operation width
    parameter int AXI_NSAID_WIDTH   = 4,      // Non-secure access ID width
    parameter int AXI_MPAM_WIDTH    = 11,     // MPAM width (PartID + PMG)
    parameter int AXI_MECID_WIDTH   = 16,     // Memory encryption context ID width
    parameter int AXI_TAG_WIDTH     = 4,      // Memory tag width per 16 bytes
    parameter int AXI_TAGOP_WIDTH   = 2,      // Tag operation width

    // Feature enables (set to 0 to disable optional signals)
    parameter bit ENABLE_ATOMIC     = 1,
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_MTE        = 1,      // Memory Tagging Extension
    parameter bit ENABLE_POISON     = 1,

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    // Number of tags based on data width (1 tag per 16 bytes)
    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,

    // AW channel packet size calculation
    // Base: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER
    // AXI5: + ATOP + NSAID + TRACE + MPAM + MECID + UNIQUE + TAGOP + TAG
    parameter int AWSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_ATOMIC ? AXI_ATOP_WIDTH : 0) +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_MTE ? (AXI_TAGOP_WIDTH + TW) : 0),

    // W channel packet size calculation
    // Base: DATA + STRB + LAST + USER
    // AXI5: + POISON + TAG + TAGUPDATE
    parameter int WSize    = DW + SW + 1 + UW +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_MTE ? (TW + NUM_TAGS) : 0),

    // B channel packet size calculation
    // Base: ID + RESP + USER
    // AXI5: + TRACE + TAG + TAGMATCH
    parameter int BSize    = IW + 2 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side - FUB/Functional Unit Block)
    // =========================================================================

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
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // AXI5 AW channel signals
    input  logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,     // Atomic operation
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,    // Non-secure access ID
    input  logic                       fub_axi_awtrace,    // Trace signal
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,     // Memory partitioning
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,    // Memory encryption context
    input  logic                       fub_axi_awunique,   // Unique ID indicator
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,    // Tag operation (MTE)
    input  logic [TW-1:0]              fub_axi_awtag,      // Address memory tags

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // AXI5 W channel signals
    input  logic                       fub_axi_wpoison,    // Data poison indicator
    input  logic [TW-1:0]              fub_axi_wtag,       // Write data tags
    input  logic [NUM_TAGS-1:0]        fub_axi_wtagupdate, // Tag update mask

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // AXI5 B channel signals
    output logic                       fub_axi_btrace,     // Response trace
    output logic [TW-1:0]              fub_axi_btag,       // Response tags
    output logic                       fub_axi_btagmatch,  // Tag match response

    // =========================================================================
    // Master AXI5 Interface (Output Side)
    // =========================================================================

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
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // AXI5 AW channel signals
    output logic [AXI_ATOP_WIDTH-1:0]  m_axi_awatop,
    output logic [AXI_NSAID_WIDTH-1:0] m_axi_awnsaid,
    output logic                       m_axi_awtrace,
    output logic [AXI_MPAM_WIDTH-1:0]  m_axi_awmpam,
    output logic [AXI_MECID_WIDTH-1:0] m_axi_awmecid,
    output logic                       m_axi_awunique,
    output logic [AXI_TAGOP_WIDTH-1:0] m_axi_awtagop,
    output logic [TW-1:0]              m_axi_awtag,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // AXI5 W channel signals
    output logic                       m_axi_wpoison,
    output logic [TW-1:0]              m_axi_wtag,
    output logic [NUM_TAGS-1:0]        m_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // AXI5 B channel signals
    input  logic                       m_axi_btrace,
    input  logic [TW-1:0]              m_axi_btag,
    input  logic                       m_axi_btagmatch,

    // Status outputs for clock gating
    output logic                       busy,

    // ---- Monitor control (the lite's own set: nothing here it cannot honour) ----
    input  logic                                  cam_clear,           // sync clear of the monitor's table (named as on the _mon wrapper: pin-compatible)
    input  logic                                  cfg_monitor_enable,  // 0 = monitor inert, table held clear
    input  logic                                  cfg_error_enable,
    input  logic                                  cfg_timeout_enable,
    input  logic                                  cfg_compl_enable,
    input  logic                                  cfg_threshold_enable,
    input  logic [15:0]                           cfg_timeout_cycles,  // MICROSECONDS of no progress; 0 = never
    input  logic [3:0]                            cfg_freq_sel,        // counter_freq_invariant LUT index
    input  logic [15:0]                           cfg_axi_pkt_mask,    // drop mask by packet type
    input  logic [31:0]                           cfg_latency_threshold, // completion latency (cycles) above this -> Threshold/LATENCY
    // ---- Address-range checker (built when N_ADDR_RANGES > 0) ----
    input  logic                                  cfg_addr_check_enable,
    input  logic                                  cfg_addr_match_enable, // hit in a match range -> AddrMatch packet
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,
    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Monitor bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,
    // ---- Status ----
    output logic [7:0]                            active_transactions, // entries in the table
    output logic [15:0]                           error_count,         // error + timeout packets emitted
    output logic [31:0]                           transaction_count,   // completion packets emitted
    output logic [15:0]                           dropped_count,       // events lost to monbus backpressure since the last report
    output logic [15:0]                           refused_count        // commands that found no free table entry
);

    // ------------------------------------------------------------------------
    // The core, passed through untouched (no monitor gating on any handshake)
    // ------------------------------------------------------------------------
    axi5_master_wr #(
        .SKID_DEPTH_AW               (SKID_DEPTH_AW),
        .SKID_DEPTH_W                (SKID_DEPTH_W),
        .SKID_DEPTH_B                (SKID_DEPTH_B),
        .AXI_ID_WIDTH                (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH              (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH              (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH              (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH             (AXI_WSTRB_WIDTH),
        .AXI_ATOP_WIDTH              (AXI_ATOP_WIDTH),
        .AXI_NSAID_WIDTH             (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH              (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH             (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH               (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH             (AXI_TAGOP_WIDTH),
        .ENABLE_ATOMIC               (ENABLE_ATOMIC),
        .ENABLE_NSAID                (ENABLE_NSAID),
        .ENABLE_TRACE                (ENABLE_TRACE),
        .ENABLE_MPAM                 (ENABLE_MPAM),
        .ENABLE_MECID                (ENABLE_MECID),
        .ENABLE_UNIQUE               (ENABLE_UNIQUE),
        .ENABLE_MTE                  (ENABLE_MTE),
        .ENABLE_POISON               (ENABLE_POISON),
        .AW                          (AW),
        .DW                          (DW),
        .IW                          (IW),
        .SW                          (SW),
        .UW                          (UW),
        .NUM_TAGS                    (NUM_TAGS),
        .TW                          (TW),
        .AWSize                      (AWSize),
        .WSize                       (WSize),
        .BSize                       (BSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .fub_axi_awid                (fub_axi_awid),
        .fub_axi_awaddr              (fub_axi_awaddr),
        .fub_axi_awlen               (fub_axi_awlen),
        .fub_axi_awsize              (fub_axi_awsize),
        .fub_axi_awburst             (fub_axi_awburst),
        .fub_axi_awlock              (fub_axi_awlock),
        .fub_axi_awcache             (fub_axi_awcache),
        .fub_axi_awprot              (fub_axi_awprot),
        .fub_axi_awqos               (fub_axi_awqos),
        .fub_axi_awuser              (fub_axi_awuser),
        .fub_axi_awvalid             (fub_axi_awvalid),
        .fub_axi_awready             (fub_axi_awready),
        .fub_axi_awatop              (fub_axi_awatop),
        .fub_axi_awnsaid             (fub_axi_awnsaid),
        .fub_axi_awtrace             (fub_axi_awtrace),
        .fub_axi_awmpam              (fub_axi_awmpam),
        .fub_axi_awmecid             (fub_axi_awmecid),
        .fub_axi_awunique            (fub_axi_awunique),
        .fub_axi_awtagop             (fub_axi_awtagop),
        .fub_axi_awtag               (fub_axi_awtag),
        .fub_axi_wdata               (fub_axi_wdata),
        .fub_axi_wstrb               (fub_axi_wstrb),
        .fub_axi_wlast               (fub_axi_wlast),
        .fub_axi_wuser               (fub_axi_wuser),
        .fub_axi_wvalid              (fub_axi_wvalid),
        .fub_axi_wready              (fub_axi_wready),
        .fub_axi_wpoison             (fub_axi_wpoison),
        .fub_axi_wtag                (fub_axi_wtag),
        .fub_axi_wtagupdate          (fub_axi_wtagupdate),
        .fub_axi_bid                 (fub_axi_bid),
        .fub_axi_bresp               (fub_axi_bresp),
        .fub_axi_buser               (fub_axi_buser),
        .fub_axi_bvalid              (fub_axi_bvalid),
        .fub_axi_bready              (fub_axi_bready),
        .fub_axi_btrace              (fub_axi_btrace),
        .fub_axi_btag                (fub_axi_btag),
        .fub_axi_btagmatch           (fub_axi_btagmatch),
        .m_axi_awid                  (m_axi_awid),
        .m_axi_awaddr                (m_axi_awaddr),
        .m_axi_awlen                 (m_axi_awlen),
        .m_axi_awsize                (m_axi_awsize),
        .m_axi_awburst               (m_axi_awburst),
        .m_axi_awlock                (m_axi_awlock),
        .m_axi_awcache               (m_axi_awcache),
        .m_axi_awprot                (m_axi_awprot),
        .m_axi_awqos                 (m_axi_awqos),
        .m_axi_awuser                (m_axi_awuser),
        .m_axi_awvalid               (m_axi_awvalid),
        .m_axi_awready               (m_axi_awready),
        .m_axi_awatop                (m_axi_awatop),
        .m_axi_awnsaid               (m_axi_awnsaid),
        .m_axi_awtrace               (m_axi_awtrace),
        .m_axi_awmpam                (m_axi_awmpam),
        .m_axi_awmecid               (m_axi_awmecid),
        .m_axi_awunique              (m_axi_awunique),
        .m_axi_awtagop               (m_axi_awtagop),
        .m_axi_awtag                 (m_axi_awtag),
        .m_axi_wdata                 (m_axi_wdata),
        .m_axi_wstrb                 (m_axi_wstrb),
        .m_axi_wlast                 (m_axi_wlast),
        .m_axi_wuser                 (m_axi_wuser),
        .m_axi_wvalid                (m_axi_wvalid),
        .m_axi_wready                (m_axi_wready),
        .m_axi_wpoison               (m_axi_wpoison),
        .m_axi_wtag                  (m_axi_wtag),
        .m_axi_wtagupdate            (m_axi_wtagupdate),
        .m_axi_bid                   (m_axi_bid),
        .m_axi_bresp                 (m_axi_bresp),
        .m_axi_buser                 (m_axi_buser),
        .m_axi_bvalid                (m_axi_bvalid),
        .m_axi_bready                (m_axi_bready),
        .m_axi_btrace                (m_axi_btrace),
        .m_axi_btag                  (m_axi_btag),
        .m_axi_btagmatch             (m_axi_btagmatch),
        .busy                        (busy)
    );

    // ------------------------------------------------------------------------
    // Monitor taps. cfg_monitor_enable gates every tap and holds the table
    // clear; cfg_timeout_cycles is MICROSECONDS at full width, 0 = never.
    // ------------------------------------------------------------------------
    logic        w_mon_cmd_valid;
    logic        w_mon_data_valid;
    logic        w_mon_resp_valid;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;
    assign w_mon_cmd_valid  = m_axi_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = m_axi_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = m_axi_bvalid & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axi_monitor_lite #(
        .UNIT_ID              (UNIT_ID),
        .AGENT_ID             (AGENT_ID),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .OUT_DEPTH (OUT_DEPTH),
        .N_ADDR_RANGES (N_ADDR_RANGES),
        .ADDR_RANGE_IS_ERROR (ADDR_RANGE_IS_ERROR),
        .ADDR_WIDTH           (AW),
        .ID_WIDTH             (IW),
        .IS_READ              (0),
        .IS_AXI               (1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (m_axi_awaddr),
        .cmd_id                     (m_axi_awid),
        .cmd_len                    (m_axi_awlen),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (m_axi_awready),
        .data_id                    (m_axi_awid),
        .data_last                  (m_axi_wlast),
        .data_resp                  (2'b00),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (m_axi_wready),
        .resp_id                    (m_axi_bid),
        .resp_code                  (m_axi_bresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (m_axi_bready),
        .cfg_freq_sel               (cfg_freq_sel),
        .cfg_timeout_cnt            (w_timeout_cnt),
        .cfg_error_enable           (cfg_error_enable),
        .cfg_compl_enable           (cfg_compl_enable),
        .cfg_timeout_enable         (cfg_timeout_enable),
        .cfg_threshold_enable       (cfg_threshold_enable),
        .cfg_active_trans_threshold (16'(ACTIVE_TRANS_THRESHOLD)),
        .cfg_axi_pkt_mask           (cfg_axi_pkt_mask),
        .cfg_latency_threshold (cfg_latency_threshold),
        .cfg_addr_check_enable (cfg_addr_check_enable),
        .cfg_addr_match_enable (cfg_addr_match_enable),
        .cfg_addr_range_enable (cfg_addr_range_enable),
        .cfg_addr_range_low (cfg_addr_range_low),
        .cfg_addr_range_high (cfg_addr_range_high),
        .monbus_valid               (monbus_valid),
        .monbus_ready               (monbus_ready),
        .monbus_packet              (monbus_packet),
        .monbus_timestamp           (monbus_timestamp),
        .active_count               (active_transactions),
        /* verilator lint_off PINCONNECTEMPTY */
        .busy                       (),
        .dropped_count (dropped_count),
        .refused_count (refused_count),
        /* verilator lint_on PINCONNECTEMPTY */
        .perf_completed_count       (w_perf_completed_count),
        .perf_error_count           (w_perf_error_count)
        );
    end else begin : gen_no_monitor
        assign monbus_valid           = 1'b0;
        assign monbus_packet          = '0;
        assign monbus_timestamp       = '0;
        assign active_transactions    = 8'h0;
        assign dropped_count          = 16'h0;
        assign refused_count          = 16'h0;
        assign w_perf_completed_count = 16'h0;
        assign w_perf_error_count     = 16'h0;
    end

    // error_count covers error+timeout packets, transaction_count completion
    // packets -- what the lite actually EMITTED, as on the _mon wrapper.
    assign error_count       = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

endmodule : axi5_master_wr_monlite
