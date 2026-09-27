// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_rd_monlite
// Purpose: AXI5 Master Read with the lite monitor (axi_monitor_lite) -- axi5_master_rd plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axi5_master_rd_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axi5_master_rd
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axi5_master_rd_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h01,
    parameter logic [15:0] AGENT_ID               = 16'h000A,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          N_ADDR_RANGES          = 0,      // address-range checker windows; 0 = not built
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,  // per range: 1 = miss is an error, 0 = hit is a match
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi5_master_rd) ----

    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_NSAID_WIDTH   = 4,      // Non-secure access ID width
    parameter int AXI_MPAM_WIDTH    = 11,     // MPAM width (PartID + PMG)
    parameter int AXI_MECID_WIDTH   = 16,     // Memory encryption context ID width
    parameter int AXI_TAG_WIDTH     = 4,      // Memory tag width per 16 bytes
    parameter int AXI_TAGOP_WIDTH   = 2,      // Tag operation width
    parameter int AXI_CHUNKNUM_WIDTH = 4,     // Chunk number width

    // Feature enables (set to 0 to disable optional signals)
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
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

    // Chunk strobe width (128-bit granules)
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,

    // AR channel packet size calculation
    // Base: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER
    // AXI5: + NSAID + TRACE + MPAM + MECID + UNIQUE + CHUNKEN + TAGOP
    parameter int ARSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_CHUNKING ? 1 : 0) +
                             (ENABLE_MTE ? AXI_TAGOP_WIDTH : 0),

    // R channel packet size calculation
    // Base: ID + DATA + RESP + LAST + USER
    // AXI5: + TRACE + POISON + CHUNKV + CHUNKNUM + CHUNKSTRB + TAG + TAGMATCH
    parameter int RSize    = IW + DW + 2 + 1 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_CHUNKING ? (1 + AXI_CHUNKNUM_WIDTH + CHUNK_STRB_WIDTH) : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side - FUB/Functional Unit Block)
    // =========================================================================

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
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // AXI5 AR channel signals
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_arnsaid,    // Non-secure access ID
    input  logic                       fub_axi_artrace,    // Trace signal
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_armpam,     // Memory partitioning
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_armecid,    // Memory encryption context
    input  logic                       fub_axi_arunique,   // Unique ID indicator
    input  logic                       fub_axi_archunken,  // Chunk enable
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_artagop,    // Tag operation (MTE)

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // AXI5 R channel signals
    output logic                       fub_axi_rtrace,     // Trace signal
    output logic                       fub_axi_rpoison,    // Data poison indicator
    output logic                       fub_axi_rchunkv,    // Chunk valid
    output logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum, // Chunk number
    output logic [CHUNK_STRB_WIDTH-1:0] fub_axi_rchunkstrb, // Chunk strobe
    output logic [TW-1:0]              fub_axi_rtag,       // Memory tags
    output logic                       fub_axi_rtagmatch,  // Tag match response

    // =========================================================================
    // Master AXI5 Interface (Output Side)
    // =========================================================================

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
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // AXI5 AR channel signals
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

    // AXI5 R channel signals
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

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
    axi5_master_rd #(
        .SKID_DEPTH_AR               (SKID_DEPTH_AR),
        .SKID_DEPTH_R                (SKID_DEPTH_R),
        .AXI_ID_WIDTH                (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH              (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH              (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH              (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH             (AXI_WSTRB_WIDTH),
        .AXI_NSAID_WIDTH             (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH              (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH             (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH               (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH             (AXI_TAGOP_WIDTH),
        .AXI_CHUNKNUM_WIDTH          (AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID                (ENABLE_NSAID),
        .ENABLE_TRACE                (ENABLE_TRACE),
        .ENABLE_MPAM                 (ENABLE_MPAM),
        .ENABLE_MECID                (ENABLE_MECID),
        .ENABLE_UNIQUE               (ENABLE_UNIQUE),
        .ENABLE_CHUNKING             (ENABLE_CHUNKING),
        .ENABLE_MTE                  (ENABLE_MTE),
        .ENABLE_POISON               (ENABLE_POISON),
        .AW                          (AW),
        .DW                          (DW),
        .IW                          (IW),
        .SW                          (SW),
        .UW                          (UW),
        .NUM_TAGS                    (NUM_TAGS),
        .TW                          (TW),
        .CHUNK_STRB_WIDTH            (CHUNK_STRB_WIDTH),
        .ARSize                      (ARSize),
        .RSize                       (RSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .fub_axi_arid                (fub_axi_arid),
        .fub_axi_araddr              (fub_axi_araddr),
        .fub_axi_arlen               (fub_axi_arlen),
        .fub_axi_arsize              (fub_axi_arsize),
        .fub_axi_arburst             (fub_axi_arburst),
        .fub_axi_arlock              (fub_axi_arlock),
        .fub_axi_arcache             (fub_axi_arcache),
        .fub_axi_arprot              (fub_axi_arprot),
        .fub_axi_arqos               (fub_axi_arqos),
        .fub_axi_aruser              (fub_axi_aruser),
        .fub_axi_arvalid             (fub_axi_arvalid),
        .fub_axi_arready             (fub_axi_arready),
        .fub_axi_arnsaid             (fub_axi_arnsaid),
        .fub_axi_artrace             (fub_axi_artrace),
        .fub_axi_armpam              (fub_axi_armpam),
        .fub_axi_armecid             (fub_axi_armecid),
        .fub_axi_arunique            (fub_axi_arunique),
        .fub_axi_archunken           (fub_axi_archunken),
        .fub_axi_artagop             (fub_axi_artagop),
        .fub_axi_rid                 (fub_axi_rid),
        .fub_axi_rdata               (fub_axi_rdata),
        .fub_axi_rresp               (fub_axi_rresp),
        .fub_axi_rlast               (fub_axi_rlast),
        .fub_axi_ruser               (fub_axi_ruser),
        .fub_axi_rvalid              (fub_axi_rvalid),
        .fub_axi_rready              (fub_axi_rready),
        .fub_axi_rtrace              (fub_axi_rtrace),
        .fub_axi_rpoison             (fub_axi_rpoison),
        .fub_axi_rchunkv             (fub_axi_rchunkv),
        .fub_axi_rchunknum           (fub_axi_rchunknum),
        .fub_axi_rchunkstrb          (fub_axi_rchunkstrb),
        .fub_axi_rtag                (fub_axi_rtag),
        .fub_axi_rtagmatch           (fub_axi_rtagmatch),
        .m_axi_arid                  (m_axi_arid),
        .m_axi_araddr                (m_axi_araddr),
        .m_axi_arlen                 (m_axi_arlen),
        .m_axi_arsize                (m_axi_arsize),
        .m_axi_arburst               (m_axi_arburst),
        .m_axi_arlock                (m_axi_arlock),
        .m_axi_arcache               (m_axi_arcache),
        .m_axi_arprot                (m_axi_arprot),
        .m_axi_arqos                 (m_axi_arqos),
        .m_axi_aruser                (m_axi_aruser),
        .m_axi_arvalid               (m_axi_arvalid),
        .m_axi_arready               (m_axi_arready),
        .m_axi_arnsaid               (m_axi_arnsaid),
        .m_axi_artrace               (m_axi_artrace),
        .m_axi_armpam                (m_axi_armpam),
        .m_axi_armecid               (m_axi_armecid),
        .m_axi_arunique              (m_axi_arunique),
        .m_axi_archunken             (m_axi_archunken),
        .m_axi_artagop               (m_axi_artagop),
        .m_axi_rid                   (m_axi_rid),
        .m_axi_rdata                 (m_axi_rdata),
        .m_axi_rresp                 (m_axi_rresp),
        .m_axi_rlast                 (m_axi_rlast),
        .m_axi_ruser                 (m_axi_ruser),
        .m_axi_rvalid                (m_axi_rvalid),
        .m_axi_rready                (m_axi_rready),
        .m_axi_rtrace                (m_axi_rtrace),
        .m_axi_rpoison               (m_axi_rpoison),
        .m_axi_rchunkv               (m_axi_rchunkv),
        .m_axi_rchunknum             (m_axi_rchunknum),
        .m_axi_rchunkstrb            (m_axi_rchunkstrb),
        .m_axi_rtag                  (m_axi_rtag),
        .m_axi_rtagmatch             (m_axi_rtagmatch),
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
    assign w_mon_cmd_valid  = m_axi_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = m_axi_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = (m_axi_rvalid && m_axi_rlast) & cfg_monitor_enable;
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
        .IS_READ              (1),
        .IS_AXI               (1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (m_axi_araddr),
        .cmd_id                     (m_axi_arid),
        .cmd_len                    (m_axi_arlen),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (m_axi_arready),
        .data_id                    (m_axi_rid),
        .data_last                  (m_axi_rlast),
        .data_resp                  (m_axi_rresp),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (m_axi_rready),
        .resp_id                    (m_axi_rid),
        .resp_code                  (m_axi_rresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (m_axi_rready),
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

endmodule : axi5_master_rd_monlite
