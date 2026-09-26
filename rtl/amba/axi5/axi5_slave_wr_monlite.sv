// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_wr_monlite
// Purpose: AXI5 Slave Write with the lite monitor (axi_monitor_lite) -- axi5_slave_wr plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/axi5/axi5_slave_wr_monlite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axi5_slave_wr_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axi5_slave_wr
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axi5_slave_wr_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h01,
    parameter logic [15:0] AGENT_ID               = 16'h000D,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi5_slave_wr) ----

    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_ATOP_WIDTH    = 6,
    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,

    // Feature enables
    parameter bit ENABLE_ATOMIC     = 1,
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,

    parameter int AWSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_ATOMIC ? AXI_ATOP_WIDTH : 0) +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_MTE ? (AXI_TAGOP_WIDTH + TW) : 0),

    parameter int WSize    = DW + SW + 1 + UW +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_MTE ? (TW + NUM_TAGS) : 0),

    parameter int BSize    = IW + 2 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
) (

    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side from external master)
    // =========================================================================

    // Write address channel (AW)
    input  logic [IW-1:0]               s_axi_awid,
    input  logic [AW-1:0]               s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [UW-1:0]               s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // AXI5 AW signals
    input  logic [AXI_ATOP_WIDTH-1:0]   s_axi_awatop,
    input  logic [AXI_NSAID_WIDTH-1:0]  s_axi_awnsaid,
    input  logic                        s_axi_awtrace,
    input  logic [AXI_MPAM_WIDTH-1:0]   s_axi_awmpam,
    input  logic [AXI_MECID_WIDTH-1:0]  s_axi_awmecid,
    input  logic                        s_axi_awunique,
    input  logic [AXI_TAGOP_WIDTH-1:0]  s_axi_awtagop,
    input  logic [TW-1:0]               s_axi_awtag,

    // Write data channel (W)
    input  logic [DW-1:0]               s_axi_wdata,
    input  logic [SW-1:0]               s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [UW-1:0]               s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // AXI5 W signals
    input  logic                        s_axi_wpoison,
    input  logic [TW-1:0]               s_axi_wtag,
    input  logic [NUM_TAGS-1:0]         s_axi_wtagupdate,

    // Write response channel (B)
    output logic [IW-1:0]               s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [UW-1:0]               s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // AXI5 B signals
    output logic                        s_axi_btrace,
    output logic [TW-1:0]               s_axi_btag,
    output logic                        s_axi_btagmatch,

    // =========================================================================
    // FUB Interface (Output Side to memory or backend)
    // =========================================================================

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
    output logic [UW-1:0]              fub_axi_awuser,
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,

    // AXI5 AW signals
    output logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,
    output logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,
    output logic                       fub_axi_awtrace,
    output logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,
    output logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,
    output logic                       fub_axi_awunique,
    output logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,
    output logic [TW-1:0]              fub_axi_awtag,

    // Write data channel (W)
    output logic [DW-1:0]              fub_axi_wdata,
    output logic [SW-1:0]              fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [UW-1:0]              fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,

    // AXI5 W signals
    output logic                       fub_axi_wpoison,
    output logic [TW-1:0]              fub_axi_wtag,
    output logic [NUM_TAGS-1:0]        fub_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [UW-1:0]              fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,

    // AXI5 B signals
    input  logic                       fub_axi_btrace,
    input  logic [TW-1:0]              fub_axi_btag,
    input  logic                       fub_axi_btagmatch,

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
    axi5_slave_wr #(
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
        .s_axi_awid                  (s_axi_awid),
        .s_axi_awaddr                (s_axi_awaddr),
        .s_axi_awlen                 (s_axi_awlen),
        .s_axi_awsize                (s_axi_awsize),
        .s_axi_awburst               (s_axi_awburst),
        .s_axi_awlock                (s_axi_awlock),
        .s_axi_awcache               (s_axi_awcache),
        .s_axi_awprot                (s_axi_awprot),
        .s_axi_awqos                 (s_axi_awqos),
        .s_axi_awuser                (s_axi_awuser),
        .s_axi_awvalid               (s_axi_awvalid),
        .s_axi_awready               (s_axi_awready),
        .s_axi_awatop                (s_axi_awatop),
        .s_axi_awnsaid               (s_axi_awnsaid),
        .s_axi_awtrace               (s_axi_awtrace),
        .s_axi_awmpam                (s_axi_awmpam),
        .s_axi_awmecid               (s_axi_awmecid),
        .s_axi_awunique              (s_axi_awunique),
        .s_axi_awtagop               (s_axi_awtagop),
        .s_axi_awtag                 (s_axi_awtag),
        .s_axi_wdata                 (s_axi_wdata),
        .s_axi_wstrb                 (s_axi_wstrb),
        .s_axi_wlast                 (s_axi_wlast),
        .s_axi_wuser                 (s_axi_wuser),
        .s_axi_wvalid                (s_axi_wvalid),
        .s_axi_wready                (s_axi_wready),
        .s_axi_wpoison               (s_axi_wpoison),
        .s_axi_wtag                  (s_axi_wtag),
        .s_axi_wtagupdate            (s_axi_wtagupdate),
        .s_axi_bid                   (s_axi_bid),
        .s_axi_bresp                 (s_axi_bresp),
        .s_axi_buser                 (s_axi_buser),
        .s_axi_bvalid                (s_axi_bvalid),
        .s_axi_bready                (s_axi_bready),
        .s_axi_btrace                (s_axi_btrace),
        .s_axi_btag                  (s_axi_btag),
        .s_axi_btagmatch             (s_axi_btagmatch),
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
    assign w_mon_cmd_valid  = fub_axi_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = fub_axi_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = fub_axi_bvalid & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axi_monitor_lite #(
        .UNIT_ID              (UNIT_ID),
        .AGENT_ID             (AGENT_ID),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .OUT_DEPTH (OUT_DEPTH),
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
        .cmd_addr                   (fub_axi_awaddr),
        .cmd_id                     (fub_axi_awid),
        .cmd_len                    (fub_axi_awlen),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (fub_axi_awready),
        .data_id                    (fub_axi_awid),
        .data_last                  (fub_axi_wlast),
        .data_resp                  (2'b00),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (fub_axi_wready),
        .resp_id                    (fub_axi_bid),
        .resp_code                  (fub_axi_bresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (fub_axi_bready),
        .cfg_freq_sel               (cfg_freq_sel),
        .cfg_timeout_cnt            (w_timeout_cnt),
        .cfg_error_enable           (cfg_error_enable),
        .cfg_compl_enable           (cfg_compl_enable),
        .cfg_timeout_enable         (cfg_timeout_enable),
        .cfg_threshold_enable       (cfg_threshold_enable),
        .cfg_active_trans_threshold (16'(ACTIVE_TRANS_THRESHOLD)),
        .cfg_axi_pkt_mask           (cfg_axi_pkt_mask),
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

endmodule : axi5_slave_wr_monlite
