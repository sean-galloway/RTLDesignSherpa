// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_wr_monlite
// Purpose: AXIL5 Master Write with the lite monitor (axi_monitor_lite) -- axil5_master_wr plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/axil5/axil5_master_wr_monlite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axil5_master_wr_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axil5_master_wr
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axil5_master_wr_monlite
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
    // ---- Core parameters (passed through verbatim to axil5_master_wr) ----

    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // AXI5-Lite optional signal widths
    parameter int USER_WIDTH         = 4,
    parameter int LOOP_WIDTH         = 3,
    parameter int MPAM_WIDTH         = 11,
    parameter int MECID_WIDTH        = 16,
    parameter int NSAID_WIDTH        = 4,

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_LOOP        = 1,
    parameter bit ENABLE_MPAM        = 1,
    parameter bit ENABLE_MECID       = 1,
    parameter bit ENABLE_NSAID       = 1,
    parameter bit ENABLE_POISON      = 1,
    parameter bit ENABLE_LOCK        = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW    = 2,
    parameter int SKID_DEPTH_W     = 4,
    parameter int SKID_DEPTH_B     = 2,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int SW       = DW / 8,
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int AWSize = AW + 3 +
                             (ENABLE_LOCK ? 1 : 0) +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_MPAM ? MW : 0) +
                             (ENABLE_MECID ? EW : 0) +
                             (ENABLE_NSAID ? NW : 0),

    parameter int WSize  = DW + SW +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_POISON ? PW : 0),

    parameter int BSize  = 2 +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AW channel: fub_ -> m_axil_
    input  logic [AW-1:0]           fub_axil_awaddr,
    input  logic [2:0]              fub_axil_awprot,
    input  logic                    fub_axil_awlock,
    input  logic [UW-1:0]           fub_axil_awuser,
    input  logic                    fub_axil_awtrace,
    input  logic [LW-1:0]           fub_axil_awloop,
    input  logic [MW-1:0]           fub_axil_awmpam,
    input  logic [EW-1:0]           fub_axil_awmecid,
    input  logic [NW-1:0]           fub_axil_awnsaid,
    input  logic                    fub_axil_awvalid,
    output logic                    fub_axil_awready,
    output logic [AW-1:0]           m_axil_awaddr,
    output logic [2:0]              m_axil_awprot,
    output logic                    m_axil_awlock,
    output logic [UW-1:0]           m_axil_awuser,
    output logic                    m_axil_awtrace,
    output logic [LW-1:0]           m_axil_awloop,
    output logic [MW-1:0]           m_axil_awmpam,
    output logic [EW-1:0]           m_axil_awmecid,
    output logic [NW-1:0]           m_axil_awnsaid,
    output logic                    m_axil_awvalid,
    input  logic                    m_axil_awready,

    // W channel: fub_ -> m_axil_
    input  logic [DW-1:0]           fub_axil_wdata,
    input  logic [SW-1:0]           fub_axil_wstrb,
    input  logic [UW-1:0]           fub_axil_wuser,
    input  logic [PW-1:0]           fub_axil_wpoison,
    input  logic                    fub_axil_wvalid,
    output logic                    fub_axil_wready,
    output logic [DW-1:0]           m_axil_wdata,
    output logic [SW-1:0]           m_axil_wstrb,
    output logic [UW-1:0]           m_axil_wuser,
    output logic [PW-1:0]           m_axil_wpoison,
    output logic                    m_axil_wvalid,
    input  logic                    m_axil_wready,

    // B channel: m_axil_ -> fub_
    input  logic [1:0]              m_axil_bresp,
    input  logic [UW-1:0]           m_axil_buser,
    input  logic                    m_axil_btrace,
    input  logic [LW-1:0]           m_axil_bloop,
    input  logic                    m_axil_bvalid,
    output logic                    m_axil_bready,
    output logic [1:0]              fub_axil_bresp,
    output logic [UW-1:0]           fub_axil_buser,
    output logic                    fub_axil_btrace,
    output logic [LW-1:0]           fub_axil_bloop,
    output logic                    fub_axil_bvalid,
    input  logic                    fub_axil_bready,

    // Status output for clock gating
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
    axil5_master_wr #(
        .AXIL_ADDR_WIDTH             (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH             (AXIL_DATA_WIDTH),
        .USER_WIDTH                  (USER_WIDTH),
        .LOOP_WIDTH                  (LOOP_WIDTH),
        .MPAM_WIDTH                  (MPAM_WIDTH),
        .MECID_WIDTH                 (MECID_WIDTH),
        .NSAID_WIDTH                 (NSAID_WIDTH),
        .ENABLE_USER                 (ENABLE_USER),
        .ENABLE_TRACE                (ENABLE_TRACE),
        .ENABLE_LOOP                 (ENABLE_LOOP),
        .ENABLE_MPAM                 (ENABLE_MPAM),
        .ENABLE_MECID                (ENABLE_MECID),
        .ENABLE_NSAID                (ENABLE_NSAID),
        .ENABLE_POISON               (ENABLE_POISON),
        .ENABLE_LOCK                 (ENABLE_LOCK),
        .SKID_DEPTH_AW               (SKID_DEPTH_AW),
        .SKID_DEPTH_W                (SKID_DEPTH_W),
        .SKID_DEPTH_B                (SKID_DEPTH_B),
        .AW                          (AW),
        .DW                          (DW),
        .SW                          (SW),
        .UW                          (UW),
        .LW                          (LW),
        .MW                          (MW),
        .EW                          (EW),
        .NW                          (NW),
        .PW                          (PW),
        .AWSize                      (AWSize),
        .WSize                       (WSize),
        .BSize                       (BSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .fub_awaddr                  (fub_axil_awaddr),
        .fub_awprot                  (fub_axil_awprot),
        .fub_awlock                  (fub_axil_awlock),
        .fub_awuser                  (fub_axil_awuser),
        .fub_awtrace                 (fub_axil_awtrace),
        .fub_awloop                  (fub_axil_awloop),
        .fub_awmpam                  (fub_axil_awmpam),
        .fub_awmecid                 (fub_axil_awmecid),
        .fub_awnsaid                 (fub_axil_awnsaid),
        .fub_awvalid                 (fub_axil_awvalid),
        .fub_awready                 (fub_axil_awready),
        .m_axil_awaddr               (m_axil_awaddr),
        .m_axil_awprot               (m_axil_awprot),
        .m_axil_awlock               (m_axil_awlock),
        .m_axil_awuser               (m_axil_awuser),
        .m_axil_awtrace              (m_axil_awtrace),
        .m_axil_awloop               (m_axil_awloop),
        .m_axil_awmpam               (m_axil_awmpam),
        .m_axil_awmecid              (m_axil_awmecid),
        .m_axil_awnsaid              (m_axil_awnsaid),
        .m_axil_awvalid              (m_axil_awvalid),
        .m_axil_awready              (m_axil_awready),
        .fub_wdata                   (fub_axil_wdata),
        .fub_wstrb                   (fub_axil_wstrb),
        .fub_wuser                   (fub_axil_wuser),
        .fub_wpoison                 (fub_axil_wpoison),
        .fub_wvalid                  (fub_axil_wvalid),
        .fub_wready                  (fub_axil_wready),
        .m_axil_wdata                (m_axil_wdata),
        .m_axil_wstrb                (m_axil_wstrb),
        .m_axil_wuser                (m_axil_wuser),
        .m_axil_wpoison              (m_axil_wpoison),
        .m_axil_wvalid               (m_axil_wvalid),
        .m_axil_wready               (m_axil_wready),
        .m_axil_bresp                (m_axil_bresp),
        .m_axil_buser                (m_axil_buser),
        .m_axil_btrace               (m_axil_btrace),
        .m_axil_bloop                (m_axil_bloop),
        .m_axil_bvalid               (m_axil_bvalid),
        .m_axil_bready               (m_axil_bready),
        .fub_bresp                   (fub_axil_bresp),
        .fub_buser                   (fub_axil_buser),
        .fub_btrace                  (fub_axil_btrace),
        .fub_bloop                   (fub_axil_bloop),
        .fub_bvalid                  (fub_axil_bvalid),
        .fub_bready                  (fub_axil_bready),
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
    assign w_mon_cmd_valid  = m_axil_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = m_axil_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = m_axil_bvalid & cfg_monitor_enable;
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
        .ID_WIDTH             (32'd1),
        .IS_READ              (1'b0),
        .IS_AXI               (1'b1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (m_axil_awaddr),
        .cmd_id                     (1'b0),
        .cmd_len                    (8'h00),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (m_axil_awready),
        .data_id                    (1'b0),
        .data_last                  (1'b1),
        .data_resp                  (2'b00),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (m_axil_wready),
        .resp_id                    (1'b0),
        .resp_code                  (m_axil_bresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (m_axil_bready),
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

endmodule : axil5_master_wr_monlite
