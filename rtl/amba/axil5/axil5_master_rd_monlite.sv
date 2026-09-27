// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_rd_monlite
// Purpose: AXIL5 Master Read with the lite monitor (axi_monitor_lite) -- axil5_master_rd plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axil5_master_rd_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axil5_master_rd
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axil5_master_rd_monlite
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
    // ---- Core parameters (passed through verbatim to axil5_master_rd) ----

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
    parameter int SKID_DEPTH_AR    = 2,
    parameter int SKID_DEPTH_R     = 4,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int ARSize = AW + 3 +
                             (ENABLE_LOCK ? 1 : 0) +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_MPAM ? MW : 0) +
                             (ENABLE_MECID ? EW : 0) +
                             (ENABLE_NSAID ? NW : 0),

    parameter int RSize  = DW + 2 +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_LOOP ? LW : 0) +
                             (ENABLE_POISON ? PW : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AR channel: fub_ -> m_axil_
    input  logic [AW-1:0]           fub_axil_araddr,
    input  logic [2:0]              fub_axil_arprot,
    input  logic                    fub_axil_arlock,
    input  logic [UW-1:0]           fub_axil_aruser,
    input  logic                    fub_axil_artrace,
    input  logic [LW-1:0]           fub_axil_arloop,
    input  logic [MW-1:0]           fub_axil_armpam,
    input  logic [EW-1:0]           fub_axil_armecid,
    input  logic [NW-1:0]           fub_axil_arnsaid,
    input  logic                    fub_axil_arvalid,
    output logic                    fub_axil_arready,
    output logic [AW-1:0]           m_axil_araddr,
    output logic [2:0]              m_axil_arprot,
    output logic                    m_axil_arlock,
    output logic [UW-1:0]           m_axil_aruser,
    output logic                    m_axil_artrace,
    output logic [LW-1:0]           m_axil_arloop,
    output logic [MW-1:0]           m_axil_armpam,
    output logic [EW-1:0]           m_axil_armecid,
    output logic [NW-1:0]           m_axil_arnsaid,
    output logic                    m_axil_arvalid,
    input  logic                    m_axil_arready,

    // R channel: m_axil_ -> fub_
    input  logic [DW-1:0]           m_axil_rdata,
    input  logic [1:0]              m_axil_rresp,
    input  logic [UW-1:0]           m_axil_ruser,
    input  logic                    m_axil_rtrace,
    input  logic [LW-1:0]           m_axil_rloop,
    input  logic [PW-1:0]           m_axil_rpoison,
    input  logic                    m_axil_rvalid,
    output logic                    m_axil_rready,
    output logic [DW-1:0]           fub_axil_rdata,
    output logic [1:0]              fub_axil_rresp,
    output logic [UW-1:0]           fub_axil_ruser,
    output logic                    fub_axil_rtrace,
    output logic [LW-1:0]           fub_axil_rloop,
    output logic [PW-1:0]           fub_axil_rpoison,
    output logic                    fub_axil_rvalid,
    input  logic                    fub_axil_rready,

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
    axil5_master_rd #(
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
        .SKID_DEPTH_AR               (SKID_DEPTH_AR),
        .SKID_DEPTH_R                (SKID_DEPTH_R),
        .AW                          (AW),
        .DW                          (DW),
        .UW                          (UW),
        .LW                          (LW),
        .MW                          (MW),
        .EW                          (EW),
        .NW                          (NW),
        .PW                          (PW),
        .ARSize                      (ARSize),
        .RSize                       (RSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .fub_araddr                  (fub_axil_araddr),
        .fub_arprot                  (fub_axil_arprot),
        .fub_arlock                  (fub_axil_arlock),
        .fub_aruser                  (fub_axil_aruser),
        .fub_artrace                 (fub_axil_artrace),
        .fub_arloop                  (fub_axil_arloop),
        .fub_armpam                  (fub_axil_armpam),
        .fub_armecid                 (fub_axil_armecid),
        .fub_arnsaid                 (fub_axil_arnsaid),
        .fub_arvalid                 (fub_axil_arvalid),
        .fub_arready                 (fub_axil_arready),
        .m_axil_araddr               (m_axil_araddr),
        .m_axil_arprot               (m_axil_arprot),
        .m_axil_arlock               (m_axil_arlock),
        .m_axil_aruser               (m_axil_aruser),
        .m_axil_artrace              (m_axil_artrace),
        .m_axil_arloop               (m_axil_arloop),
        .m_axil_armpam               (m_axil_armpam),
        .m_axil_armecid              (m_axil_armecid),
        .m_axil_arnsaid              (m_axil_arnsaid),
        .m_axil_arvalid              (m_axil_arvalid),
        .m_axil_arready              (m_axil_arready),
        .m_axil_rdata                (m_axil_rdata),
        .m_axil_rresp                (m_axil_rresp),
        .m_axil_ruser                (m_axil_ruser),
        .m_axil_rtrace               (m_axil_rtrace),
        .m_axil_rloop                (m_axil_rloop),
        .m_axil_rpoison              (m_axil_rpoison),
        .m_axil_rvalid               (m_axil_rvalid),
        .m_axil_rready               (m_axil_rready),
        .fub_rdata                   (fub_axil_rdata),
        .fub_rresp                   (fub_axil_rresp),
        .fub_ruser                   (fub_axil_ruser),
        .fub_rtrace                  (fub_axil_rtrace),
        .fub_rloop                   (fub_axil_rloop),
        .fub_rpoison                 (fub_axil_rpoison),
        .fub_rvalid                  (fub_axil_rvalid),
        .fub_rready                  (fub_axil_rready),
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
    assign w_mon_cmd_valid  = m_axil_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = m_axil_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = m_axil_rvalid & cfg_monitor_enable;
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
        .IS_READ              (1'b1),
        .IS_AXI               (1'b1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (m_axil_araddr),
        .cmd_id                     (1'b0),
        .cmd_len                    (8'h00),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (m_axil_arready),
        .data_id                    (1'b0),
        .data_last                  (1'b1),
        .data_resp                  (m_axil_rresp),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (m_axil_rready),
        .resp_id                    (1'b0),
        .resp_code                  (m_axil_rresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (m_axil_rready),
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

endmodule : axil5_master_rd_monlite
