// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_rd_monlite
// Purpose: AXIL5 Slave Read with the lite monitor (axi_monitor_lite) -- axil5_slave_rd plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axil5_slave_rd_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axil5_slave_rd
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axil5_slave_rd_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h02,
    parameter logic [15:0] AGENT_ID               = 16'h0014,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          N_ADDR_RANGES          = 0,      // address-range checker windows; 0 = not built
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,  // per range: 1 = miss is an error, 0 = hit is a match
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axil5_slave_rd) ----

    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // AXI5-Lite ID and optional signal widths
    // AWID/BID and ARID/RID width (IHI 0022L Table A5.2: 0..32).
    // This is a Subordinate-side interface, where Table B2.2 makes the ID
    // mandatory (code YS), so the legal range here is 1..32.
    parameter int ID_WIDTH           = 4,
    parameter int USER_WIDTH         = 4,

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR    = 2,
    parameter int SKID_DEPTH_R     = 4,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int ARSize = AW + 3 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0),

    parameter int RSize  = DW + 2 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_POISON ? PW : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AR channel: s_axil_ -> fub_
    input  logic [IW-1:0]           s_axil_arid,
    input  logic [AW-1:0]           s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,
    input  logic [UW-1:0]           s_axil_aruser,
    input  logic                    s_axil_artrace,
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [IW-1:0]           fub_axil_arid,
    output logic [AW-1:0]           fub_axil_araddr,
    output logic [2:0]              fub_axil_arprot,
    output logic [UW-1:0]           fub_axil_aruser,
    output logic                    fub_axil_artrace,
    output logic                    fub_axil_arvalid,
    input  logic                    fub_axil_arready,

    // R channel: fub_ -> s_axil_
    input  logic [IW-1:0]           fub_axil_rid,
    input  logic [DW-1:0]           fub_axil_rdata,
    input  logic [1:0]              fub_axil_rresp,
    input  logic [UW-1:0]           fub_axil_ruser,
    input  logic                    fub_axil_rtrace,
    input  logic [PW-1:0]           fub_axil_rpoison,
    input  logic                    fub_axil_rvalid,
    output logic                    fub_axil_rready,
    output logic [IW-1:0]           s_axil_rid,
    output logic [DW-1:0]           s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic [UW-1:0]           s_axil_ruser,
    output logic                    s_axil_rtrace,
    output logic [PW-1:0]           s_axil_rpoison,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,

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

    // ---------------------------------------------------------------------
    // Elaboration-time parameter guard (the one sanctioned in-RTL check; see
    // vault/handbook/design/no-assertions-in-rtl.md). Checks nothing at run
    // time.
    //   AXIL_DATA_WIDTH: AXI5-Lite takes any AXI DATA_WIDTH -- 8, 16, 32, 64,
    //     128, 256, 512 or 1024 (IHI 0022L Table A3.19; Table B2.4 adds no
    //     AXI5-Lite constraint, unlike AXI4-Lite's 32/64 of IHI 0022H B1.1.2).
    //   ID_WIDTH: 1..32 (Table A5.2). Subordinate-side: the ID is mandatory (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_slave_rd_monlite: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 1 || ID_WIDTH > 32)
            $fatal(1, "axil5_slave_rd_monlite: ID_WIDTH=%0d out of range 1..32 (IHI 0022L Table A5.2; a Subordinate must carry the ID)",
                   ID_WIDTH);
    end
`endif

    // ------------------------------------------------------------------------
    // The core, passed through untouched (no monitor gating on any handshake)
    // ------------------------------------------------------------------------
    axil5_slave_rd #(
        .AXIL_ADDR_WIDTH             (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH             (AXIL_DATA_WIDTH),
        .ID_WIDTH                    (ID_WIDTH),
        .USER_WIDTH                  (USER_WIDTH),
        .ENABLE_USER                 (ENABLE_USER),
        .ENABLE_TRACE                (ENABLE_TRACE),
        .ENABLE_POISON               (ENABLE_POISON),
        .SKID_DEPTH_AR               (SKID_DEPTH_AR),
        .SKID_DEPTH_R                (SKID_DEPTH_R),
        .AW                          (AW),
        .DW                          (DW),
        .UW                          (UW),
        .PW                          (PW),
        .ARSize                      (ARSize),
        .RSize                       (RSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .s_axil_arid                 (s_axil_arid),
        .s_axil_araddr               (s_axil_araddr),
        .s_axil_arprot               (s_axil_arprot),
        .s_axil_aruser               (s_axil_aruser),
        .s_axil_artrace              (s_axil_artrace),
        .s_axil_arvalid              (s_axil_arvalid),
        .s_axil_arready              (s_axil_arready),
        .fub_arid                    (fub_axil_arid),
        .fub_araddr                  (fub_axil_araddr),
        .fub_arprot                  (fub_axil_arprot),
        .fub_aruser                  (fub_axil_aruser),
        .fub_artrace                 (fub_axil_artrace),
        .fub_arvalid                 (fub_axil_arvalid),
        .fub_arready                 (fub_axil_arready),
        .fub_rid                      (fub_axil_rid),
        .fub_rdata                   (fub_axil_rdata),
        .fub_rresp                   (fub_axil_rresp),
        .fub_ruser                   (fub_axil_ruser),
        .fub_rtrace                  (fub_axil_rtrace),
        .fub_rpoison                 (fub_axil_rpoison),
        .fub_rvalid                  (fub_axil_rvalid),
        .fub_rready                  (fub_axil_rready),
        .s_axil_rid                   (s_axil_rid),
        .s_axil_rdata                (s_axil_rdata),
        .s_axil_rresp                (s_axil_rresp),
        .s_axil_ruser                (s_axil_ruser),
        .s_axil_rtrace               (s_axil_rtrace),
        .s_axil_rpoison              (s_axil_rpoison),
        .s_axil_rvalid               (s_axil_rvalid),
        .s_axil_rready               (s_axil_rready),
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
    assign w_mon_cmd_valid  = s_axil_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = s_axil_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = s_axil_rvalid & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    // AXI5-Lite IDs to the monitor (amba #104). ARID/RID exist on AXI5-Lite
    // and a Subordinate may return read data out of order across IDs (IHI
    // 0022L B2.1.5), so the monitor matches each R to the oldest command of
    // the SAME ID, as on AXI4 -- with the ID tied 0 it paired every R with the
    // oldest command outstanding, whichever one the R answered.
    logic [IW-1:0] w_mon_cmd_id, w_mon_data_id;
    assign w_mon_cmd_id  = s_axil_arid;
    assign w_mon_data_id = s_axil_rid;

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
        .IS_READ              (1'b1),
        .IS_AXI               (1'b1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (s_axil_araddr),
        .cmd_id                     (w_mon_cmd_id),
        .cmd_len                    (8'h00),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (s_axil_arready),
        .data_id                    (w_mon_data_id),
        .data_last                  (1'b1),
        .data_resp                  (s_axil_rresp),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (s_axil_rready),
        .resp_id                    (w_mon_data_id),
        .resp_code                  (s_axil_rresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (s_axil_rready),
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

endmodule : axil5_slave_rd_monlite
