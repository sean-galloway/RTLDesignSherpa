// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_wr_monlite
// Purpose: AXI4 Slave Write with the lite monitor (axi_monitor_lite) -- axi4_slave_wr plus a fifth of the monitor gates
//
// Documentation: docs/markdown/rtl-amba/axi4/axi4_slave_wr_monlite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-monitor sibling of axi4_slave_wr_mon (amba/monitor-lite TASK-001). Same
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
// Every core parameter and port is declared here verbatim from axi4_slave_wr
// and passed through by name; the monitor section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axi4_slave_wr_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h02,
    parameter logic [15:0] AGENT_ID               = 16'h0015,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axi4_slave_wr) ----

    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short params and calculations
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW
) (

    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Slave AXI Interface (Input Side)
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
    input  logic [3:0]                  s_axi_awregion,
    input  logic [UW-1:0]               s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]               s_axi_wdata,
    input  logic [SW-1:0]               s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [UW-1:0]               s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]               s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [UW-1:0]               s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Master AXI Interface (Output Side to memory or backend)
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
    output logic [3:0]                 fub_axi_awregion,
    output logic [UW-1:0]              fub_axi_awuser,
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              fub_axi_wdata,
    output logic [SW-1:0]              fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [UW-1:0]              fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [UW-1:0]              fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,

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
    axi4_slave_wr #(
        .SKID_DEPTH_AW               (SKID_DEPTH_AW),
        .SKID_DEPTH_W                (SKID_DEPTH_W),
        .SKID_DEPTH_B                (SKID_DEPTH_B),
        .AXI_ID_WIDTH                (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH              (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH              (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH              (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH             (AXI_WSTRB_WIDTH),
        .AW                          (AW),
        .DW                          (DW),
        .IW                          (IW),
        .SW                          (SW),
        .UW                          (UW),
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
        .s_axi_awregion              (s_axi_awregion),
        .s_axi_awuser                (s_axi_awuser),
        .s_axi_awvalid               (s_axi_awvalid),
        .s_axi_awready               (s_axi_awready),
        .s_axi_wdata                 (s_axi_wdata),
        .s_axi_wstrb                 (s_axi_wstrb),
        .s_axi_wlast                 (s_axi_wlast),
        .s_axi_wuser                 (s_axi_wuser),
        .s_axi_wvalid                (s_axi_wvalid),
        .s_axi_wready                (s_axi_wready),
        .s_axi_bid                   (s_axi_bid),
        .s_axi_bresp                 (s_axi_bresp),
        .s_axi_buser                 (s_axi_buser),
        .s_axi_bvalid                (s_axi_bvalid),
        .s_axi_bready                (s_axi_bready),
        .fub_axi_awid                (fub_axi_awid),
        .fub_axi_awaddr              (fub_axi_awaddr),
        .fub_axi_awlen               (fub_axi_awlen),
        .fub_axi_awsize              (fub_axi_awsize),
        .fub_axi_awburst             (fub_axi_awburst),
        .fub_axi_awlock              (fub_axi_awlock),
        .fub_axi_awcache             (fub_axi_awcache),
        .fub_axi_awprot              (fub_axi_awprot),
        .fub_axi_awqos               (fub_axi_awqos),
        .fub_axi_awregion            (fub_axi_awregion),
        .fub_axi_awuser              (fub_axi_awuser),
        .fub_axi_awvalid             (fub_axi_awvalid),
        .fub_axi_awready             (fub_axi_awready),
        .fub_axi_wdata               (fub_axi_wdata),
        .fub_axi_wstrb               (fub_axi_wstrb),
        .fub_axi_wlast               (fub_axi_wlast),
        .fub_axi_wuser               (fub_axi_wuser),
        .fub_axi_wvalid              (fub_axi_wvalid),
        .fub_axi_wready              (fub_axi_wready),
        .fub_axi_bid                 (fub_axi_bid),
        .fub_axi_bresp               (fub_axi_bresp),
        .fub_axi_buser               (fub_axi_buser),
        .fub_axi_bvalid              (fub_axi_bvalid),
        .fub_axi_bready              (fub_axi_bready),
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
    assign w_mon_cmd_valid  = s_axi_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = s_axi_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = s_axi_bvalid & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axi_monitor_lite #(
        .UNIT_ID (UNIT_ID),
        .AGENT_ID (AGENT_ID),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .OUT_DEPTH (OUT_DEPTH),
        .ADDR_WIDTH (AW),
        .ID_WIDTH (IW),
        .IS_READ (1'b0),
        .IS_AXI (1'b1),
        .CFI_MIN_FREQ_MHZ (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk (aclk),
        .aresetn (aresetn),
        .clear (cam_clear | ~cfg_monitor_enable),
        .i_mon_time (i_mon_time),
        .cmd_addr (s_axi_awaddr),
        .cmd_id (s_axi_awid),
        .cmd_len (s_axi_awlen),
        .cmd_valid (w_mon_cmd_valid),
        .cmd_ready (s_axi_awready),
        .data_id (s_axi_awid),
        .data_last (s_axi_wlast),
        .data_resp (2'b00),
        .data_valid (w_mon_data_valid),
        .data_ready (s_axi_wready),
        .resp_id (s_axi_bid),
        .resp_code (s_axi_bresp),
        .resp_valid (w_mon_resp_valid),
        .resp_ready (s_axi_bready),
        .cfg_freq_sel (cfg_freq_sel),
        .cfg_timeout_cnt (w_timeout_cnt),
        .cfg_error_enable (cfg_error_enable),
        .cfg_compl_enable (cfg_compl_enable),
        .cfg_timeout_enable (cfg_timeout_enable),
        .cfg_threshold_enable (cfg_threshold_enable),
        .cfg_active_trans_threshold (16'(ACTIVE_TRANS_THRESHOLD)),
        .cfg_axi_pkt_mask (cfg_axi_pkt_mask),
        .monbus_valid (monbus_valid),
        .monbus_ready (monbus_ready),
        .monbus_packet (monbus_packet),
        .monbus_timestamp (monbus_timestamp),
        .active_count (active_transactions),
        /* verilator lint_off PINCONNECTEMPTY */
        .busy (),
        .dropped_count (dropped_count),
        .refused_count (refused_count),
        /* verilator lint_on PINCONNECTEMPTY */
        .perf_completed_count (w_perf_completed_count),
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

endmodule : axi4_slave_wr_monlite
