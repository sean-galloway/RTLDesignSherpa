// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_wr_monlite
// Purpose: AXIL5 Master Write with the lite ocelus (axi_monitor_lite) -- axil5_master_wr plus a fifth of the ocelus gates
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The lite-ocelus sibling of axil5_master_wr_mon (amba/ocelus-lite TASK-001). Same
// core, same taps, same 128-bit packets on the same monbus with the same
// UNIT/AGENT ids, so the arbiter, group and host tooling cannot tell the two
// apart. Different interface: only what the lite can honour is on the port
// list -- no perf window, no debug, no address-range checker, no ID/address
// filters, no per-event masks -- and two status outputs the full ocelus
// does not have (dropped_count, refused_count). The lite never stalls the
// port: an event it cannot deliver is dropped and counted, and a command
// that finds no free table entry is counted and left untracked (its beats
// then report as ORPHAN errors). There is no block_ready and no gating of
// the command handshake; the core's ready goes straight to the port.
//
// Every core parameter and port is declared here verbatim from axil5_master_wr
// and passed through by name; the ocelus section is the same lite tap
// wiring the _mon wrapper carries. Sean, 2026-09-26: "make monlite versions
// of the various axi wrappers".
// ============================================================================
`timescale 1ns / 1ps

module axil5_master_wr_monlite
#(
    // ---- Ocelus parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the ocelus, tie its outputs
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

    // AXI5-Lite ID and optional signal widths
    // AWID/BID and ARID/RID width (IHI 0022L Table A5.2: 0..32).
    // This is a Manager-side interface, where Table B2.2 makes the ID
    // optional (code YS): 0 means no ID -- the m_axil_ ID outputs are
    // driven 0 (the "tied LOW" of A5.1.1) and the ID inputs are ignored.
    parameter int ID_WIDTH           = 4,
    parameter int USER_WIDTH         = 4,

    // AXI5-Lite optional signal groups. All default ON; set a group to 0 and
    // its signals leave the SKID payload entirely.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW    = 2,
    parameter int SKID_DEPTH_W     = 4,
    parameter int SKID_DEPTH_B     = 2,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int SW       = DW / 8,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    // One poison bit per 64-bit granule, matching axil5_opt_slave
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1,

    parameter int AWSize = AW + 3 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0),

    parameter int WSize  = DW + SW +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_POISON ? PW : 0),

    parameter int BSize  = 2 + ID_WIDTH +
                             (ENABLE_USER ? UW : 0) +
                             (ENABLE_TRACE ? 1 : 0)
) (

    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // AW channel: fub_ -> m_axil_
    input  logic [IW-1:0]           fub_axil_awid,
    input  logic [AW-1:0]           fub_axil_awaddr,
    input  logic [2:0]              fub_axil_awprot,
    input  logic [UW-1:0]           fub_axil_awuser,
    input  logic                    fub_axil_awtrace,
    input  logic                    fub_axil_awvalid,
    output logic                    fub_axil_awready,
    output logic [IW-1:0]           m_axil_awid,
    output logic [AW-1:0]           m_axil_awaddr,
    output logic [2:0]              m_axil_awprot,
    output logic [UW-1:0]           m_axil_awuser,
    output logic                    m_axil_awtrace,
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
    input  logic [IW-1:0]           m_axil_bid,
    input  logic [1:0]              m_axil_bresp,
    input  logic [UW-1:0]           m_axil_buser,
    input  logic                    m_axil_btrace,
    input  logic                    m_axil_bvalid,
    output logic                    m_axil_bready,
    output logic [IW-1:0]           fub_axil_bid,
    output logic [1:0]              fub_axil_bresp,
    output logic [UW-1:0]           fub_axil_buser,
    output logic                    fub_axil_btrace,
    output logic                    fub_axil_bvalid,
    input  logic                    fub_axil_bready,

    // Status output for clock gating
    output logic                       busy,

    // ---- Ocelus control (the lite's own set: nothing here it cannot honour) ----
    input  logic                                  cam_clear,           // sync clear of the ocelus's table (named as on the _mon wrapper: pin-compatible)
    input  logic                                  cfg_monitor_enable,  // 0 = ocelus inert, table held clear
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
    input  ocelus_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Ocelus bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output ocelus_common_pkg::monitor_packet_t   monbus_packet,
    output ocelus_common_pkg::monbus_timestamp_t monbus_timestamp,
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
    //   ID_WIDTH: 0..32 (Table A5.2). Manager-side: 0 = no ID is legal (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_master_wr_monlite: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 0 || ID_WIDTH > 32)
            $fatal(1, "axil5_master_wr_monlite: ID_WIDTH=%0d out of range 0..32 (IHI 0022L Table A5.2)",
                   ID_WIDTH);
    end
`endif

    // ------------------------------------------------------------------------
    // The core, passed through untouched (no ocelus gating on any handshake)
    // ------------------------------------------------------------------------
    axil5_master_wr #(
        .AXIL_ADDR_WIDTH             (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH             (AXIL_DATA_WIDTH),
        .ID_WIDTH                    (ID_WIDTH),
        .USER_WIDTH                  (USER_WIDTH),
        .ENABLE_USER                 (ENABLE_USER),
        .ENABLE_TRACE                (ENABLE_TRACE),
        .ENABLE_POISON               (ENABLE_POISON),
        .SKID_DEPTH_AW               (SKID_DEPTH_AW),
        .SKID_DEPTH_W                (SKID_DEPTH_W),
        .SKID_DEPTH_B                (SKID_DEPTH_B),
        .AW                          (AW),
        .DW                          (DW),
        .SW                          (SW),
        .UW                          (UW),
        .PW                          (PW),
        .AWSize                      (AWSize),
        .WSize                       (WSize),
        .BSize                       (BSize)
    ) u_core (
        .aclk                        (aclk),
        .aresetn                     (aresetn),
        .fub_awid                    (fub_axil_awid),
        .fub_awaddr                  (fub_axil_awaddr),
        .fub_awprot                  (fub_axil_awprot),
        .fub_awuser                  (fub_axil_awuser),
        .fub_awtrace                 (fub_axil_awtrace),
        .fub_awvalid                 (fub_axil_awvalid),
        .fub_awready                 (fub_axil_awready),
        .m_axil_awid                 (m_axil_awid),
        .m_axil_awaddr               (m_axil_awaddr),
        .m_axil_awprot               (m_axil_awprot),
        .m_axil_awuser               (m_axil_awuser),
        .m_axil_awtrace              (m_axil_awtrace),
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
        .m_axil_bid                  (m_axil_bid),
        .m_axil_bresp                (m_axil_bresp),
        .m_axil_buser                (m_axil_buser),
        .m_axil_btrace               (m_axil_btrace),
        .m_axil_bvalid               (m_axil_bvalid),
        .m_axil_bready               (m_axil_bready),
        .fub_bid                     (fub_axil_bid),
        .fub_bresp                   (fub_axil_bresp),
        .fub_buser                   (fub_axil_buser),
        .fub_btrace                  (fub_axil_btrace),
        .fub_bvalid                  (fub_axil_bvalid),
        .fub_bready                  (fub_axil_bready),
        .busy                        (busy)
    );

    // ------------------------------------------------------------------------
    // Ocelus taps. cfg_monitor_enable gates every tap and holds the table
    // clear; cfg_timeout_cycles is MICROSECONDS at full width, 0 = never.
    // ------------------------------------------------------------------------
    logic        w_mon_cmd_valid;
    logic        w_mon_data_valid;
    logic        w_mon_resp_valid;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;
    // Monitor tap: the FUB-side handshake (owner rule: monitors always tap the
    // FUB side, for timing -- the tap then never sits on the external bus I/O).
    // monitor-lite has no block_ready: a command that finds no free slot is
    // counted in refused_count, never stalled.
    assign w_mon_cmd_valid  = fub_axil_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = fub_axil_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = fub_axil_bvalid & cfg_monitor_enable;
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    // AXI5-Lite IDs to the ocelus (amba #104). AWID/BID exist on AXI5-Lite
    // and a Subordinate may return responses out of order across IDs (IHI
    // 0022L B2.1.5), so the ocelus pairs each B with the oldest command of
    // the SAME ID, as on AXI4 -- with the ID tied 0 it paired every B with the
    // oldest command outstanding, whichever one the B answered.
    // W carries no ID (Table B2.2). It needs none: write data follows AW order
    // (A5.5; the Resource Plane exception is credited transport only) and may
    // lead its AW (A2.6), and the core attributes W in AW order from its own
    // bookkeeping, never from data_id -- so data_id is tied 0, not fed AWID
    // (the AWID on the bus at W time belongs to whichever AW is presented
    // then, not to the burst on W).
    // ID_WIDTH = 0 (legal on a Manager, Table B2.2 YS): the IDs read 0.
    logic [IW-1:0] w_mon_cmd_id, w_mon_resp_id;
    assign w_mon_cmd_id  = (ID_WIDTH > 0) ? fub_axil_awid : '0;
    assign w_mon_resp_id = (ID_WIDTH > 0) ? fub_axil_bid : '0;

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
        .IS_READ              (1'b0),
        .IS_AXI               (1'b1),
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) axi_monitor_lite_inst (
        .aclk                       (aclk),
        .aresetn                    (aresetn),
        .clear                      (cam_clear | ~cfg_monitor_enable),
        .i_mon_time                 (i_mon_time),
        .cmd_addr                   (fub_axil_awaddr),
        .cmd_id                     (w_mon_cmd_id),
        .cmd_len                    (8'h00),
        .cmd_valid                  (w_mon_cmd_valid),
        .cmd_ready                  (fub_axil_awready),
        .data_id                    ('0),
        .data_last                  (1'b1),
        .data_resp                  (2'b00),
        .data_valid                 (w_mon_data_valid),
        .data_ready                 (fub_axil_wready),
        .resp_id                    (w_mon_resp_id),
        .resp_code                  (fub_axil_bresp),
        .resp_valid                 (w_mon_resp_valid),
        .resp_ready                 (fub_axil_bready),
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
