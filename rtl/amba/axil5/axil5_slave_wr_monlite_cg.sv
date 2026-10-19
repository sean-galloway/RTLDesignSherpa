// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_wr_monlite_cg
// Purpose: AXIL5 Slave Write with the lite ocelus, clock gated -- axil5_slave_wr_monlite behind one amba_clock_gate_ctrl
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The clock-gated sibling of axil5_slave_wr_monlite, built exactly as axil5_slave_wr_mon_cg is built
// around axil5_slave_wr_mon (amba/ocelus-lite TASK-001, Sean 2026-09-26: "build the
// monlite_cg wrappers"). One amba_clock_gate_ctrl gates the whole inner
// wrapper; the activity term, the ready masks and the monbus liveness terms
// are the axil5_slave_wr_mon_cg ones verbatim, so val/amba/test_mon_cg_gating.py's six
// phases hold here too (val/amba/ocelus-lite/test_monlite_cg_gating.py).
//
// Activity is derived from VALID signals and outstanding work ONLY, never a
// peer's READY (a consumer parking its response-ready high while idle would
// otherwise pin the block awake). Request-side readys are masked to 0 while
// gated, so nothing is accepted with the clock stopped. A packet parked on
// the ocelus bus, and any occupied table entry, hold the block awake so the
// lite can retire the handshake; the external monbus_valid is masked by
// !cg_gating so the consumer never sees a valid a stopped lite could not
// retire (TASK-070 liveness terms, as on axil5_slave_wr_mon_cg).
//
// Every axil5_slave_wr_monlite parameter and port is declared here verbatim and passed
// through by name; the four clock-gating pins are appended.
// ============================================================================
`timescale 1ns / 1ps

module axil5_slave_wr_monlite_cg
#(
    // ---- Clock gating ----
    parameter int          CG_IDLE_COUNT_WIDTH    = 4,      // width of the idle countdown (sizes cfg_cg_idle_count)

    // ---- Ocelus parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the ocelus, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h02,
    parameter logic [15:0] AGENT_ID               = 16'h0015,
    parameter int          MAX_TRANSACTIONS       = 8,      // table entries; a command finding none is counted, not tracked
    parameter int          ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          N_ADDR_RANGES          = 0,      // address-range checker windows; 0 = not built
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,  // per range: 1 = miss is an error, 0 = hit is a match
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axil5_slave_wr) ----

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

    // AW channel: s_axil_ -> fub_
    input  logic [IW-1:0]           s_axil_awid,
    input  logic [AW-1:0]           s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic [UW-1:0]           s_axil_awuser,
    input  logic                    s_axil_awtrace,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    output logic [IW-1:0]           fub_axil_awid,
    output logic [AW-1:0]           fub_axil_awaddr,
    output logic [2:0]              fub_axil_awprot,
    output logic [UW-1:0]           fub_axil_awuser,
    output logic                    fub_axil_awtrace,
    output logic                    fub_axil_awvalid,
    input  logic                    fub_axil_awready,

    // W channel: s_axil_ -> fub_
    input  logic [DW-1:0]           s_axil_wdata,
    input  logic [SW-1:0]           s_axil_wstrb,
    input  logic [UW-1:0]           s_axil_wuser,
    input  logic [PW-1:0]           s_axil_wpoison,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [DW-1:0]           fub_axil_wdata,
    output logic [SW-1:0]           fub_axil_wstrb,
    output logic [UW-1:0]           fub_axil_wuser,
    output logic [PW-1:0]           fub_axil_wpoison,
    output logic                    fub_axil_wvalid,
    input  logic                    fub_axil_wready,

    // B channel: fub_ -> s_axil_
    input  logic [IW-1:0]           fub_axil_bid,
    input  logic [1:0]              fub_axil_bresp,
    input  logic [UW-1:0]           fub_axil_buser,
    input  logic                    fub_axil_btrace,
    input  logic                    fub_axil_bvalid,
    output logic                    fub_axil_bready,
    output logic [IW-1:0]           s_axil_bid,
    output logic [1:0]              s_axil_bresp,
    output logic [UW-1:0]           s_axil_buser,
    output logic                    s_axil_btrace,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,

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
    output logic [15:0]                           refused_count,        // commands that found no free table entry
    // ---- Clock gating (as on the _mon_cg wrapper: pin-compatible) ----
    input  logic                                  cfg_cg_enable,       // enable clock gating
    input  logic [CG_IDLE_COUNT_WIDTH-1:0]        cfg_cg_idle_count,   // idle cycles before gating
    output logic                                  cg_gating,           // gated clock is stopped
    output logic                                  cg_idle              // no activity observed
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
            $fatal(1, "axil5_slave_wr_monlite_cg: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 1 || ID_WIDTH > 32)
            $fatal(1, "axil5_slave_wr_monlite_cg: ID_WIDTH=%0d out of range 1..32 (IHI 0022L Table A5.2; a Subordinate must carry the ID)",
                   ID_WIDTH);
    end
`endif

    // ------------------------------------------------------------------------
    // Clock gating (the axil5_slave_wr_mon_cg logic, verbatim)
    // ------------------------------------------------------------------------
    logic gated_aclk;
    logic user_valid, axi_valid;
    logic w_monbus_valid;
    logic int_awready, int_wready, int_bready, int_busy;

    assign user_valid = s_axil_awvalid || s_axil_wvalid || s_axil_bvalid || int_busy ||
                        w_monbus_valid || (|active_transactions);
    assign axi_valid  = fub_axil_awvalid || fub_axil_wvalid || fub_axil_bvalid;

    assign s_axil_awready       = cg_gating ? 1'b0 : int_awready;
    assign s_axil_wready        = cg_gating ? 1'b0 : int_wready;
    assign fub_axil_bready      = cg_gating ? 1'b0 : int_bready;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    // ------------------------------------------------------------------------
    // The lite wrapper on the gated clock, passed through by name
    // ------------------------------------------------------------------------
    axil5_slave_wr_monlite #(
        .USE_MONITOR                 (USE_MONITOR),
        .UNIT_ID                     (UNIT_ID),
        .AGENT_ID                    (AGENT_ID),
        .MAX_TRANSACTIONS            (MAX_TRANSACTIONS),
        .ACTIVE_TRANS_THRESHOLD      (ACTIVE_TRANS_THRESHOLD),
        .OUT_DEPTH                   (OUT_DEPTH),
        .N_ADDR_RANGES               (N_ADDR_RANGES),
        .ADDR_RANGE_IS_ERROR         (ADDR_RANGE_IS_ERROR),
        .ACLK_MHZ                    (ACLK_MHZ),
        .CFI_MIN_FREQ_MHZ            (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ            (CFI_MAX_FREQ_MHZ),
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
    ) u_monlite (
        .aclk                        (gated_aclk),
        .aresetn                     (aresetn),
        .s_axil_awid                 (s_axil_awid),
        .s_axil_awaddr               (s_axil_awaddr),
        .s_axil_awprot               (s_axil_awprot),
        .s_axil_awuser               (s_axil_awuser),
        .s_axil_awtrace              (s_axil_awtrace),
        .s_axil_awvalid              (s_axil_awvalid),
        .s_axil_awready              (int_awready),
        .fub_axil_awid               (fub_axil_awid),
        .fub_axil_awaddr             (fub_axil_awaddr),
        .fub_axil_awprot             (fub_axil_awprot),
        .fub_axil_awuser             (fub_axil_awuser),
        .fub_axil_awtrace            (fub_axil_awtrace),
        .fub_axil_awvalid            (fub_axil_awvalid),
        .fub_axil_awready            (fub_axil_awready),
        .s_axil_wdata                (s_axil_wdata),
        .s_axil_wstrb                (s_axil_wstrb),
        .s_axil_wuser                (s_axil_wuser),
        .s_axil_wpoison              (s_axil_wpoison),
        .s_axil_wvalid               (s_axil_wvalid),
        .s_axil_wready               (int_wready),
        .fub_axil_wdata              (fub_axil_wdata),
        .fub_axil_wstrb              (fub_axil_wstrb),
        .fub_axil_wuser              (fub_axil_wuser),
        .fub_axil_wpoison            (fub_axil_wpoison),
        .fub_axil_wvalid             (fub_axil_wvalid),
        .fub_axil_wready             (fub_axil_wready),
        .fub_axil_bid                (fub_axil_bid),
        .fub_axil_bresp              (fub_axil_bresp),
        .fub_axil_buser              (fub_axil_buser),
        .fub_axil_btrace             (fub_axil_btrace),
        .fub_axil_bvalid             (fub_axil_bvalid),
        .fub_axil_bready             (int_bready),
        .s_axil_bid                  (s_axil_bid),
        .s_axil_bresp                (s_axil_bresp),
        .s_axil_buser                (s_axil_buser),
        .s_axil_btrace               (s_axil_btrace),
        .s_axil_bvalid               (s_axil_bvalid),
        .s_axil_bready               (s_axil_bready),
        .busy                        (int_busy),
        .cam_clear                   (cam_clear),
        .cfg_monitor_enable          (cfg_monitor_enable),
        .cfg_error_enable            (cfg_error_enable),
        .cfg_timeout_enable          (cfg_timeout_enable),
        .cfg_compl_enable            (cfg_compl_enable),
        .cfg_threshold_enable        (cfg_threshold_enable),
        .cfg_timeout_cycles          (cfg_timeout_cycles),
        .cfg_freq_sel                (cfg_freq_sel),
        .cfg_axi_pkt_mask            (cfg_axi_pkt_mask),
        .cfg_latency_threshold       (cfg_latency_threshold),
        .cfg_addr_check_enable       (cfg_addr_check_enable),
        .cfg_addr_match_enable       (cfg_addr_match_enable),
        .cfg_addr_range_enable       (cfg_addr_range_enable),
        .cfg_addr_range_low          (cfg_addr_range_low),
        .cfg_addr_range_high         (cfg_addr_range_high),
        .i_mon_time                  (i_mon_time),
        .monbus_valid                (w_monbus_valid),
        .monbus_ready                (monbus_ready),
        .monbus_packet               (monbus_packet),
        .monbus_timestamp            (monbus_timestamp),
        .active_transactions         (active_transactions),
        .error_count                 (error_count),
        .transaction_count           (transaction_count),
        .dropped_count               (dropped_count),
        .refused_count               (refused_count)
    );

    // Liveness: a packet the stopped lite could not retire is never shown
    // to the consumer; once pending terms are high, gating cannot engage.
    assign monbus_valid = w_monbus_valid && !cg_gating;
    assign busy         = int_busy;

endmodule : axil5_slave_wr_monlite_cg
