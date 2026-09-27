// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_wr_monlite_cg
// Purpose: AXIL5 Master Write with the lite monitor, clock gated -- axil5_master_wr_monlite behind one amba_clock_gate_ctrl
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-26
//
// ============================================================================
// The clock-gated sibling of axil5_master_wr_monlite, built exactly as axil5_master_wr_mon_cg is built
// around axil5_master_wr_mon (amba/monitor-lite TASK-001, Sean 2026-09-26: "build the
// monlite_cg wrappers"). One amba_clock_gate_ctrl gates the whole inner
// wrapper; the activity term, the ready masks and the monbus liveness terms
// are the axil5_master_wr_mon_cg ones verbatim, so val/amba/test_mon_cg_gating.py's six
// phases hold here too (val/amba/monitor-lite/test_monlite_cg_gating.py).
//
// Activity is derived from VALID signals and outstanding work ONLY, never a
// peer's READY (a consumer parking its response-ready high while idle would
// otherwise pin the block awake). Request-side readys are masked to 0 while
// gated, so nothing is accepted with the clock stopped. A packet parked on
// the monitor bus, and any occupied table entry, hold the block awake so the
// lite can retire the handshake; the external monbus_valid is masked by
// !cg_gating so the consumer never sees a valid a stopped lite could not
// retire (TASK-070 liveness terms, as on axil5_master_wr_mon_cg).
//
// Every axil5_master_wr_monlite parameter and port is declared here verbatim and passed
// through by name; the four clock-gating pins are appended.
// ============================================================================
`timescale 1ns / 1ps

module axil5_master_wr_monlite_cg
#(
    // ---- Clock gating ----
    parameter int          CG_IDLE_COUNT_WIDTH    = 4,      // width of the idle countdown (sizes cfg_cg_idle_count)

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
    output logic [15:0]                           refused_count,        // commands that found no free table entry
    // ---- Clock gating (as on the _mon_cg wrapper: pin-compatible) ----
    input  logic                                  cfg_cg_enable,       // enable clock gating
    input  logic [CG_IDLE_COUNT_WIDTH-1:0]        cfg_cg_idle_count,   // idle cycles before gating
    output logic                                  cg_gating,           // gated clock is stopped
    output logic                                  cg_idle              // no activity observed
);

    // ------------------------------------------------------------------------
    // Clock gating (the axil5_master_wr_mon_cg logic, verbatim)
    // ------------------------------------------------------------------------
    logic gated_aclk;
    logic user_valid, axi_valid;
    logic w_monbus_valid;
    logic int_awready, int_wready, int_bready, int_busy;

    assign user_valid = fub_axil_awvalid || fub_axil_wvalid || fub_axil_bvalid || int_busy ||
                        w_monbus_valid || (|active_transactions);
    assign axi_valid  = m_axil_awvalid || m_axil_wvalid || m_axil_bvalid;

    assign fub_axil_awready     = cg_gating ? 1'b0 : int_awready;
    assign fub_axil_wready      = cg_gating ? 1'b0 : int_wready;
    assign m_axil_bready        = cg_gating ? 1'b0 : int_bready;

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
    axil5_master_wr_monlite #(
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
    ) u_monlite (
        .aclk                        (gated_aclk),
        .aresetn                     (aresetn),
        .fub_axil_awaddr             (fub_axil_awaddr),
        .fub_axil_awprot             (fub_axil_awprot),
        .fub_axil_awlock             (fub_axil_awlock),
        .fub_axil_awuser             (fub_axil_awuser),
        .fub_axil_awtrace            (fub_axil_awtrace),
        .fub_axil_awloop             (fub_axil_awloop),
        .fub_axil_awmpam             (fub_axil_awmpam),
        .fub_axil_awmecid            (fub_axil_awmecid),
        .fub_axil_awnsaid            (fub_axil_awnsaid),
        .fub_axil_awvalid            (fub_axil_awvalid),
        .fub_axil_awready            (int_awready),
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
        .fub_axil_wdata              (fub_axil_wdata),
        .fub_axil_wstrb              (fub_axil_wstrb),
        .fub_axil_wuser              (fub_axil_wuser),
        .fub_axil_wpoison            (fub_axil_wpoison),
        .fub_axil_wvalid             (fub_axil_wvalid),
        .fub_axil_wready             (int_wready),
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
        .m_axil_bready               (int_bready),
        .fub_axil_bresp              (fub_axil_bresp),
        .fub_axil_buser              (fub_axil_buser),
        .fub_axil_btrace             (fub_axil_btrace),
        .fub_axil_bloop              (fub_axil_bloop),
        .fub_axil_bvalid             (fub_axil_bvalid),
        .fub_axil_bready             (fub_axil_bready),
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

endmodule : axil5_master_wr_monlite_cg
