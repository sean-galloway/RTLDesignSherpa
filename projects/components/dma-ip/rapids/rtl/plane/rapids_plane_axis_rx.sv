// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_plane_axis_rx
// Purpose: AXIS network plane, sink ingress (RX): axis4_slave_monlite
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_planes.md
// Subsystem: rapids
//
// Author: sean galloway
// Created: 2026-10-15
//
// ============================================================================
// A RAPIDS network PLANE: the endpoint that turns the core's ingress AXIS
// stream into a network link, plus its monitor-lite. Every plane has the same
// parameters and the same INNER interface (core-facing AXIS stream, monitor
// cfg in, monitor status and monbus out), so a top selects AXIS or CXS by the
// module name and its outer pins alone:
//
//   rapids_plane_axis_rx / rapids_plane_cxs_rx
//
// The monitor cfg/status are the SRC_/SNK_ AXIS-monitor CSRs (rapids
// TASK-015); a CXS plane maps the same enables onto cxs_monitor_lite's classes.
// The monbus output is client 1 of the core half's monbus_arbiter.
// ============================================================================

`timescale 1ns / 1ps

module rapids_plane_axis_rx #(
    parameter bit USE_MONITOR      = 1'b1,
    parameter int MON_UNIT_ID      = 1,
    parameter int MON_AGENT_ID     = 10,
    parameter int ACLK_MHZ         = 100,     // the monitor's microsecond tick
    parameter int DATA_WIDTH       = 512,
    parameter int AXIS_ID_WIDTH    = 8,
    parameter int AXIS_DEST_WIDTH  = 4,
    parameter int AXIS_USER_WIDTH  = 1,
    parameter int SKID_DEPTH       = 4,
    parameter int DW               = DATA_WIDTH,
    parameter int SW               = DW / 8
) (
    input  logic                                  clk,
    input  logic                                  rst_n,

    // ---- Inner (core-facing) AXIS stream ----
    output logic [DW-1:0]                         fub_axis_tdata,
    output logic [SW-1:0]                         fub_axis_tstrb,
    output logic                                  fub_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]              fub_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]            fub_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]            fub_axis_tuser,
    output logic                                  fub_axis_tvalid,
    input  logic                                  fub_axis_tready,

    // ---- Monitor configuration (the AXIS-monitor CSRs) ----
    input  logic                                  cfg_mon_enable,
    input  logic                                  cfg_mon_err_enable,
    input  logic                                  cfg_mon_compl_enable,
    input  logic                                  cfg_mon_perf_enable,
    input  logic                                  cfg_mon_timeout_enable,
    input  logic [31:0]                           cfg_mon_timeout_cycles,   // [15:0] MICROSECONDS, 0 = never
    input  logic [31:0]                           cfg_mon_latency_thresh,   // stall CYCLES for Credit events
    input  logic [15:0]                           cfg_mon_pkt_mask,

    // ---- Monitor status and bus ----
    output logic                                  sts_mon_busy,
    output logic [31:0]                           sts_mon_packet_count,
    output logic [15:0]                           sts_mon_error_count,
    output logic [15:0]                           sts_mon_dropped_count,
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output ocelus_common_pkg::monitor_packet_t   monbus_packet,
    output ocelus_common_pkg::monbus_timestamp_t monbus_timestamp,

    // ---- Outer: the AXIS network port ----
    input  logic [DW-1:0]                             s_axis_tdata,
    input  logic [SW-1:0]                             s_axis_tstrb,
    input  logic                                      s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]                  s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]                s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]                s_axis_tuser,
    input  logic                                      s_axis_tvalid,
    output logic                                      s_axis_tready
);

    // axis4_slave_monlite = the axis4_slave skid stage (SKID_DEPTH deep, present in
    // every build) plus an axis_monitor_lite TAP built only when USE_MONITOR.
    // Moved here unchanged from rapids_snk (both trees) when the network
    // endpoint became a plane; the class-enable mapping is the original's.
    // The lite's timeout is 16 bits of microseconds; the register is 32 wide.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [15:0] unused_mon_timeout_hi;
    assign unused_mon_timeout_hi = cfg_mon_timeout_cycles[31:16];
    /* verilator lint_on UNUSEDSIGNAL */

    axis4_slave_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'(MON_UNIT_ID)),
        .AGENT_ID         (16'(MON_AGENT_ID)),
        .OUT_DEPTH        (4),
        .ACLK_MHZ         (ACLK_MHZ),
        .SKID_DEPTH       (SKID_DEPTH),
        .AXIS_DATA_WIDTH  (DW),
        .AXIS_ID_WIDTH    (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH  (AXIS_USER_WIDTH)
    ) u_endpoint (
        .aclk                  (clk),
        .aresetn               (rst_n),
        .s_axis_tdata           (s_axis_tdata),
        .s_axis_tstrb           (s_axis_tstrb),
        .s_axis_tlast           (s_axis_tlast),
        .s_axis_tid             (s_axis_tid),
        .s_axis_tdest           (s_axis_tdest),
        .s_axis_tuser           (s_axis_tuser),
        .s_axis_tvalid          (s_axis_tvalid),
        .s_axis_tready          (s_axis_tready),
        .fub_axis_tdata        (fub_axis_tdata),
        .fub_axis_tstrb        (fub_axis_tstrb),
        .fub_axis_tlast        (fub_axis_tlast),
        .fub_axis_tid          (fub_axis_tid),
        .fub_axis_tdest        (fub_axis_tdest),
        .fub_axis_tuser        (fub_axis_tuser),
        .fub_axis_tvalid       (fub_axis_tvalid),
        .fub_axis_tready       (fub_axis_tready),
        .busy                  (sts_mon_busy),
        .cam_clear             (1'b0),
        .cfg_monitor_enable    (cfg_mon_enable),
        .cfg_error_enable      (cfg_mon_err_enable),
        .cfg_timeout_enable    (cfg_mon_timeout_enable),
        .cfg_compl_enable      (cfg_mon_compl_enable),
        .cfg_credit_enable     (cfg_mon_perf_enable),
        .cfg_channel_enable    (cfg_mon_err_enable),
        .cfg_stream_enable     (cfg_mon_perf_enable),
        .cfg_strb_check_enable (cfg_mon_err_enable),
        .cfg_timeout_cycles    (cfg_mon_timeout_cycles[15:0]),
        .cfg_freq_sel          (4'b0000),
        .cfg_axis_pkt_mask     (cfg_mon_pkt_mask),
        .cfg_stall_threshold   (cfg_mon_latency_thresh),
        .i_mon_time            ('0),
        .monbus_valid          (monbus_valid),
        .monbus_ready          (monbus_ready),
        .monbus_packet         (monbus_packet),
        .monbus_timestamp      (monbus_timestamp),
        /* verilator lint_off PINCONNECTEMPTY */
        .in_packet             (),
        /* verilator lint_on PINCONNECTEMPTY */
        .packet_count          (sts_mon_packet_count),
        .error_count           (sts_mon_error_count),
        .dropped_count         (sts_mon_dropped_count)
    );

endmodule : rapids_plane_axis_rx
