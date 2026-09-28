// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis4_slave_monlite_cg
// Purpose: AXI4-Stream Slave with the lite stream monitor, clock gated -- axis4_slave_monlite behind one amba_clock_gate_ctrl
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-27
//
// ============================================================================
// The clock-gated twin of axis4_slave_monlite (amba/monitor-lite TASK-003). One
// amba_clock_gate_ctrl gates the whole inner wrapper -- endpoint and monitor.
// Gating terms are axis4_slave_cg's verbatim -- user_valid from the upstream
// tvalid and the core's busy (never a peer's READY), axi_valid from the
// downstream tvalid -- plus the monitor's own activity: a packet queued on the
// monbus or a packet open on the tapped port keeps the clock alive, so a
// stopped monitor never holds an undeliverable packet or loses a TLAST.
// The upstream READY is masked with !cg_gating: it is driven by a register on
// the GATED clock, which HOLDS its last value when the clock stops, and a
// producer seeing a stale READY would consider a beat accepted that nobody
// observed (the rule every _cg wrapper in rtl/amba follows). monbus_valid is
// masked the same way so the consumer never sees a valid a stopped lite
// could not complete.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"
module axis4_slave_monlite_cg
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h09,
    parameter logic [15:0] AGENT_ID               = 16'h0064,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CG_IDLE_COUNT_WIDTH    = 4,      // width of the idle countdown (sizes cfg_cg_idle_count)
    // ---- Core parameters (passed through verbatim to axis4_slave_monlite) ----
    parameter int      SKID_DEPTH           = 4,
    parameter int      AXIS_DATA_WIDTH      = 32,
    parameter int      AXIS_ID_WIDTH        = 8,
    parameter int      AXIS_DEST_WIDTH      = 4,
    parameter int      AXIS_USER_WIDTH      = 1,  // Short and calculated params
    parameter int      DW                   = AXIS_DATA_WIDTH,
    parameter int      IW                   = AXIS_ID_WIDTH,
    parameter int      DESTW                = AXIS_DEST_WIDTH,
    parameter int      UW                   = AXIS_USER_WIDTH,
    parameter int      SW                   = DW / 8,
    parameter int      IW_WIDTH             = (IW > 0) ? IW : 1,  // Minimum 1 bit for zero-width signals
    parameter int      DESTW_WIDTH          = (DESTW > 0) ? DESTW : 1,
    parameter int      UW_WIDTH             = (UW > 0) ? UW : 1,
    parameter int      TSize                = DW+SW+1+IW_WIDTH+DESTW_WIDTH+UW_WIDTH  // tdata+tstrb+tlast+tid+tdest+tuser
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  logic [DW-1:0]             s_axis_tdata,
    input  logic [SW-1:0]             s_axis_tstrb,
    input  logic                      s_axis_tlast,
    input  logic [IW_WIDTH-1:0]       s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]    s_axis_tdest,
    input  logic [UW_WIDTH-1:0]       s_axis_tuser,
    input  logic                      s_axis_tvalid,
    output logic                      s_axis_tready,
    output logic [DW-1:0]             fub_axis_tdata,
    output logic [SW-1:0]             fub_axis_tstrb,
    output logic                      fub_axis_tlast,
    output logic [IW_WIDTH-1:0]       fub_axis_tid,
    output logic [DESTW_WIDTH-1:0]    fub_axis_tdest,
    output logic [UW_WIDTH-1:0]       fub_axis_tuser,
    output logic                      fub_axis_tvalid,
    input  logic                      fub_axis_tready,
    output logic                      busy,
    // ---- Monitor control (the lite's own set: nothing here it cannot honour) ----
    input  logic                                  cam_clear,           // sync clear of the monitor's state (named as on the AXI lite wrappers). Legal only while idle
    input  logic                                  cfg_monitor_enable,  // 0 = monitor inert, state held clear
    input  logic                                  cfg_error_enable,
    input  logic                                  cfg_timeout_enable,
    input  logic                                  cfg_compl_enable,
    input  logic                                  cfg_credit_enable,
    input  logic                                  cfg_channel_enable,
    input  logic                                  cfg_stream_enable,
    input  logic                                  cfg_strb_check_enable, // Error/STRB_INVALID on an all-zero TSTRB beat
    input  logic [15:0]                           cfg_timeout_cycles,  // MICROSECONDS of stall or in-packet gap; 0 = never
    input  logic [3:0]                            cfg_freq_sel,        // counter_freq_invariant LUT index
    input  logic [15:0]                           cfg_axis_pkt_mask,   // drop mask by packet type
    input  logic [31:0]                           cfg_stall_threshold, // stall CYCLES above which Credit/BACKPRESSURE reports; 0 = off
    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Monitor bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,
    // ---- Status ----
    output logic                                  in_packet,           // a beat accepted on the tapped port, TLAST not yet seen
    output logic [31:0]                           packet_count,        // packets completed on the tapped port
    output logic [15:0]                           error_count,         // error packets emitted
    output logic [15:0]                           dropped_count,        // events lost to monbus backpressure since the last report
    // ---- Clock gating (as on the family's _cg wrapper: pin-compatible) ----
    input  logic                                  cfg_cg_enable,       // enable clock gating
    input  logic [CG_IDLE_COUNT_WIDTH-1:0]        cfg_cg_idle_count,   // idle cycles before gating
    output logic                                  cg_gating,           // gated clock is stopped
    output logic                                  cg_idle              // no activity observed
);
    // ------------------------------------------------------------------------
    // Clock gating (axis4_slave_cg's logic, plus the monitor's activity)
    // ------------------------------------------------------------------------
    logic gated_aclk;
    logic user_valid, axi_valid;
    logic int_tready, int_busy;
    logic w_monbus_valid, w_in_packet;
    assign user_valid = s_axis_tvalid || int_busy || w_monbus_valid || w_in_packet;   // never a peer's READY
    assign axi_valid  = fub_axis_tvalid;
    assign s_axis_tready  = cg_gating ? 1'b0 : int_tready;
    assign monbus_valid = w_monbus_valid & ~cg_gating;
    assign in_packet    = w_in_packet;
    assign busy         = int_busy;

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
    axis4_slave_monlite #(
        .USE_MONITOR            (USE_MONITOR),
        .UNIT_ID                (UNIT_ID),
        .AGENT_ID               (AGENT_ID),
        .OUT_DEPTH              (OUT_DEPTH),
        .ACLK_MHZ               (ACLK_MHZ),
        .CFI_MIN_FREQ_MHZ       (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ       (CFI_MAX_FREQ_MHZ),
        .SKID_DEPTH            (SKID_DEPTH),
        .AXIS_DATA_WIDTH       (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH         (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH       (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH       (AXIS_USER_WIDTH),
        .DW                    (DW),
        .IW                    (IW),
        .DESTW                 (DESTW),
        .UW                    (UW),
        .SW                    (SW),
        .IW_WIDTH              (IW_WIDTH),
        .DESTW_WIDTH           (DESTW_WIDTH),
        .UW_WIDTH              (UW_WIDTH),
        .TSize                 (TSize)
    ) u_monlite (
        .aclk                   (gated_aclk),
        .aresetn                (aresetn),
        .s_axis_tdata          (s_axis_tdata),
        .s_axis_tstrb          (s_axis_tstrb),
        .s_axis_tlast          (s_axis_tlast),
        .s_axis_tid            (s_axis_tid),
        .s_axis_tdest          (s_axis_tdest),
        .s_axis_tuser          (s_axis_tuser),
        .s_axis_tvalid         (s_axis_tvalid),
        .s_axis_tready         (int_tready),
        .fub_axis_tdata        (fub_axis_tdata),
        .fub_axis_tstrb        (fub_axis_tstrb),
        .fub_axis_tlast        (fub_axis_tlast),
        .fub_axis_tid          (fub_axis_tid),
        .fub_axis_tdest        (fub_axis_tdest),
        .fub_axis_tuser        (fub_axis_tuser),
        .fub_axis_tvalid       (fub_axis_tvalid),
        .fub_axis_tready       (fub_axis_tready),
        .busy                  (int_busy),
        .monbus_valid          (w_monbus_valid),
        .in_packet             (w_in_packet),
        .cam_clear             (cam_clear),
        .cfg_monitor_enable    (cfg_monitor_enable),
        .cfg_error_enable      (cfg_error_enable),
        .cfg_timeout_enable    (cfg_timeout_enable),
        .cfg_compl_enable      (cfg_compl_enable),
        .cfg_credit_enable     (cfg_credit_enable),
        .cfg_channel_enable    (cfg_channel_enable),
        .cfg_stream_enable     (cfg_stream_enable),
        .cfg_strb_check_enable (cfg_strb_check_enable),
        .cfg_timeout_cycles    (cfg_timeout_cycles),
        .cfg_freq_sel          (cfg_freq_sel),
        .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
        .cfg_stall_threshold   (cfg_stall_threshold),
        .i_mon_time            (i_mon_time),
        .monbus_ready          (monbus_ready),
        .monbus_packet         (monbus_packet),
        .monbus_timestamp      (monbus_timestamp),
        .packet_count          (packet_count),
        .error_count           (error_count),
        .dropped_count         (dropped_count)
    );

endmodule : axis4_slave_monlite_cg
