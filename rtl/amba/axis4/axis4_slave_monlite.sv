// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis4_slave_monlite
// Purpose: AXI4-Stream Slave with the lite stream monitor (axis_monitor_lite) -- axis4_slave plus a tap on its s_axis_* port
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite_wrappers.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-27
//
// ============================================================================
// The lite-monitor sibling of axis4_slave (amba/monitor-lite TASK-003). The
// stream endpoint is passed through untouched; axis_monitor_lite TAPS the
// upstream (s_axis_*) port -- the external one -- and emits the AXIS packet
// classes (Stream, Credit, Channel) plus Error / Timeout / Completion on the
// same monbus handshake, UNIT/AGENT ids and 128-bit packet as every other
// monitor, so the arbiter, group and host tooling see one more producer.
// The monitor drives nothing: both tvalid and tready of the tapped port are
// inputs to it, and an event the monbus will not take is dropped and COUNTED.
//
// Every core parameter and port is declared here verbatim from axis4_slave
// and passed through by name. cfg_monitor_enable gates the tap and holds the
// monitor clear; cfg_timeout_cycles is MICROSECONDS, 0 = never.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"
module axis4_slave_monlite
#(
    // ---- Monitor parameters ----
    parameter bit          USE_MONITOR            = 1'b1,   // 0 = omit the monitor, tie its outputs
    parameter logic [7:0]  UNIT_ID                = 8'h09,
    parameter logic [15:0] AGENT_ID               = 16'h0064,
    parameter int          OUT_DEPTH              = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ               = 100,
    parameter int          CFI_MIN_FREQ_MHZ       = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ       = ACLK_MHZ,
    // ---- Core parameters (passed through verbatim to axis4_slave) ----
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
    output logic [15:0]                           dropped_count        // events lost to monbus backpressure since the last report
);
    // ------------------------------------------------------------------------
    // The core, passed through untouched (nothing gates the stream)
    // ------------------------------------------------------------------------
    axis4_slave #(
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
    ) u_core (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .s_axis_tdata          (s_axis_tdata),
        .s_axis_tstrb          (s_axis_tstrb),
        .s_axis_tlast          (s_axis_tlast),
        .s_axis_tid            (s_axis_tid),
        .s_axis_tdest          (s_axis_tdest),
        .s_axis_tuser          (s_axis_tuser),
        .s_axis_tvalid         (s_axis_tvalid),
        .s_axis_tready         (s_axis_tready),
        .fub_axis_tdata        (fub_axis_tdata),
        .fub_axis_tstrb        (fub_axis_tstrb),
        .fub_axis_tlast        (fub_axis_tlast),
        .fub_axis_tid          (fub_axis_tid),
        .fub_axis_tdest        (fub_axis_tdest),
        .fub_axis_tuser        (fub_axis_tuser),
        .fub_axis_tvalid       (fub_axis_tvalid),
        .fub_axis_tready       (fub_axis_tready),
        .busy                  (busy)
    );

    // ------------------------------------------------------------------------
    // The tap. cfg_monitor_enable gates tvalid into the monitor and holds it
    // clear; cfg_timeout_cycles == 0 maps to the lite's "never" (16'hFFFF).
    // ------------------------------------------------------------------------
    logic        w_mon_tvalid;
    logic [15:0] w_timeout_cnt;
    logic        w_mon_busy;
    assign w_mon_tvalid  = s_axis_tvalid & cfg_monitor_enable;
    assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        axis_monitor_lite #(
            .UNIT_ID          (UNIT_ID),
            .AGENT_ID         (AGENT_ID),
            .DATA_WIDTH       (AXIS_DATA_WIDTH),
            .ID_WIDTH         (AXIS_ID_WIDTH),
            .DEST_WIDTH       (AXIS_DEST_WIDTH),
            .OUT_DEPTH        (OUT_DEPTH),
            .CFI_MIN_FREQ_MHZ (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ (CFI_MAX_FREQ_MHZ)
        ) u_axis_monitor_lite (
            .aclk                  (aclk),
            .aresetn               (aresetn),
            .clear                 (cam_clear | ~cfg_monitor_enable),
            .i_mon_time            (i_mon_time),
            .axis_tvalid           (w_mon_tvalid),
            .axis_tready           (s_axis_tready),
            .axis_tlast            (s_axis_tlast),
            .axis_tid              (s_axis_tid),
            .axis_tdest            (s_axis_tdest),
            .axis_tstrb            (s_axis_tstrb),
            .cfg_freq_sel          (cfg_freq_sel),
            .cfg_timeout_cnt       (w_timeout_cnt),
            .cfg_error_enable      (cfg_error_enable),
            .cfg_timeout_enable    (cfg_timeout_enable),
            .cfg_compl_enable      (cfg_compl_enable),
            .cfg_credit_enable     (cfg_credit_enable),
            .cfg_channel_enable    (cfg_channel_enable),
            .cfg_stream_enable     (cfg_stream_enable),
            .cfg_strb_check_enable (cfg_strb_check_enable),
            .cfg_stall_threshold   (cfg_stall_threshold),
            .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
            .monbus_valid          (monbus_valid),
            .monbus_ready          (monbus_ready),
            .monbus_packet         (monbus_packet),
            .monbus_timestamp      (monbus_timestamp),
            .busy                  (w_mon_busy),
            .in_packet             (in_packet),
            .packet_count          (packet_count),
            .error_count           (error_count),
            .dropped_count         (dropped_count)
        );
    end else begin : gen_no_monitor
        assign monbus_valid     = 1'b0;
        assign monbus_packet    = '0;
        assign monbus_timestamp = '0;
        assign w_mon_busy       = 1'b0;
        assign in_packet        = 1'b0;
        assign packet_count     = '0;
        assign error_count      = '0;
        assign dropped_count    = '0;
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_mon_busy;
    assign unused_mon_busy = w_mon_busy;   // the _cg twin folds it into its wake term
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : axis4_slave_monlite
