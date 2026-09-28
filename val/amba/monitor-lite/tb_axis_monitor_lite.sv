// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_axis_monitor_lite
// Purpose: Test fixture for axis_monitor_lite (amba/monitor-lite TASK-003).
//          The core is a TAP with no data port: it never sees TDATA or TUSER.
//          The framework AXIS BFMs need the full signal set on the top level
//          to bind to, so this fixture exposes a complete `axis_*` stream --
//          the master BFM drives the payload side, the slave BFM drives
//          tready, and the core watches the handshake between them. TDATA and
//          TUSER terminate here. Same role as tb_axis4_pattern_pair.sv.
`timescale 1ns / 1ps
module tb_axis_monitor_lite
    import monitor_common_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID          = 8'h09,
    parameter logic [15:0] AGENT_ID         = 16'h0064,
    parameter int          AXIS_DATA_WIDTH  = 32,
    parameter int          AXIS_ID_WIDTH    = 8,
    parameter int          AXIS_DEST_WIDTH  = 4,
    parameter int          AXIS_USER_WIDTH  = 1,
    parameter int          OUT_DEPTH        = 4,
    parameter int          ACLK_MHZ         = 100,
    parameter int          DW    = AXIS_DATA_WIDTH,
    parameter int          SW    = AXIS_DATA_WIDTH / 8,
    parameter int          IW    = (AXIS_ID_WIDTH   > 0) ? AXIS_ID_WIDTH   : 1,
    parameter int          DESTW = (AXIS_DEST_WIDTH > 0) ? AXIS_DEST_WIDTH : 1,
    parameter int          UW    = (AXIS_USER_WIDTH > 0) ? AXIS_USER_WIDTH : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,
    input  monbus_timestamp_t     i_mon_time,

    // The stream under observation (both BFMs bind here)
    input  logic [DW-1:0]         axis_tdata,     // terminated: the monitor has no data port
    input  logic [SW-1:0]         axis_tstrb,
    input  logic                  axis_tlast,
    input  logic [IW-1:0]         axis_tid,
    input  logic [DESTW-1:0]      axis_tdest,
    input  logic [UW-1:0]         axis_tuser,     // terminated
    input  logic                  axis_tvalid,
    input  logic                  axis_tready,

    // Configuration (the core's names)
    input  logic [3:0]            cfg_freq_sel,
    input  logic [15:0]           cfg_timeout_cnt,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_timeout_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_credit_enable,
    input  logic                  cfg_channel_enable,
    input  logic                  cfg_stream_enable,
    input  logic                  cfg_strb_check_enable,
    input  logic [31:0]           cfg_stall_threshold,
    input  logic [15:0]           cfg_axis_pkt_mask,

    // Monitor bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic                  busy,
    output logic                  in_packet,
    output logic [31:0]           packet_count,
    output logic [15:0]           error_count,
    output logic [15:0]           dropped_count
);

    /* verilator lint_off UNUSEDSIGNAL */
    logic [DW-1:0] unused_tdata;
    logic [UW-1:0] unused_tuser;
    assign unused_tdata = axis_tdata;
    assign unused_tuser = axis_tuser;
    /* verilator lint_on UNUSEDSIGNAL */

    axis_monitor_lite #(
        .UNIT_ID          (UNIT_ID),
        .AGENT_ID         (AGENT_ID),
        .DATA_WIDTH       (AXIS_DATA_WIDTH),
        .ID_WIDTH         (AXIS_ID_WIDTH),
        .DEST_WIDTH       (AXIS_DEST_WIDTH),
        .OUT_DEPTH        (OUT_DEPTH),
        .CFI_MIN_FREQ_MHZ (ACLK_MHZ),
        .CFI_MAX_FREQ_MHZ (ACLK_MHZ)
    ) u_mon (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .clear                 (clear),
        .i_mon_time            (i_mon_time),
        .axis_tvalid           (axis_tvalid),
        .axis_tready           (axis_tready),
        .axis_tlast            (axis_tlast),
        .axis_tid              (axis_tid),
        .axis_tdest            (axis_tdest),
        .axis_tstrb            (axis_tstrb),
        .cfg_freq_sel          (cfg_freq_sel),
        .cfg_timeout_cnt       (cfg_timeout_cnt),
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
        .busy                  (busy),
        .in_packet             (in_packet),
        .packet_count          (packet_count),
        .error_count           (error_count),
        .dropped_count         (dropped_count)
    );

endmodule : tb_axis_monitor_lite
