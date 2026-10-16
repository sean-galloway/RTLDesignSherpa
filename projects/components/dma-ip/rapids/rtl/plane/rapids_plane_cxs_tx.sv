// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_plane_cxs_tx
// Purpose: CXS network plane, source egress (TX): axis_to_cxs + cxs_master_monlite
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_planes.md
// Subsystem: rapids
//
// Author: sean galloway
// Created: 2026-10-15
//
// ============================================================================
// A RAPIDS network PLANE: the endpoint that turns the core's egress AXIS
// stream into a network link, plus its monitor-lite. Every plane has the same
// parameters and the same INNER interface (core-facing AXIS stream, monitor
// cfg in, monitor status and monbus out), so a top selects AXIS or CXS by the
// module name and its outer pins alone:
//
//   rapids_plane_axis_tx / rapids_plane_cxs_tx
//
// The monitor cfg/status are the SRC_/SNK_ AXIS-monitor CSRs (rapids
// TASK-015); a CXS plane maps the same enables onto cxs_monitor_lite's classes.
// The monbus output is client 1 of the core half's monbus_arbiter.
// ============================================================================

`timescale 1ns / 1ps

module rapids_plane_cxs_tx #(
    parameter bit USE_MONITOR      = 1'b1,
    parameter int MON_UNIT_ID      = 1,
    parameter int MON_AGENT_ID     = 10,
    parameter int ACLK_MHZ         = 100,     // the monitor's microsecond tick
    parameter int DATA_WIDTH       = 512,
    parameter int AXIS_ID_WIDTH    = 8,
    parameter int AXIS_DEST_WIDTH  = 4,
    parameter int AXIS_USER_WIDTH  = 1,
    parameter int SKID_DEPTH       = 4,
    parameter int CXS_MAX_CREDIT   = 15,      // credits the link carries (1..63, or more with CXS_CREDIT_BEYOND_SPEC)
    parameter bit CXS_CREDIT_BEYOND_SPEC = (CXS_MAX_CREDIT > 63),
    // Channels interleave on the link (CXSSRCID = TID = channel), so packets
    // are framed per stream on the low CXSSRCID bits (IHI 0079D 2.5.2)
    parameter int CXS_STREAM_SRCID_BITS = 3,
    parameter logic [7:0] CXS_IDLE_CYCLES = 8'd32,   // idle RUN cycles before the link goes down
    parameter int DW               = DATA_WIDTH,
    parameter int SW               = DW / 8,
    // The CXS link this plane speaks: Issue D (TSTRB rides in CXSUSER), one
    // packet per flit run (CXSMAXPKTPERFLIT = 2, 16-byte start alignment),
    // TID -> CXSSRCID, TDEST -> CXSTGTID, explicit credit return, no parity.
    parameter int  CXS_N         = 2,
    parameter int  CXS_ALIGN     = 16,
    parameter bit  CARRY_TUSER   = (SW + AXIS_USER_WIDTH) <= 128,
    parameter int  CXS_UW        = SW + (CARRY_TUSER ? AXIS_USER_WIDTH : 0),
    parameter int  IW            = cxs_pkg::port_w(AXIS_ID_WIDTH),
    parameter int  DESTW         = cxs_pkg::port_w(AXIS_DEST_WIDTH),
    parameter int  CNTL_PW       = cxs_pkg::port_w(cxs_pkg::cntl_width(CXS_N, DW, CXS_ALIGN))
) (
    input  logic                                  clk,
    input  logic                                  rst_n,

    // ---- Inner (core-facing) AXIS stream ----
    input  logic [DW-1:0]                         fub_axis_tdata,
    input  logic [SW-1:0]                         fub_axis_tstrb,
    input  logic                                  fub_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]              fub_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]            fub_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]            fub_axis_tuser,
    input  logic                                  fub_axis_tvalid,
    output logic                                  fub_axis_tready,

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
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,

    // ---- Outer: the CXS link (Arm IHI 0079, Issue D) ----
    output logic                                      m_cxs_valid,
    output logic [DW-1:0]                             m_cxs_data,
    output logic [CNTL_PW-1:0]                        m_cxs_cntl,
    output logic [IW-1:0]                             m_cxs_srcid,
    output logic [DESTW-1:0]                          m_cxs_tgtid,
    output logic [CXS_UW-1:0]                         m_cxs_user,
    input  logic                                      m_cxs_crdgnt,
    output logic                                      m_cxs_crdrtn,
    output logic                                      m_cxs_activereq,
    input  logic                                      m_cxs_activeack,
    input  logic                                      m_cxs_deacthint,

    // ---- Plane-specific status ----
    output logic [1:0]                            sts_cxs_link_state,      // {ACTIVEREQ, ACTIVEACK}
    output logic                                  sts_cxs_protocol_error
);


    // The flit between the adapter and the CXS endpoint's FUB port
    logic                w_flit_valid;
    logic                w_flit_ready;
    logic [DW-1:0]       w_flit_data;
    logic [CNTL_PW-1:0]  w_flit_cntl;
    logic [IW-1:0]       w_flit_srcid;
    logic [DESTW-1:0]    w_flit_tgtid;
    logic [CXS_UW-1:0]   w_flit_user;

    // The lite's timeout is 16 bits of microseconds; the register is 32 wide.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [15:0] unused_mon_timeout_hi;
    assign unused_mon_timeout_hi = cfg_mon_timeout_cycles[31:16];
    /* verilator lint_on UNUSEDSIGNAL */

    axis_to_cxs #(
        .DATA_WIDTH           (DW),
        .ID_WIDTH             (AXIS_ID_WIDTH),
        .DEST_WIDTH           (AXIS_DEST_WIDTH),
        .USER_WIDTH           (AXIS_USER_WIDTH),
        .CXS_MAX_PKT_PER_FLIT (CXS_N),
        .CXS_START_ALIGN      (CXS_ALIGN),
        .CARRY_TUSER          (CARRY_TUSER),
        .STREAM_ID_BITS       (CXS_STREAM_SRCID_BITS),
        .STREAM_DEST_BITS     (0)
    ) u_axis_to_cxs (
        .aclk          (clk),
        .aresetn       (rst_n),
        .s_axis_tdata  (fub_axis_tdata),
        .s_axis_tstrb  (fub_axis_tstrb),
        .s_axis_tlast  (fub_axis_tlast),
        .s_axis_tid    (fub_axis_tid),
        .s_axis_tdest  (fub_axis_tdest),
        .s_axis_tuser  (fub_axis_tuser),
        .s_axis_tvalid (fub_axis_tvalid),
        .s_axis_tready (fub_axis_tready),
        .cxs_valid     (w_flit_valid),
        .cxs_ready     (w_flit_ready),
        .cxs_data      (w_flit_data),
        .cxs_cntl      (w_flit_cntl),
        .cxs_srcid     (w_flit_srcid),
        .cxs_tgtid     (w_flit_tgtid),
        .cxs_user      (w_flit_user)
    );

    cxs_master_monlite #(
        .USE_MONITOR          (USE_MONITOR),
        .UNIT_ID              (8'(MON_UNIT_ID)),
        .AGENT_ID             (16'(MON_AGENT_ID)),
        .OUT_DEPTH            (4),
        .ACLK_MHZ             (ACLK_MHZ),
        .CXS_ISSUE            (cxs_pkg::CXS_ISSUE_D),
        .CXS_DATA_WIDTH       (DW),
        .CXS_MAX_PKT_PER_FLIT (CXS_N),
        .CXS_START_ALIGN      (CXS_ALIGN),
        .CXS_HAS_LAST         (1'b0),
        .CXS_HAS_PRCLTYPE     (1'b0),
        .CXS_SRCID_WIDTH      (AXIS_ID_WIDTH),
        .CXS_TGTID_WIDTH      (AXIS_DEST_WIDTH),
        .CXS_USER_WIDTH       (CXS_UW),
        .CXS_MAX_CREDIT       (CXS_MAX_CREDIT),
        .CXS_CREDIT_BEYOND_SPEC(CXS_CREDIT_BEYOND_SPEC),
        .CXS_STREAM_SRCID_BITS(CXS_STREAM_SRCID_BITS),
        .CXS_LINK_CTRL        (1'b1),
        .CXS_CHECK            (1'b0),
        .SKID_DEPTH           (SKID_DEPTH)
    ) u_endpoint (
        .aclk                  (clk),
        .aresetn               (rst_n),
        .cfg_link_enable       (1'b1),
        .cfg_link_hold         (1'b0),
        .cfg_idle_cycles       (CXS_IDLE_CYCLES),
        .fub_cxs_valid         (w_flit_valid),
        .fub_cxs_ready         (w_flit_ready),
        .fub_cxs_data          (w_flit_data),
        .fub_cxs_cntl          (w_flit_cntl),
        .fub_cxs_last          (1'b0),
        .fub_cxs_prcltype      (3'b000),
        .fub_cxs_srcid         (w_flit_srcid),
        .fub_cxs_tgtid         (w_flit_tgtid),
        .fub_cxs_user          (w_flit_user),
        .m_cxs_valid           (m_cxs_valid),
        .m_cxs_data            (m_cxs_data),
        .m_cxs_cntl            (m_cxs_cntl),
        .m_cxs_srcid           (m_cxs_srcid),
        .m_cxs_tgtid           (m_cxs_tgtid),
        .m_cxs_user            (m_cxs_user),
        .m_cxs_crdgnt          (m_cxs_crdgnt),
        .m_cxs_crdrtn          (m_cxs_crdrtn),
        .m_cxs_activereq       (m_cxs_activereq),
        .m_cxs_activeack       (m_cxs_activeack),
        .m_cxs_deacthint       (m_cxs_deacthint),
        .m_cxs_crdgntchk       (1'b1),
        .m_cxs_activeackchk    (1'b1),
        .busy                  (sts_mon_busy),
        .link_state            (sts_cxs_link_state),
        .protocol_error        (sts_cxs_protocol_error),
        .cam_clear             (1'b0),
        .cfg_monitor_enable    (cfg_mon_enable),
        .cfg_error_enable      (cfg_mon_err_enable),
        .cfg_timeout_enable    (cfg_mon_timeout_enable),
        .cfg_compl_enable      (cfg_mon_compl_enable),
        .cfg_credit_enable     (cfg_mon_perf_enable),
        .cfg_channel_enable    (cfg_mon_err_enable),
        .cfg_stream_enable     (cfg_mon_perf_enable),
        .cfg_timeout_cycles    (cfg_mon_timeout_cycles[15:0]),
        .cfg_freq_sel          (4'b0000),
        .cfg_cxs_pkt_mask      (cfg_mon_pkt_mask),
        .cfg_stall_threshold   (cfg_mon_latency_thresh),
        .i_mon_time            ('0),
        .monbus_valid          (monbus_valid),
        .monbus_ready          (monbus_ready),
        .monbus_packet         (monbus_packet),
        .monbus_timestamp      (monbus_timestamp),
        .packet_count          (sts_mon_packet_count),
        .error_count           (sts_mon_error_count),
        .dropped_count         (sts_mon_dropped_count),
        /* verilator lint_off PINCONNECTEMPTY */
        .m_cxs_last            (),
        .m_cxs_prcltype        (),
        .m_cxs_validchk        (),
        .m_cxs_datachk         (),
        .m_cxs_cntlchk         (),
        .m_cxs_lastchk         (),
        .m_cxs_prcltypechk     (),
        .m_cxs_srcidchk        (),
        .m_cxs_tgtidchk        (),
        .m_cxs_userchk         (),
        .m_cxs_crdrtnchk       (),
        .m_cxs_activereqchk    (),
        .credits               (),
        .in_packet             (),
        .credit_starved        (),
        .parity_error          (),
        .flit_count            ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : rapids_plane_cxs_tx
