// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_plane_cxs_rx
// Purpose: CXS network plane, sink ingress (RX): cxs_slave_monlite + cxs_to_axis
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

module rapids_plane_cxs_rx #(
    parameter bit USE_MONITOR      = 1'b1,
    parameter int MON_UNIT_ID      = 1,
    parameter int MON_AGENT_ID     = 10,
    parameter int ACLK_MHZ         = 100,     // the monitor's microsecond tick
    parameter int DATA_WIDTH       = 512,
    parameter int AXIS_ID_WIDTH    = 8,
    parameter int AXIS_DEST_WIDTH  = 4,
    parameter int AXIS_USER_WIDTH  = 1,
    // SKID_DEPTH is unused here (the receive FIFO is the buffer); it stays so
    // every plane takes the same parameters and a top can swap the module name.
    /* verilator lint_off UNUSEDPARAM */
    parameter int SKID_DEPTH       = 4,
    /* verilator lint_on UNUSEDPARAM */
    parameter int CXS_MAX_CREDIT   = 15,      // credits the link carries (1..63, or more with CXS_CREDIT_BEYOND_SPEC)
    parameter bit CXS_CREDIT_BEYOND_SPEC = (CXS_MAX_CREDIT > 63),
    // Channels interleave on the link (CXSSRCID = TID = channel), so packets
    // are framed per stream on the low CXSSRCID bits (IHI 0079D 2.5.2)
    parameter int CXS_STREAM_SRCID_BITS = 3,
    parameter int RX_FIFO_DEPTH    = CXS_MAX_CREDIT,   // receive FIFO = the credit pool
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
    output monitor_common_pkg::monitor_packet_t   monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t monbus_timestamp,

    // ---- Outer: the CXS link (Arm IHI 0079, Issue D) ----
    input  logic                                      s_cxs_valid,
    input  logic [DW-1:0]                             s_cxs_data,
    input  logic [CNTL_PW-1:0]                        s_cxs_cntl,
    input  logic [IW-1:0]                             s_cxs_srcid,
    input  logic [DESTW-1:0]                          s_cxs_tgtid,
    input  logic [CXS_UW-1:0]                         s_cxs_user,
    output logic                                      s_cxs_crdgnt,
    input  logic                                      s_cxs_crdrtn,
    input  logic                                      s_cxs_activereq,
    output logic                                      s_cxs_activeack,
    output logic                                      s_cxs_deacthint,

    // ---- Plane-specific status ----
    output logic [1:0]                            sts_cxs_link_state,      // {ACTIVEREQ, ACTIVEACK}
    output logic                                  sts_cxs_protocol_error,
    output logic                                  sts_cxs_unsupported      // a received flit AXIS cannot carry
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

    cxs_slave_monlite #(
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
        .RX_FIFO_DEPTH        (RX_FIFO_DEPTH),
        .ACTIVEREQ_SYNC_STAGES(2)
    ) u_endpoint (
        .aclk                  (clk),
        .aresetn               (rst_n),
        .cfg_rx_enable         (1'b1),
        .cfg_deact_hint        (1'b0),
        .s_cxs_valid           (s_cxs_valid),
        .s_cxs_data            (s_cxs_data),
        .s_cxs_cntl            (s_cxs_cntl),
        .s_cxs_last            (1'b0),
        .s_cxs_prcltype        (3'b000),
        .s_cxs_srcid           (s_cxs_srcid),
        .s_cxs_tgtid           (s_cxs_tgtid),
        .s_cxs_user            (s_cxs_user),
        .s_cxs_crdgnt          (s_cxs_crdgnt),
        .s_cxs_crdrtn          (s_cxs_crdrtn),
        .s_cxs_activereq       (s_cxs_activereq),
        .s_cxs_activeack       (s_cxs_activeack),
        .s_cxs_deacthint       (s_cxs_deacthint),
        .s_cxs_validchk        (1'b1),
        .s_cxs_datachk         ('0),
        .s_cxs_cntlchk         ('0),
        .s_cxs_lastchk         (1'b1),
        .s_cxs_prcltypechk     (1'b1),
        .s_cxs_srcidchk        (1'b1),
        .s_cxs_tgtidchk        (1'b1),
        .s_cxs_userchk         ('0),
        .s_cxs_crdrtnchk       (1'b1),
        .s_cxs_activereqchk    (1'b1),
        .fub_cxs_valid         (w_flit_valid),
        .fub_cxs_ready         (w_flit_ready),
        .fub_cxs_data          (w_flit_data),
        .fub_cxs_cntl          (w_flit_cntl),
        .fub_cxs_srcid         (w_flit_srcid),
        .fub_cxs_tgtid         (w_flit_tgtid),
        .fub_cxs_user          (w_flit_user),
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
        .s_cxs_crdgntchk       (),
        .s_cxs_activeackchk    (),
        .fub_cxs_last          (),
        .fub_cxs_prcltype      (),
        .credits_outstanding   (),
        .in_packet             (),
        .credit_starved        (),
        .parity_error          (),
        .flit_count            ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    cxs_to_axis #(
        .DATA_WIDTH           (DW),
        .ID_WIDTH             (AXIS_ID_WIDTH),
        .DEST_WIDTH           (AXIS_DEST_WIDTH),
        .USER_WIDTH           (AXIS_USER_WIDTH),
        .CXS_MAX_PKT_PER_FLIT (CXS_N),
        .CXS_START_ALIGN      (CXS_ALIGN),
        .CARRY_TUSER          (CARRY_TUSER)
    ) u_cxs_to_axis (
        .aclk          (clk),
        .aresetn       (rst_n),
        .cxs_valid     (w_flit_valid),
        .cxs_ready     (w_flit_ready),
        .cxs_data      (w_flit_data),
        .cxs_cntl      (w_flit_cntl),
        .cxs_srcid     (w_flit_srcid),
        .cxs_tgtid     (w_flit_tgtid),
        .cxs_user      (w_flit_user),
        .m_axis_tdata  (fub_axis_tdata),
        .m_axis_tstrb  (fub_axis_tstrb),
        .m_axis_tlast  (fub_axis_tlast),
        .m_axis_tid    (fub_axis_tid),
        .m_axis_tdest  (fub_axis_tdest),
        .m_axis_tuser  (fub_axis_tuser),
        .m_axis_tvalid (fub_axis_tvalid),
        .m_axis_tready (fub_axis_tready),
        .unsupported   (sts_cxs_unsupported)
    );

endmodule : rapids_plane_cxs_rx
