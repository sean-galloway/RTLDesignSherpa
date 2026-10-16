// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_slave_pattern_check
// Purpose: The CXS counterpart of axis4_slave_pattern_check: receives CXS
//          flits on a credited CXS link (Arm IHI 0079, Issue D) and checks
//          them against the per-channel LFSR pattern
//
// Documentation: docs/markdown/rtl-amba/shared/cxs_injectors.md
// Subsystem: amba/shared
//
// Composition, nothing re-implemented:
//
//   s_cxs_* -> cxs_slave -> cxs_to_axis -> axis4_slave_pattern_check
//
// The checker, its CRC and every cfg_* / status port are
// axis4_slave_pattern_check's, unchanged. ready_en still gates the stream:
// held low, the receive FIFO fills and the link stops granting credits,
// which is what backpressure is on CXS. The link profile matches
// cxs_master_injector and the RAPIDS CXS planes.
//
// Parameters (beyond axis4_slave_pattern_check's):
//   - CXS_MAX_CREDIT: credits the receiver can have outstanding
//   - RX_FIFO_DEPTH: receive FIFO depth = the credit pool
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

module cxs_slave_pattern_check #(
    parameter int          NUM_CHANNELS     = 1,
    parameter int          AXIS_DATA_WIDTH  = 512,
    parameter int          AXIS_ID_WIDTH    = 8,
    parameter int          AXIS_DEST_WIDTH  = 4,
    parameter int          AXIS_USER_WIDTH  = 1,
    parameter int          LFSR_WIDTH       = 32,
    parameter logic [31:0] LFSR_SEED        = 32'hDEADBEEF,
    parameter logic [47:0] LFSR_TAPS        = {12'd23, 12'd3, 12'd2, 12'd1},
    parameter int          CRC_WIDTH        = 32,
    parameter int          CRC_DATA_WIDTH   = 32,
    parameter logic [31:0] CRC_POLY         = 32'h04C11DB7,
    parameter logic [31:0] CRC_INIT         = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT       = 32'hFFFFFFFF,
    parameter int          CRC_REFIN        = 1,
    parameter int          CRC_REFOUT       = 1,
    parameter int          BEAT_COUNT_WIDTH = 32,
    parameter bit          BYTE_CRC         = 1'b0,
    parameter int          CXS_MAX_CREDIT   = 32,
    // Per-stream framing key: channels interleave on the link and TID ->
    // CXSSRCID carries the channel, so the channel bits of CXSSRCID tell the
    // streams apart (IHI 0079D 2.5.2). Both ends must use the same value.
    parameter int          STREAM_SRCID_BITS = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 0,
    // Credit pool deeper than the spec's 63 (a whole-SRAM receiver); both ends
    parameter bit          CXS_CREDIT_BEYOND_SPEC = 1'b0,
    parameter int          RX_FIFO_DEPTH    = CXS_MAX_CREDIT,
    // Derived
    parameter int          DW               = AXIS_DATA_WIDTH,
    parameter int          STRB_WIDTH       = DW / 8,
    parameter int          CXS_N            = 2,
    parameter int          CXS_ALIGN        = 16,
    parameter bit          CARRY_TUSER      = (STRB_WIDTH + AXIS_USER_WIDTH) <= 128,
    parameter int          CXS_UW           = STRB_WIDTH + (CARRY_TUSER ? AXIS_USER_WIDTH : 0),
    parameter int          IW               = cxs_pkg::port_w(AXIS_ID_WIDTH),
    parameter int          DESTW            = cxs_pkg::port_w(AXIS_DEST_WIDTH),
    parameter int          CNTL_PW          = cxs_pkg::port_w(cxs_pkg::cntl_width(CXS_N, DW, CXS_ALIGN))
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Configuration / control (axis4_slave_pattern_check's, unchanged)
    input  logic                          cfg_start,
    input  logic [LFSR_WIDTH-1:0]         cfg_lfsr_seed,
    input  logic                          ready_en,
    output logic [NUM_CHANNELS-1:0][31:0] o_actual_crc,
    output logic [NUM_CHANNELS-1:0]       o_actual_crc_valid,
    output logic                          o_data_error,
    output logic [NUM_CHANNELS-1:0][31:0] o_beat_count,
    output logic [31:0]                   o_beat_count_total,
    output logic [BEAT_COUNT_WIDTH-1:0]   o_pkt_count,

    // CXS receive link
    input  logic                          s_cxs_valid,
    input  logic [DW-1:0]                 s_cxs_data,
    input  logic [CNTL_PW-1:0]            s_cxs_cntl,
    input  logic [IW-1:0]                 s_cxs_srcid,
    input  logic [DESTW-1:0]              s_cxs_tgtid,
    input  logic [CXS_UW-1:0]             s_cxs_user,
    output logic                          s_cxs_crdgnt,
    input  logic                          s_cxs_crdrtn,
    input  logic                          s_cxs_activereq,
    output logic                          s_cxs_activeack,
    output logic                          s_cxs_deacthint,

    // Link status
    output logic [1:0]                    link_state,       // {ACTIVEREQ synced, ACTIVEACK}
    output logic                          protocol_error,   // sticky
    output logic                          unsupported       // sticky: a flit AXIS framing cannot carry
);

    logic                       w_axis_tvalid, w_axis_tready, w_axis_tlast;
    logic [DW-1:0]              w_axis_tdata;
    logic [STRB_WIDTH-1:0]      w_axis_tstrb;
    logic [AXIS_ID_WIDTH-1:0]   w_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] w_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] w_axis_tuser;

    logic                w_flit_valid, w_flit_ready;
    logic [DW-1:0]       w_flit_data;
    logic [CNTL_PW-1:0]  w_flit_cntl;
    logic [IW-1:0]       w_flit_srcid;
    logic [DESTW-1:0]    w_flit_tgtid;
    logic [CXS_UW-1:0]   w_flit_user;

    cxs_slave #(
        .CXS_ISSUE             (cxs_pkg::CXS_ISSUE_D),
        .CXS_DATA_WIDTH        (DW),
        .CXS_MAX_PKT_PER_FLIT  (CXS_N),
        .CXS_START_ALIGN       (CXS_ALIGN),
        .CXS_HAS_LAST          (1'b0),
        .CXS_HAS_PRCLTYPE      (1'b0),
        .CXS_SRCID_WIDTH       (AXIS_ID_WIDTH),
        .CXS_TGTID_WIDTH       (AXIS_DEST_WIDTH),
        .CXS_USER_WIDTH        (CXS_UW),
        .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
        .CXS_CREDIT_BEYOND_SPEC (CXS_CREDIT_BEYOND_SPEC),
        .CXS_STREAM_SRCID_BITS  (STREAM_SRCID_BITS),
        .CXS_LINK_CTRL         (1'b1),
        .CXS_CHECK             (1'b0),
        .RX_FIFO_DEPTH         (RX_FIFO_DEPTH),
        .ACTIVEREQ_SYNC_STAGES (2)
    ) u_cxs (
        .aclk               (clk),
        .aresetn            (rst_n),
        .cfg_rx_enable      (1'b1),
        .cfg_deact_hint     (1'b0),
        .s_cxs_valid        (s_cxs_valid),
        .s_cxs_data         (s_cxs_data),
        .s_cxs_cntl         (s_cxs_cntl),
        .s_cxs_last         (1'b0),
        .s_cxs_prcltype     (3'b000),
        .s_cxs_srcid        (s_cxs_srcid),
        .s_cxs_tgtid        (s_cxs_tgtid),
        .s_cxs_user         (s_cxs_user),
        .s_cxs_crdgnt       (s_cxs_crdgnt),
        .s_cxs_crdrtn       (s_cxs_crdrtn),
        .s_cxs_activereq    (s_cxs_activereq),
        .s_cxs_activeack    (s_cxs_activeack),
        .s_cxs_deacthint    (s_cxs_deacthint),
        .s_cxs_validchk     (1'b1),
        .s_cxs_datachk      ('0),
        .s_cxs_cntlchk      ('0),
        .s_cxs_lastchk      (1'b1),
        .s_cxs_prcltypechk  (1'b1),
        .s_cxs_srcidchk     (1'b1),
        .s_cxs_tgtidchk     (1'b1),
        .s_cxs_userchk      ('0),
        .s_cxs_crdrtnchk    (1'b1),
        .s_cxs_activereqchk (1'b1),
        .fub_cxs_valid      (w_flit_valid),
        .fub_cxs_ready      (w_flit_ready),
        .fub_cxs_data       (w_flit_data),
        .fub_cxs_cntl       (w_flit_cntl),
        .fub_cxs_srcid      (w_flit_srcid),
        .fub_cxs_tgtid      (w_flit_tgtid),
        .fub_cxs_user       (w_flit_user),
        .link_state         (link_state),
        .protocol_error     (protocol_error),
        /* verilator lint_off PINCONNECTEMPTY */
        .s_cxs_crdgntchk    (),
        .s_cxs_activeackchk (),
        .fub_cxs_last       (),
        .fub_cxs_prcltype   (),
        .busy               (),
        .credits_outstanding(),
        .in_packet          (),
        .credit_starved     (),
        .parity_error       ()
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
        .m_axis_tdata  (w_axis_tdata),
        .m_axis_tstrb  (w_axis_tstrb),
        .m_axis_tlast  (w_axis_tlast),
        .m_axis_tid    (w_axis_tid),
        .m_axis_tdest  (w_axis_tdest),
        .m_axis_tuser  (w_axis_tuser),
        .m_axis_tvalid (w_axis_tvalid),
        .m_axis_tready (w_axis_tready),
        .unsupported   (unsupported)
    );

    axis4_slave_pattern_check #(
        .NUM_CHANNELS     (NUM_CHANNELS),
        .AXIS_DATA_WIDTH  (DW),
        .AXIS_ID_WIDTH    (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH  (AXIS_USER_WIDTH),
        .LFSR_WIDTH       (LFSR_WIDTH),
        .LFSR_SEED        (LFSR_SEED),
        .LFSR_TAPS        (LFSR_TAPS),
        .CRC_WIDTH        (CRC_WIDTH),
        .CRC_DATA_WIDTH   (CRC_DATA_WIDTH),
        .CRC_POLY         (CRC_POLY),
        .CRC_INIT         (CRC_INIT),
        .CRC_XOROUT       (CRC_XOROUT),
        .CRC_REFIN        (CRC_REFIN),
        .CRC_REFOUT       (CRC_REFOUT),
        .BEAT_COUNT_WIDTH (BEAT_COUNT_WIDTH),
        .BYTE_CRC         (BYTE_CRC)
    ) u_axis_chk (
        .clk                (clk),
        .rst_n              (rst_n),
        .cfg_start          (cfg_start),
        .cfg_lfsr_seed      (cfg_lfsr_seed),
        .ready_en           (ready_en),
        .o_actual_crc       (o_actual_crc),
        .o_actual_crc_valid (o_actual_crc_valid),
        .o_data_error       (o_data_error),
        .o_beat_count       (o_beat_count),
        .o_beat_count_total (o_beat_count_total),
        .o_pkt_count        (o_pkt_count),
        .s_axis_tvalid      (w_axis_tvalid),
        .s_axis_tready      (w_axis_tready),
        .s_axis_tdata       (w_axis_tdata),
        .s_axis_tstrb       (w_axis_tstrb),
        .s_axis_tlast       (w_axis_tlast),
        .s_axis_tid         (w_axis_tid),
        .s_axis_tdest       (w_axis_tdest),
        .s_axis_tuser       (w_axis_tuser)
    );

endmodule : cxs_slave_pattern_check
