// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_master_injector
// Purpose: The CXS counterpart of axis4_master_injector: the same per-channel
//          LFSR pattern and expected CRC, sent as CXS flits on a credited
//          CXS link (Arm IHI 0079, Issue D)
//
// Documentation: docs/markdown/rtl-amba/shared/cxs_injectors.md
// Subsystem: amba/shared
//
// Composition, nothing re-implemented:
//
//   axis4_master_injector -> axis_to_cxs -> cxs_master -> m_cxs_*
//
// The pattern, the per-channel CRC, the packet cadence and every cfg_* /
// status port are axis4_master_injector's, unchanged, so the expected CRC
// stays bit-identical to axis4_slave_pattern_check, cxs_slave_pattern_check,
// axi4_slave_rd_injector and axi4_slave_wr_crc_check. The link is the RAPIDS
// CXS plane profile (projects/components/dma-ip/rapids/docs/rapids_planes.md):
// Issue D, CXSMAXPKTPERFLIT = 2, 16-byte start alignment, TID -> CXSSRCID,
// TDEST -> CXSTGTID, CXSUSER = {TUSER, TSTRB} (TUSER dropped when
// DW/8 + TUSER width > 128), link activation on, no parity.
//
// Parameters (beyond axis4_master_injector's):
//   - CXS_MAX_CREDIT: credits the transmitter can hold (Issue D: 1..63)
//   - CXS_IDLE_CYCLES: idle RUN cycles before the link deactivates
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

module cxs_master_injector #(
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
    parameter int          CXS_MAX_CREDIT   = 32,
    // Per-stream framing key: channels interleave on the link and TID ->
    // CXSSRCID carries the channel, so the channel bits of CXSSRCID tell the
    // streams apart (IHI 0079D 2.5.2). Both ends must use the same value.
    parameter int          STREAM_SRCID_BITS = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 0,
    // Credit pool deeper than the spec's 63 (a whole-SRAM receiver); both ends
    parameter bit          CXS_CREDIT_BEYOND_SPEC = 1'b0,
    parameter logic [7:0]  CXS_IDLE_CYCLES  = 8'd32,
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

    // Configuration / control (axis4_master_injector's, unchanged)
    input  logic                          cfg_start,
    input  logic [LFSR_WIDTH-1:0]         cfg_lfsr_seed,
    input  logic [NUM_CHANNELS-1:0]       cfg_channel_mask,
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_num_beats,
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_beats_per_pkt,
    input  logic                          cfg_interleave,
    input  logic [AXIS_DEST_WIDTH-1:0]    cfg_tdest,
    input  logic [7:0]                    cfg_last_bytes,
    output logic                          cfg_busy,
    output logic                          cfg_done,
    output logic [NUM_CHANNELS-1:0][31:0] o_expected_crc,
    output logic [NUM_CHANNELS-1:0]       o_expected_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] o_beat_count,
    output logic [31:0]                   o_beat_count_total,

    // CXS transmit link
    output logic                          m_cxs_valid,
    output logic [DW-1:0]                 m_cxs_data,
    output logic [CNTL_PW-1:0]            m_cxs_cntl,
    output logic [IW-1:0]                 m_cxs_srcid,
    output logic [DESTW-1:0]              m_cxs_tgtid,
    output logic [CXS_UW-1:0]             m_cxs_user,
    input  logic                          m_cxs_crdgnt,
    output logic                          m_cxs_crdrtn,
    output logic                          m_cxs_activereq,
    input  logic                          m_cxs_activeack,
    input  logic                          m_cxs_deacthint,

    // Link status
    output logic [1:0]                    link_state,       // {ACTIVEREQ, ACTIVEACK}
    output logic                          protocol_error    // sticky
);

    // AXIS between the pattern source and the adapter
    logic                       w_axis_tvalid, w_axis_tready, w_axis_tlast;
    logic [DW-1:0]              w_axis_tdata;
    logic [STRB_WIDTH-1:0]      w_axis_tstrb;
    logic [AXIS_ID_WIDTH-1:0]   w_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] w_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] w_axis_tuser;

    // Flits between the adapter and the endpoint
    logic                w_flit_valid, w_flit_ready;
    logic [DW-1:0]       w_flit_data;
    logic [CNTL_PW-1:0]  w_flit_cntl;
    logic [IW-1:0]       w_flit_srcid;
    logic [DESTW-1:0]    w_flit_tgtid;
    logic [CXS_UW-1:0]   w_flit_user;

    axis4_master_injector #(
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
        .BEAT_COUNT_WIDTH (BEAT_COUNT_WIDTH)
    ) u_axis_gen (
        .clk                  (clk),
        .rst_n                (rst_n),
        .cfg_start            (cfg_start),
        .cfg_lfsr_seed        (cfg_lfsr_seed),
        .cfg_channel_mask     (cfg_channel_mask),
        .cfg_num_beats        (cfg_num_beats),
        .cfg_beats_per_pkt    (cfg_beats_per_pkt),
        .cfg_interleave       (cfg_interleave),
        .cfg_tdest            (cfg_tdest),
        .cfg_last_bytes       (cfg_last_bytes),
        .cfg_busy             (cfg_busy),
        .cfg_done             (cfg_done),
        .o_expected_crc       (o_expected_crc),
        .o_expected_crc_valid (o_expected_crc_valid),
        .o_beat_count         (o_beat_count),
        .o_beat_count_total   (o_beat_count_total),
        .m_axis_tvalid        (w_axis_tvalid),
        .m_axis_tready        (w_axis_tready),
        .m_axis_tdata         (w_axis_tdata),
        .m_axis_tstrb         (w_axis_tstrb),
        .m_axis_tlast         (w_axis_tlast),
        .m_axis_tid           (w_axis_tid),
        .m_axis_tdest         (w_axis_tdest),
        .m_axis_tuser         (w_axis_tuser)
    );

    axis_to_cxs #(
        .DATA_WIDTH           (DW),
        .ID_WIDTH             (AXIS_ID_WIDTH),
        .DEST_WIDTH           (AXIS_DEST_WIDTH),
        .USER_WIDTH           (AXIS_USER_WIDTH),
        .CXS_MAX_PKT_PER_FLIT (CXS_N),
        .CXS_START_ALIGN      (CXS_ALIGN),
        .CARRY_TUSER          (CARRY_TUSER),
        .STREAM_ID_BITS       (STREAM_SRCID_BITS),
        .STREAM_DEST_BITS     (0)
    ) u_axis_to_cxs (
        .aclk          (clk),
        .aresetn       (rst_n),
        .s_axis_tdata  (w_axis_tdata),
        .s_axis_tstrb  (w_axis_tstrb),
        .s_axis_tlast  (w_axis_tlast),
        .s_axis_tid    (w_axis_tid),
        .s_axis_tdest  (w_axis_tdest),
        .s_axis_tuser  (w_axis_tuser),
        .s_axis_tvalid (w_axis_tvalid),
        .s_axis_tready (w_axis_tready),
        .cxs_valid     (w_flit_valid),
        .cxs_ready     (w_flit_ready),
        .cxs_data      (w_flit_data),
        .cxs_cntl      (w_flit_cntl),
        .cxs_srcid     (w_flit_srcid),
        .cxs_tgtid     (w_flit_tgtid),
        .cxs_user      (w_flit_user)
    );

    cxs_master #(
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
        .CXS_CREDIT_BEYOND_SPEC (CXS_CREDIT_BEYOND_SPEC),
        .CXS_STREAM_SRCID_BITS  (STREAM_SRCID_BITS),
        .CXS_LINK_CTRL        (1'b1),
        .CXS_CHECK            (1'b0)
    ) u_cxs (
        .aclk               (clk),
        .aresetn            (rst_n),
        .cfg_link_enable    (1'b1),
        .cfg_link_hold      (1'b0),
        .cfg_idle_cycles    (CXS_IDLE_CYCLES),
        .fub_cxs_valid      (w_flit_valid),
        .fub_cxs_ready      (w_flit_ready),
        .fub_cxs_data       (w_flit_data),
        .fub_cxs_cntl       (w_flit_cntl),
        .fub_cxs_last       (1'b0),
        .fub_cxs_prcltype   (3'b000),
        .fub_cxs_srcid      (w_flit_srcid),
        .fub_cxs_tgtid      (w_flit_tgtid),
        .fub_cxs_user       (w_flit_user),
        .m_cxs_valid        (m_cxs_valid),
        .m_cxs_data         (m_cxs_data),
        .m_cxs_cntl         (m_cxs_cntl),
        .m_cxs_srcid        (m_cxs_srcid),
        .m_cxs_tgtid        (m_cxs_tgtid),
        .m_cxs_user         (m_cxs_user),
        .m_cxs_crdgnt       (m_cxs_crdgnt),
        .m_cxs_crdrtn       (m_cxs_crdrtn),
        .m_cxs_activereq    (m_cxs_activereq),
        .m_cxs_activeack    (m_cxs_activeack),
        .m_cxs_deacthint    (m_cxs_deacthint),
        .m_cxs_crdgntchk    (1'b1),
        .m_cxs_activeackchk (1'b1),
        .link_state         (link_state),
        .protocol_error     (protocol_error),
        /* verilator lint_off PINCONNECTEMPTY */
        .m_cxs_last         (),
        .m_cxs_prcltype     (),
        .m_cxs_validchk     (),
        .m_cxs_datachk      (),
        .m_cxs_cntlchk      (),
        .m_cxs_lastchk      (),
        .m_cxs_prcltypechk  (),
        .m_cxs_srcidchk     (),
        .m_cxs_tgtidchk     (),
        .m_cxs_userchk      (),
        .m_cxs_crdrtnchk    (),
        .m_cxs_activereqchk (),
        .busy               (),
        .credits            (),
        .in_packet          (),
        .credit_starved     (),
        .parity_error       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : cxs_master_injector
