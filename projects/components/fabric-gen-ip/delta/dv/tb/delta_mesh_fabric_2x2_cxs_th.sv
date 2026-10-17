// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: delta_mesh_fabric_2x2_cxs_th
// Purpose: Test harness for the CXS-interface delta mesh fabric. Wraps the
//          generated delta_mesh_fabric_2x2x1_cxs with one house CXS link
//          endpoint per boundary per direction, so the cocotb TB drives and
//          receives PLAIN AXI-Stream while every CXS mechanism (Issue D
//          framing, credit grant/return, activation handshake) is exercised
//          through the validated house rtl:
//
//            TB b_s_axis_* -> axis_to_cxs -> cxs_master --CXS link-->
//                fabric s_local_cxs_*[b]   (delta RX plane: cxs_slave +
//                cxs_to_axis -> cell core)
//            cell core -> delta TX plane (axis_to_cxs + cxs_master) --CXS
//                link--> cxs_slave + cxs_to_axis -> b_m_axis_* -> TB
//
//          Boundary index -> coordinate map (x-major; Z=1 so all 4 cells are
//          boundary): b0=(0,0,0) b1=(1,0,0) b2=(0,1,0) b3=(1,1,0).
//
//          Mesh credit sidebands (the inter-cell flow control) are kept
//          distinct from CXS link credit: s_local_credit is tied '1 here,
//          m_local_credit is exposed per boundary, matching the AXIS 2x2
//          harness's convention.
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

module delta_mesh_fabric_2x2_cxs_th #(
    parameter int DATA_WIDTH   = 256,   // CXS multi-packet flits require 256+
    parameter int USER_WIDTH   = 64,
    parameter int NUM_VC       = 2,
    parameter int NUM_BOUNDARY = 4,
    parameter int CXS_MAX_CREDIT = 32,
    // cxs_pkg-derived widths (mirror delta_mesh_plane_cxs_* at DATA_WIDTH=256;
    // literals because this hand-written SV has no param-parser constraint).
    parameter int SW       = DATA_WIDTH / 8,
    parameter int CNTL_W   = 14,                // cntl_width(2, 256, 16)
    parameter int CNTL_PW  = 14,
    parameter int CXS_UW   = SW + USER_WIDTH
) (
    input  logic aclk,
    input  logic aresetn,

    // TB-facing plain AXIS per boundary (arrays; the cocotb TB indexes them)
    input  logic [DATA_WIDTH-1:0] b_s_axis_tdata  [NUM_BOUNDARY],
    input  logic                  b_s_axis_tvalid [NUM_BOUNDARY],
    output logic                  b_s_axis_tready [NUM_BOUNDARY],
    input  logic                  b_s_axis_tlast  [NUM_BOUNDARY],
    input  logic [USER_WIDTH-1:0] b_s_axis_tuser  [NUM_BOUNDARY],

    output logic [DATA_WIDTH-1:0] b_m_axis_tdata  [NUM_BOUNDARY],
    output logic                  b_m_axis_tvalid [NUM_BOUNDARY],
    input  logic                  b_m_axis_tready [NUM_BOUNDARY],
    output logic                  b_m_axis_tlast  [NUM_BOUNDARY],
    output logic [USER_WIDTH-1:0] b_m_axis_tuser  [NUM_BOUNDARY],

    // Mesh (inter-cell) credit sidebands, per boundary
    output logic [NUM_VC-1:0]     b_m_credit [NUM_BOUNDARY],

    // Debug taps: peer link FSM/credit state per boundary (test observability)
    output logic [1:0]            b_dbg_tx_state [NUM_BOUNDARY],
    output logic [5:0]            b_dbg_tx_credits [NUM_BOUNDARY],
    output logic                  b_dbg_tx_starved [NUM_BOUNDARY],
    output logic [1:0]            b_dbg_rx_state [NUM_BOUNDARY]
);

    // ------------------------------------------------------------------
    // Fabric-facing CXS link wires per boundary
    // ------------------------------------------------------------------
    logic                  w_m_valid [NUM_BOUNDARY];
    logic [DATA_WIDTH-1:0] w_m_data  [NUM_BOUNDARY];
    logic [CNTL_PW-1:0]    w_m_cntl  [NUM_BOUNDARY];
    logic [0:0]            w_m_srcid [NUM_BOUNDARY];
    logic [0:0]            w_m_tgtid [NUM_BOUNDARY];
    logic [CXS_UW-1:0]     w_m_user  [NUM_BOUNDARY];
    logic                  w_m_crdgnt [NUM_BOUNDARY];
    logic                  w_m_crdrtn [NUM_BOUNDARY];
    logic                  w_m_actreq [NUM_BOUNDARY];
    logic                  w_m_actack [NUM_BOUNDARY];
    logic                  w_m_dehint [NUM_BOUNDARY];

    logic                  w_s_valid [NUM_BOUNDARY];
    logic [DATA_WIDTH-1:0] w_s_data  [NUM_BOUNDARY];
    logic [CNTL_PW-1:0]    w_s_cntl  [NUM_BOUNDARY];
    logic [0:0]            w_s_srcid [NUM_BOUNDARY];
    logic [0:0]            w_s_tgtid [NUM_BOUNDARY];
    logic [CXS_UW-1:0]     w_s_user  [NUM_BOUNDARY];
    logic                  w_s_crdgnt [NUM_BOUNDARY];
    logic                  w_s_crdrtn [NUM_BOUNDARY];
    logic                  w_s_actreq [NUM_BOUNDARY];
    logic                  w_s_actack [NUM_BOUNDARY];
    logic                  w_s_dehint [NUM_BOUNDARY];

    logic [NUM_VC-1:0]     w_s_credit [NUM_BOUNDARY];

    logic [31:0]           b_dbg_err [NUM_BOUNDARY];

    for (genvar b = 0; b < NUM_BOUNDARY; b++) begin : g_peer
        // --------------------------------------------------------------
        // Peer TX (TB -> fabric s_local): axis_to_cxs + cxs_master
        // --------------------------------------------------------------
        logic                peer_tx_flit_valid;
        logic                peer_tx_flit_ready;
        logic [DATA_WIDTH-1:0] peer_tx_flit_data;
        logic [CNTL_PW-1:0]  peer_tx_flit_cntl;
        logic [0:0]          peer_tx_flit_srcid;
        logic [0:0]          peer_tx_flit_tgtid;
        logic [CXS_UW-1:0]   peer_tx_flit_user;

        axis_to_cxs #(
            .DATA_WIDTH          (DATA_WIDTH),
            .ID_WIDTH            (0),
            .DEST_WIDTH          (0),
            .USER_WIDTH          (USER_WIDTH),
            .CXS_MAX_PKT_PER_FLIT(2),
            .CXS_START_ALIGN     (16),
            .CARRY_TUSER         (1'b1),
            .STREAM_ID_BITS      (0),
            .STREAM_DEST_BITS    (0)
        ) u_peer_tx_framer (
            .aclk          (aclk),
            .aresetn       (aresetn),
            .s_axis_tdata  (b_s_axis_tdata[b]),
            .s_axis_tstrb  ({SW{1'b1}}),
            .s_axis_tlast  (b_s_axis_tlast[b]),
            .s_axis_tid    ('0),
            .s_axis_tdest  ('0),
            .s_axis_tuser  (b_s_axis_tuser[b]),
            .s_axis_tvalid (b_s_axis_tvalid[b]),
            .s_axis_tready (b_s_axis_tready[b]),
            .cxs_valid     (peer_tx_flit_valid),
            .cxs_ready     (peer_tx_flit_ready),
            .cxs_data      (peer_tx_flit_data),
            .cxs_cntl      (peer_tx_flit_cntl),
            .cxs_srcid     (peer_tx_flit_srcid),
            .cxs_tgtid     (peer_tx_flit_tgtid),
            .cxs_user      (peer_tx_flit_user)
        );

        cxs_master #(
            .CXS_ISSUE             (cxs_pkg::CXS_ISSUE_D),
            .CXS_DATA_WIDTH        (DATA_WIDTH),
            .CXS_MAX_PKT_PER_FLIT  (2),
            .CXS_START_ALIGN       (16),
            .CXS_HAS_LAST          (1'b0),
            .CXS_HAS_PRCLTYPE      (1'b0),
            .CXS_SRCID_WIDTH       (0),
            .CXS_TGTID_WIDTH       (0),
            .CXS_USER_WIDTH        (CXS_UW),
            .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
            .CXS_CREDIT_BEYOND_SPEC(CXS_MAX_CREDIT > 63),
            .CXS_LINK_CTRL         (1'b1),
            .CXS_CHECK             (1'b0),
            .SKID_DEPTH            (4)
        ) u_peer_tx_link (
            .aclk                  (aclk),
            .aresetn               (aresetn),
            .cfg_link_enable       (1'b1),
            .cfg_link_hold         (1'b0),
            .cfg_idle_cycles       (8'd0),      // never deactivate: simplest TB
            .fub_cxs_valid         (peer_tx_flit_valid),
            .fub_cxs_ready         (peer_tx_flit_ready),
            .fub_cxs_data          (peer_tx_flit_data),
            .fub_cxs_cntl          (peer_tx_flit_cntl),
            .fub_cxs_last          (1'b0),
            .fub_cxs_prcltype      (3'b000),
            .fub_cxs_srcid         (peer_tx_flit_srcid),
            .fub_cxs_tgtid         (peer_tx_flit_tgtid),
            .fub_cxs_user          (peer_tx_flit_user),
            .m_cxs_valid           (w_s_valid[b]),
            .m_cxs_data            (w_s_data[b]),
            .m_cxs_cntl            (w_s_cntl[b]),
            .m_cxs_last            (),
            .m_cxs_prcltype        (),
            .m_cxs_srcid           (w_s_srcid[b]),
            .m_cxs_tgtid           (w_s_tgtid[b]),
            .m_cxs_user            (w_s_user[b]),
            .m_cxs_crdgnt          (w_s_crdgnt[b]),
            .m_cxs_crdrtn          (w_s_crdrtn[b]),
            .m_cxs_activereq       (w_s_actreq[b]),
            .m_cxs_activeack       (w_s_actack[b]),
            .m_cxs_deacthint       (w_s_dehint[b]),
            .m_cxs_validchk        (),
            .m_cxs_datachk         (),
            .m_cxs_cntlchk         (),
            .m_cxs_lastchk         (),
            .m_cxs_prcltypechk     (),
            .m_cxs_srcidchk        (),
            .m_cxs_tgtidchk        (),
            .m_cxs_userchk         (),
            .m_cxs_crdgntchk       (1'b0),
            .m_cxs_crdrtnchk       (),
            .m_cxs_activereqchk    (),
            .m_cxs_activeackchk    (1'b0),
            .busy                  (),
            .credits               (b_dbg_tx_credits[b]),
            .credit_starved        (b_dbg_tx_starved[b]),
            .in_packet             (),
            .link_state            (b_dbg_tx_state[b]),
            .parity_error          (),
            .protocol_error        ()
        );

        // --------------------------------------------------------------
        // Peer RX (fabric m_local -> TB): cxs_slave + cxs_to_axis
        // --------------------------------------------------------------
        logic                peer_rx_flit_valid;
        logic                peer_rx_flit_ready;
        logic [DATA_WIDTH-1:0] peer_rx_flit_data;
        logic [CNTL_PW-1:0]  peer_rx_flit_cntl;
        logic [0:0]          peer_rx_flit_srcid;
        logic [0:0]          peer_rx_flit_tgtid;
        logic [CXS_UW-1:0]   peer_rx_flit_user;

        cxs_slave #(
            .CXS_ISSUE             (cxs_pkg::CXS_ISSUE_D),
            .CXS_DATA_WIDTH        (DATA_WIDTH),
            .CXS_MAX_PKT_PER_FLIT  (2),
            .CXS_START_ALIGN       (16),
            .CXS_HAS_LAST          (1'b0),
            .CXS_HAS_PRCLTYPE      (1'b0),
            .CXS_SRCID_WIDTH       (0),
            .CXS_TGTID_WIDTH       (0),
            .CXS_USER_WIDTH        (CXS_UW),
            .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
            .CXS_CREDIT_BEYOND_SPEC(CXS_MAX_CREDIT > 63),
            .CXS_LINK_CTRL         (1'b1),
            .CXS_CHECK             (1'b0),
            .RX_FIFO_DEPTH         (CXS_MAX_CREDIT)
        ) u_peer_rx_link (
            .aclk                  (aclk),
            .aresetn               (aresetn),
            .cfg_rx_enable         (1'b1),
            .cfg_deact_hint        (1'b0),
            .s_cxs_valid           (w_m_valid[b]),
            .s_cxs_data            (w_m_data[b]),
            .s_cxs_cntl            (w_m_cntl[b]),
            .s_cxs_last            (1'b0),
            .s_cxs_prcltype        (3'b000),
            .s_cxs_srcid           (w_m_srcid[b]),
            .s_cxs_tgtid           (w_m_tgtid[b]),
            .s_cxs_user            (w_m_user[b]),
            .s_cxs_crdgnt          (w_m_crdgnt[b]),
            .s_cxs_crdrtn          (w_m_crdrtn[b]),
            .s_cxs_activereq       (w_m_actreq[b]),
            .s_cxs_activeack       (w_m_actack[b]),
            .s_cxs_deacthint       (w_m_dehint[b]),
            .fub_cxs_valid         (peer_rx_flit_valid),
            .fub_cxs_ready         (peer_rx_flit_ready),
            .fub_cxs_data          (peer_rx_flit_data),
            .fub_cxs_cntl          (peer_rx_flit_cntl),
            .fub_cxs_last          (),
            .fub_cxs_prcltype      (),
            .fub_cxs_srcid         (peer_rx_flit_srcid),
            .fub_cxs_tgtid         (peer_rx_flit_tgtid),
            .fub_cxs_user          (peer_rx_flit_user),
            .s_cxs_validchk        (1'b0),
            .s_cxs_datachk         ('0),
            .s_cxs_cntlchk         ('0),
            .s_cxs_lastchk         (1'b0),
            .s_cxs_prcltypechk     (1'b0),
            .s_cxs_srcidchk        (1'b0),
            .s_cxs_tgtidchk        (1'b0),
            .s_cxs_userchk         ('0),
            .s_cxs_crdgntchk       (),
            .s_cxs_crdrtnchk       (1'b0),
            .s_cxs_activereqchk    (1'b0),
            .s_cxs_activeackchk    (),
            .busy                  (),
            .credits_outstanding   (),
            .credit_starved        (),
            .in_packet             (),
            .link_state            (b_dbg_rx_state[b]),
            .parity_error          (),
            .protocol_error        ()
        );

        cxs_to_axis #(
            .DATA_WIDTH          (DATA_WIDTH),
            .ID_WIDTH            (0),
            .DEST_WIDTH          (0),
            .USER_WIDTH          (USER_WIDTH),
            .CXS_MAX_PKT_PER_FLIT(2),
            .CXS_START_ALIGN     (16),
            .CARRY_TUSER         (1'b1)
        ) u_peer_rx_deframer (
            .aclk          (aclk),
            .aresetn       (aresetn),
            .cxs_valid     (peer_rx_flit_valid),
            .cxs_ready     (peer_rx_flit_ready),
            .cxs_data      (peer_rx_flit_data),
            .cxs_cntl      (peer_rx_flit_cntl),
            .cxs_srcid     (peer_rx_flit_srcid),
            .cxs_tgtid     (peer_rx_flit_tgtid),
            .cxs_user      (peer_rx_flit_user),
            .m_axis_tdata  (b_m_axis_tdata[b]),
            .m_axis_tstrb  (),
            .m_axis_tlast  (b_m_axis_tlast[b]),
            .m_axis_tid    (),
            .m_axis_tdest  (),
            .m_axis_tuser  (b_m_axis_tuser[b]),
            .m_axis_tvalid (b_m_axis_tvalid[b]),
            .m_axis_tready (b_m_axis_tready[b]),
            .unsupported   ()
        );

        assign w_s_credit[b] = {NUM_VC{1'b1}};
        // b_m_credit is driven by the fabric (m_local_credit); no tie here.
    end

    // ------------------------------------------------------------------
    // DUT: the generated CXS fabric (2x2x1)
    // ------------------------------------------------------------------
    delta_mesh_fabric_2x2x1_cxs #(
        .DATA_WIDTH   (DATA_WIDTH),
        .USER_WIDTH   (USER_WIDTH)
    ) u_fabric (
        .aclk (aclk),
        .aresetn (aresetn),
        .s_local_cxs_valid     (w_s_valid),
        .s_local_cxs_data      (w_s_data),
        .s_local_cxs_cntl      (w_s_cntl),
        .s_local_cxs_srcid     (w_s_srcid),
        .s_local_cxs_tgtid     (w_s_tgtid),
        .s_local_cxs_user      (w_s_user),
        .s_local_cxs_crdgnt    (w_s_crdgnt),
        .s_local_cxs_crdrtn    (w_s_crdrtn),
        .s_local_cxs_activereq (w_s_actreq),
        .s_local_cxs_activeack (w_s_actack),
        .s_local_cxs_deacthint (w_s_dehint),
        .m_local_cxs_valid     (w_m_valid),
        .m_local_cxs_data      (w_m_data),
        .m_local_cxs_cntl      (w_m_cntl),
        .m_local_cxs_srcid     (w_m_srcid),
        .m_local_cxs_tgtid     (w_m_tgtid),
        .m_local_cxs_user      (w_m_user),
        .m_local_cxs_crdgnt    (w_m_crdgnt),
        .m_local_cxs_crdrtn    (w_m_crdrtn),
        .m_local_cxs_activereq (w_m_actreq),
        .m_local_cxs_activeack (w_m_actack),
        .m_local_cxs_deacthint (w_m_dehint),
        .s_local_credit (w_s_credit),
        .m_local_credit (b_m_credit),
        .o_err          (b_dbg_err),
        .o_mode_acks    (),
        .o_bulk_starved (),
        .o_dft_active   ()
    );

endmodule
