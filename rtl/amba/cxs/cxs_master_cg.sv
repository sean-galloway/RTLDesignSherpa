// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_master_cg
// Purpose: cxs_master behind one amba_clock_gate_ctrl
//
// Documentation: docs/markdown/rtl-amba/cxs/cxs_master_cg.md
// Subsystem: amba
//
// When it is safe to stop the clock. A credited link moves state with no
// handshake the gated side could stall: a CXSCRDGNT that arrives while the
// clock is stopped is a credit lost for good. So the core's `busy` includes
// every state in which the receiver may still grant -- ACTIVEREQ or the
// sampled ACTIVEACK high, or any credit held -- and the block can only gate
// in STOP with zero credits, where the receiver "must not send credit"
// (IHI 0079D 5.2).
//
//   - CXS_LINK_CTRL = 1: gates in STOP. The FUB's fub_cxs_valid wakes it;
//     the woken core then raises CXSACTIVEREQ.
//   - CXS_LINK_CTRL = 0: there is no STOP. The receiver grants whenever it
//     has room, so the core holds credits indefinitely and `busy` never
//     falls: this wrapper never gates. That is the protocol's property, not
//     a defect here -- use CXS_LINK_CTRL = 1 to save clock power.
//
// Activity terms (vault/handbook/design/clock-gating-activity-terms):
//   user_valid = fub_cxs_valid | core busy        (FUB VALID + pending work)
//   axi_valid  = m_cxs_crdgnt | m_cxs_activeack   (the peer's VALID-like
//                inputs, both synchronous to aclk per IHI 0079D 5.5)
// No READY of any peer is in either term; CXS has none. Every event output
// (CXSVALID, CXSCRDRTN and their check bits) is masked with !cg_gating for
// the wake-latency overlap, and fub_cxs_ready is forced low while gated.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

module cxs_master_cg
    import cxs_pkg::*;
#(
    parameter int CXS_ISSUE            = CXS_ISSUE_D,
    parameter int CXS_DATA_WIDTH       = 256,
    parameter int CXS_MAX_PKT_PER_FLIT = 2,
    parameter int CXS_START_ALIGN      = 16,
    parameter bit CXS_HAS_LAST         = 1'b0,
    parameter bit CXS_HAS_PRCLTYPE     = 1'b0,
    parameter int CXS_SRCID_WIDTH      = 0,
    parameter int CXS_TGTID_WIDTH      = 0,
    parameter int CXS_USER_WIDTH       = 0,
    parameter int CXS_MAX_CREDIT       = 15,
    parameter bit  CXS_CREDIT_BEYOND_SPEC = 1'b0,   // see cxs_master / cxs_slave
    parameter int  CXS_STREAM_PRCL_BITS   = 0,      // per-stream tracking key (cxs_stream_key)
    parameter int  CXS_STREAM_SRCID_BITS  = 0,
    parameter int  CXS_STREAM_TGTID_BITS  = 0,
    parameter bit CXS_LINK_CTRL        = 1'b1,
    parameter bit CXS_CHECK            = 1'b0,
    parameter int SKID_DEPTH           = 4,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH  = 4,

    // Short and calculated params
    parameter int DW        = CXS_DATA_WIDTH,
    parameter int N         = CXS_MAX_PKT_PER_FLIT,
    parameter int CNTL_W    = cntl_width(N, DW, CXS_START_ALIGN),
    parameter int CNTL_PW   = port_w(CNTL_W),
    parameter int SRCID_PW  = port_w(CXS_SRCID_WIDTH),
    parameter int TGTID_PW  = port_w(CXS_TGTID_WIDTH),
    parameter int USER_PW   = port_w(CXS_USER_WIDTH),
    parameter int DATACHK_W = chk_width(DW),
    parameter int CNTLCHK_W = port_w(chk_width(CNTL_W)),
    parameter int USERCHK_W = port_w(chk_width(CXS_USER_WIDTH)),
    parameter int CRW       = $clog2(CXS_MAX_CREDIT + 1)
) (
    input  logic                           aclk,
    input  logic                           aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Configuration
    input  logic                  cfg_link_enable,
    input  logic                  cfg_link_hold,
    input  logic [7:0]            cfg_idle_cycles,

    // FUB side
    input  logic                  fub_cxs_valid,
    output logic                  fub_cxs_ready,
    input  logic [DW-1:0]         fub_cxs_data,
    input  logic [CNTL_PW-1:0]    fub_cxs_cntl,
    input  logic                  fub_cxs_last,
    input  logic [2:0]            fub_cxs_prcltype,
    input  logic [SRCID_PW-1:0]   fub_cxs_srcid,
    input  logic [TGTID_PW-1:0]   fub_cxs_tgtid,
    input  logic [USER_PW-1:0]    fub_cxs_user,

    // CXS Transmitter interface
    output logic                  m_cxs_valid,
    output logic [DW-1:0]         m_cxs_data,
    output logic [CNTL_PW-1:0]    m_cxs_cntl,
    output logic                  m_cxs_last,
    output logic [2:0]            m_cxs_prcltype,
    output logic [SRCID_PW-1:0]   m_cxs_srcid,
    output logic [TGTID_PW-1:0]   m_cxs_tgtid,
    output logic [USER_PW-1:0]    m_cxs_user,
    input  logic                  m_cxs_crdgnt,
    output logic                  m_cxs_crdrtn,
    output logic                  m_cxs_activereq,
    input  logic                  m_cxs_activeack,
    input  logic                  m_cxs_deacthint,

    // CXS check signals
    output logic                  m_cxs_validchk,
    output logic [DATACHK_W-1:0]  m_cxs_datachk,
    output logic [CNTLCHK_W-1:0]  m_cxs_cntlchk,
    output logic                  m_cxs_lastchk,
    output logic                  m_cxs_prcltypechk,
    output logic                  m_cxs_srcidchk,
    output logic                  m_cxs_tgtidchk,
    output logic [USERCHK_W-1:0]  m_cxs_userchk,
    input  logic                  m_cxs_crdgntchk,
    output logic                  m_cxs_crdrtnchk,
    output logic                  m_cxs_activereqchk,
    input  logic                  m_cxs_activeackchk,

    // Status
    output logic [CRW-1:0]        credits,
    output logic [1:0]            link_state,
    output logic                  in_packet,
    output logic                  credit_starved,
    output logic                  protocol_error,
    output logic                  parity_error,

    // Clock gating status
    output logic                  cg_gating,
    output logic                  cg_idle
);

    logic gated_aclk;
    logic int_busy;
    logic int_ready;
    logic int_valid;
    logic int_crdrtn;
    logic int_validchk;
    logic int_crdrtnchk;
    logic user_valid;
    logic axi_valid;

    assign user_valid = fub_cxs_valid || int_busy;
    assign axi_valid  = m_cxs_crdgnt || m_cxs_activeack;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in            (aclk),
        .aresetn           (aresetn),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .user_valid        (user_valid),
        .axi_valid         (axi_valid),
        .clk_out           (gated_aclk),
        .gating            (cg_gating),
        .idle              (cg_idle)
    );

    // Event outputs and FUB ready are masked during gating; the check bits
    // follow their masked signals (a masked 0 carries check 1).
    assign fub_cxs_ready   = cg_gating ? 1'b0 : int_ready;
    assign m_cxs_valid     = cg_gating ? 1'b0 : int_valid;
    assign m_cxs_crdrtn    = cg_gating ? 1'b0 : int_crdrtn;
    assign m_cxs_validchk  = (cg_gating && CXS_CHECK) ? 1'b1 : int_validchk;
    assign m_cxs_crdrtnchk = (cg_gating && CXS_CHECK) ? 1'b1 : int_crdrtnchk;

    cxs_master #(
        .CXS_ISSUE            (CXS_ISSUE),
        .CXS_DATA_WIDTH       (CXS_DATA_WIDTH),
        .CXS_MAX_PKT_PER_FLIT (CXS_MAX_PKT_PER_FLIT),
        .CXS_START_ALIGN      (CXS_START_ALIGN),
        .CXS_HAS_LAST         (CXS_HAS_LAST),
        .CXS_HAS_PRCLTYPE     (CXS_HAS_PRCLTYPE),
        .CXS_SRCID_WIDTH      (CXS_SRCID_WIDTH),
        .CXS_TGTID_WIDTH      (CXS_TGTID_WIDTH),
        .CXS_USER_WIDTH       (CXS_USER_WIDTH),
        .CXS_MAX_CREDIT       (CXS_MAX_CREDIT),
        .CXS_CREDIT_BEYOND_SPEC(CXS_CREDIT_BEYOND_SPEC),
        .CXS_STREAM_PRCL_BITS (CXS_STREAM_PRCL_BITS),
        .CXS_STREAM_SRCID_BITS(CXS_STREAM_SRCID_BITS),
        .CXS_STREAM_TGTID_BITS(CXS_STREAM_TGTID_BITS),
        .CXS_LINK_CTRL        (CXS_LINK_CTRL),
        .CXS_CHECK            (CXS_CHECK),
        .SKID_DEPTH           (SKID_DEPTH)
    ) i_cxs_master (
        .aclk               (gated_aclk),
        .aresetn            (aresetn),
        .cfg_link_enable    (cfg_link_enable),
        .cfg_link_hold      (cfg_link_hold),
        .cfg_idle_cycles    (cfg_idle_cycles),
        .fub_cxs_valid      (fub_cxs_valid),
        .fub_cxs_ready      (int_ready),
        .fub_cxs_data       (fub_cxs_data),
        .fub_cxs_cntl       (fub_cxs_cntl),
        .fub_cxs_last       (fub_cxs_last),
        .fub_cxs_prcltype   (fub_cxs_prcltype),
        .fub_cxs_srcid      (fub_cxs_srcid),
        .fub_cxs_tgtid      (fub_cxs_tgtid),
        .fub_cxs_user       (fub_cxs_user),
        .m_cxs_valid        (int_valid),
        .m_cxs_data         (m_cxs_data),
        .m_cxs_cntl         (m_cxs_cntl),
        .m_cxs_last         (m_cxs_last),
        .m_cxs_prcltype     (m_cxs_prcltype),
        .m_cxs_srcid        (m_cxs_srcid),
        .m_cxs_tgtid        (m_cxs_tgtid),
        .m_cxs_user         (m_cxs_user),
        .m_cxs_crdgnt       (m_cxs_crdgnt),
        .m_cxs_crdrtn       (int_crdrtn),
        .m_cxs_activereq    (m_cxs_activereq),
        .m_cxs_activeack    (m_cxs_activeack),
        .m_cxs_deacthint    (m_cxs_deacthint),
        .m_cxs_validchk     (int_validchk),
        .m_cxs_datachk      (m_cxs_datachk),
        .m_cxs_cntlchk      (m_cxs_cntlchk),
        .m_cxs_lastchk      (m_cxs_lastchk),
        .m_cxs_prcltypechk  (m_cxs_prcltypechk),
        .m_cxs_srcidchk     (m_cxs_srcidchk),
        .m_cxs_tgtidchk     (m_cxs_tgtidchk),
        .m_cxs_userchk      (m_cxs_userchk),
        .m_cxs_crdgntchk    (m_cxs_crdgntchk),
        .m_cxs_crdrtnchk    (int_crdrtnchk),
        .m_cxs_activereqchk (m_cxs_activereqchk),
        .m_cxs_activeackchk (m_cxs_activeackchk),
        .busy               (int_busy),
        .credits            (credits),
        .link_state         (link_state),
        .in_packet          (in_packet),
        .credit_starved     (credit_starved),
        .protocol_error     (protocol_error),
        .parity_error       (parity_error)
    );

endmodule : cxs_master_cg
