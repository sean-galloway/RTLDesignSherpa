// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_rnf_port
// Purpose: CHI Request Node (RN-F) port (Arm IHI 0050 Issue H): the link layer of
//          the requester side of one link pair, FUB valid/ready flits on one
//          side and credited CHI channels with the LINKACTIVE handshake on
//          the other
//
// Documentation: docs/markdown/rtl-amba/chi/chi_rnf_port.md
// Subsystem: amba
//
// The CHI counterpart of cxs_master / cxs_slave, except that a CHI port is
// a PAIR of links (B13.2): this block transmits on REQ, RSP, DAT and
// receives on RSP, DAT, SNP (Table B13.1 for RN-F). It is the
// link layer only (chapters B13 and B14): credits, FLITPEND, the two
// LINKACTIVE pairs, LCrdReturn and SACTIVE. Flits are opaque to it beyond
// the Opcode (zero = Link flit) and TxnID; the Protocol layer (B2 to B12)
// lives on the FUB side. This port is an RN-F: its Protocol layer (a core, a cluster, a DMA with a
// coherent cache) issues requests on fub_txreq, answers snoops and sends
// CompAck / write data on fub_txrsp and fub_txdat, and receives completions
// and snoops on fub_rxrsp, fub_rxdat and fub_rxsnp. The link side faces the
// interconnect (an HN-F); the RDS-DV CHIHomeNode BFM drives it with
// prefix 'm_chi_' and nothing else.
//
// Per channel: chi_tx_channel (skid buffer, credit counter, FLITPEND) or
// chi_rx_channel (receive FIFO as the credit pool, LCRDV). Per direction:
// chi_link_tx drives TXLINKACTIVEREQ, chi_link_rx drives RXLINKACTIVEACK,
// and the two are cross-coupled for B14.6 (a remote activation brings the
// other direction up by itself) and B14.6.3.4 (output ordering).
//
// TXSACTIVE (B14.7.2): asserted while fub_sactive is high (the Protocol
// layer's "transactions in progress") or any TX channel holds a flit. The
// Protocol layer must keep fub_sactive high from before its first request
// flit until its last completing flit is sent or received; the link layer
// cannot know that on its own. TXSACTIVE is combinational from fub_sactive
// and the FUB valids (on purpose: "before or in the same cycle" as the first
// flit) and held one cycle after they fall; it is the one port output with
// a combinational path from a FUB input. RXSACTIVE is passed through to
// fub_rxsactive so the Protocol layer can answer "in a timely manner"
// (B14.7.3).
//
// cfg_link_enable = 0 does not keep the TX link up (it drops when idle and
// is not held); queued flits and a remote activation still raise it.
// cfg_rx_enable = 0 keeps the whole port in STOP: no activation is
// acknowledged and none is started (see chi_link_tx).
//
// Parameters (every width as the RDS-DV CHIConfig names it; an illegal set
// stops elaboration with the chi_pkg::config_error rule number):
//   - NODEID_WIDTH 7..16, ADDR_WIDTH 44..52, DATA_WIDTH 128/256/512
//   - REQ_RSVDC_WIDTH / DAT_RSVDC_WIDTH 0,4,8,12,16,24,32
//   - MPAM_WIDTH 0/12/15, PBHA_WIDTH 0/4, MECID_WIDTH 0/16,
//     STREAMID_WIDTH 0/16, SECSID1_WIDTH 0/1, DATA_CHECK, POISON
//   - MAX_LCREDIT: 1..15, the same bound on every channel
//   - LINK_CTRL: 1 = LINKACTIVE handshake, 0 = always RUN (pins tied)
//   - SKID_DEPTH: TX skid buffers, 2..8; RX_FIFO_DEPTH: receive FIFO per RX
//     channel = its credit pool, default MAX_LCREDIT
//   - LINKACTIVE_SYNC_STAGES: synchronizer flops on RXLINKACTIVEREQ, 0 or >= 2.
//     Grants may continue for that many + 1 cycles after the pin falls
//     (Table B14.2 allows credits when first entering DEACTIVATE); a
//     checker's DEACTIVATE grace must cover it
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module chi_rnf_port
    import chi_pkg::*;
#(
    parameter int NODEID_WIDTH          = 7,
    parameter int ADDR_WIDTH            = 44,
    parameter int DATA_WIDTH            = 128,
    parameter int REQ_RSVDC_WIDTH       = 0,
    parameter int DAT_RSVDC_WIDTH       = 0,
    parameter int MPAM_WIDTH            = 0,
    parameter int PBHA_WIDTH            = 0,
    parameter int MECID_WIDTH           = 0,
    parameter int STREAMID_WIDTH        = 0,
    parameter int SECSID1_WIDTH         = 0,
    parameter bit DATA_CHECK            = 1'b0,
    parameter bit POISON                = 1'b0,
    parameter int MAX_LCREDIT           = 15,
    parameter bit LINK_CTRL             = 1'b1,
    parameter int SKID_DEPTH            = 4,
    parameter int RX_FIFO_DEPTH         = MAX_LCREDIT,
    parameter int LINKACTIVE_SYNC_STAGES = 2,

    // Short and calculated params
    parameter int REQ_W = req_flit_w(NODEID_WIDTH, ADDR_WIDTH, REQ_RSVDC_WIDTH, MPAM_WIDTH, PBHA_WIDTH,
                                     MECID_WIDTH, STREAMID_WIDTH, SECSID1_WIDTH),
    parameter int RSP_W = rsp_flit_w(NODEID_WIDTH),
    parameter int SNP_W = snp_flit_w(NODEID_WIDTH, ADDR_WIDTH, MPAM_WIDTH, MECID_WIDTH),
    parameter int DAT_W = dat_flit_w(NODEID_WIDTH, DATA_WIDTH, DAT_RSVDC_WIDTH, DATA_CHECK, POISON,
                                     MECID_WIDTH),
    parameter int CRW   = $clog2(MAX_LCREDIT + 1)
) (
    // Global Clock and Reset
    input  logic             aclk,
    input  logic             aresetn,

    // Configuration
    input  logic             cfg_link_enable,   // 0 = do not keep the TX link up: drop when idle, never hold
    input  logic             cfg_link_hold,     // 1 = keep the TX link in RUN with nothing to send
    input  logic [7:0]       cfg_idle_cycles,   // idle RUN cycles before deactivating; 0 = never
    input  logic             cfg_rx_enable,     // 0 = keep the port in STOP: no activation acknowledged or started
    input  logic             fub_sactive,       // Protocol layer: transactions in progress (B14.7.2)
    output logic             fub_rxsactive,     // RXSACTIVE passed through (B14.7.3)

    // FUB side: transmit channels (valid/ready flits in)
    input  logic             fub_txreq_valid,
    output logic             fub_txreq_ready,
    input  logic [REQ_W-1:0] fub_txreq_flit,
    input  logic             fub_txrsp_valid,
    output logic             fub_txrsp_ready,
    input  logic [RSP_W-1:0] fub_txrsp_flit,
    input  logic             fub_txdat_valid,
    output logic             fub_txdat_ready,
    input  logic [DAT_W-1:0] fub_txdat_flit,

    // FUB side: receive channels (valid/ready flits out)
    output logic             fub_rxrsp_valid,
    input  logic             fub_rxrsp_ready,
    output logic [RSP_W-1:0] fub_rxrsp_flit,
    output logic             fub_rxdat_valid,
    input  logic             fub_rxdat_ready,
    output logic [DAT_W-1:0] fub_rxdat_flit,
    output logic             fub_rxsnp_valid,
    input  logic             fub_rxsnp_ready,
    output logic [SNP_W-1:0] fub_rxsnp_flit,

    // CHI link: activity and LINKACTIVE pairs (B14.5, B14.7)
    output logic             m_chi_txsactive,
    input  logic             m_chi_rxsactive,
    output logic             m_chi_txlinkactivereq,
    input  logic             m_chi_txlinkactiveack,
    input  logic             m_chi_rxlinkactivereq,
    output logic             m_chi_rxlinkactiveack,

    // CHI link: transmit channels
    output logic             m_chi_txreqflitpend,
    output logic             m_chi_txreqflitv,
    output logic [REQ_W-1:0] m_chi_txreqflit,
    input  logic             m_chi_txreqlcrdv,
    output logic             m_chi_txrspflitpend,
    output logic             m_chi_txrspflitv,
    output logic [RSP_W-1:0] m_chi_txrspflit,
    input  logic             m_chi_txrsplcrdv,
    output logic             m_chi_txdatflitpend,
    output logic             m_chi_txdatflitv,
    output logic [DAT_W-1:0] m_chi_txdatflit,
    input  logic             m_chi_txdatlcrdv,

    // CHI link: receive channels
    input  logic             m_chi_rxrspflitpend,
    input  logic             m_chi_rxrspflitv,
    input  logic [RSP_W-1:0] m_chi_rxrspflit,
    output logic             m_chi_rxrsplcrdv,
    input  logic             m_chi_rxdatflitpend,
    input  logic             m_chi_rxdatflitv,
    input  logic [DAT_W-1:0] m_chi_rxdatflit,
    output logic             m_chi_rxdatlcrdv,
    input  logic             m_chi_rxsnpflitpend,
    input  logic             m_chi_rxsnpflitv,
    input  logic [SNP_W-1:0] m_chi_rxsnpflit,
    output logic             m_chi_rxsnplcrdv,

    // Status
    output logic             busy,              // any flit queued or buffered, or a link not in STOP
    output logic [1:0]       tx_link_state,     // {TXLINKACTIVEREQ, TXLINKACTIVEACK sampled}: 00 STOP 10 ACTIVATE 11 RUN 01 DEACTIVATE; 11 with LINK_CTRL = 0
    output logic [1:0]       rx_link_state,     // {RXLINKACTIVEREQ sampled, RXLINKACTIVEACK}
    output logic [CRW-1:0]   txreq_credits,      // credits held on TXREQ
    output logic [CRW-1:0]   txrsp_credits,      // credits held on TXRSP
    output logic [CRW-1:0]   txdat_credits,      // credits held on TXDAT
    output logic [CRW-1:0]   rxrsp_outstanding,  // credits granted and not home on RXRSP
    output logic [CRW-1:0]   rxdat_outstanding,  // credits granted and not home on RXDAT
    output logic [CRW-1:0]   rxsnp_outstanding,  // credits granted and not home on RXSNP
    output logic             credit_starved,    // a flit waits in RUN with no credit on some TX channel
    output logic             protocol_error     // sticky OR of every channel's protocol error
);

    // ------------------------------------------------------------------
    // Elaboration-time property check (the one sanctioned guard form)
    // ------------------------------------------------------------------
    localparam int CFG_ERR = config_error(NODEID_WIDTH, ADDR_WIDTH, DATA_WIDTH, REQ_RSVDC_WIDTH,
                                          DAT_RSVDC_WIDTH, MPAM_WIDTH, PBHA_WIDTH, MECID_WIDTH,
                                          STREAMID_WIDTH, SECSID1_WIDTH, MAX_LCREDIT);
`ifndef SYNTHESIS
    initial begin : param_check
        if (CFG_ERR != 0)
            $fatal(1, "chi_rnf_port: illegal CHI property set (rule %0d, see chi_pkg::config_error)",
                   CFG_ERR);
        if (RX_FIFO_DEPTH < 1)
            $fatal(1, "chi_rnf_port: RX_FIFO_DEPTH must be >= 1 (it is the credit pool)");
        if (LINKACTIVE_SYNC_STAGES == 1)
            $fatal(1, "chi_rnf_port: LINKACTIVE_SYNC_STAGES must be 0 (synchronous) or >= 2");
        if (SKID_DEPTH < 2 || SKID_DEPTH > 8)
            $fatal(1, "chi_rnf_port: SKID_DEPTH must be 2..8");
    end
`endif

    // ------------------------------------------------------------------
    // Link directions
    // ------------------------------------------------------------------
    logic w_tx_run, w_tx_deact, w_tx_want;
    logic w_rx_grant_ok, w_rx_req_s, w_rx_all_returned;

    logic w_txreq_busy, w_txreq_starved, w_txreq_err;
    logic w_txrsp_busy, w_txrsp_starved, w_txrsp_err;
    logic w_txdat_busy, w_txdat_starved, w_txdat_err;
    logic w_rxrsp_busy, w_rxrsp_all_returned, w_rxrsp_err;
    logic w_rxdat_busy, w_rxdat_all_returned, w_rxdat_err;
    logic w_rxsnp_busy, w_rxsnp_all_returned, w_rxsnp_err;

    assign w_tx_want          = w_txreq_busy || w_txrsp_busy || w_txdat_busy;
    assign w_rx_all_returned  = w_rxrsp_all_returned && w_rxdat_all_returned && w_rxsnp_all_returned;

    chi_link_tx #(.LINK_CTRL (LINK_CTRL)) u_link_tx (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .cfg_link_enable (cfg_link_enable),
        .cfg_link_hold   (cfg_link_hold),
        .cfg_idle_cycles (cfg_idle_cycles),
        .cfg_rx_enable   (cfg_rx_enable),
        .i_want          (w_tx_want),
        .i_rx_req        (w_rx_req_s),
        .i_rx_ack        (m_chi_rxlinkactiveack),
        .o_req           (m_chi_txlinkactivereq),
        .i_ack           (m_chi_txlinkactiveack),
        .o_run           (w_tx_run),
        .o_deact         (w_tx_deact),
        .o_state         (tx_link_state)
    );

    chi_link_rx #(
        .LINK_CTRL              (LINK_CTRL),
        .LINKACTIVE_SYNC_STAGES (LINKACTIVE_SYNC_STAGES)
    ) u_link_rx (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .cfg_rx_enable  (cfg_rx_enable),
        .i_all_returned (w_rx_all_returned),
        .i_tx_req       (m_chi_txlinkactivereq),
        .i_req          (m_chi_rxlinkactivereq),
        .o_ack          (m_chi_rxlinkactiveack),
        .o_req_s        (w_rx_req_s),
        .o_grant_ok     (w_rx_grant_ok),
        .o_state        (rx_link_state)
    );

    // ------------------------------------------------------------------
    // Transmit channels
    // ------------------------------------------------------------------
    chi_tx_channel #(
        .FLIT_W      (REQ_W),
        .MAX_LCREDIT (MAX_LCREDIT),
        .SKID_DEPTH  (SKID_DEPTH)
    ) u_txreq (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_run            (w_tx_run),
        .i_deact          (w_tx_deact),
        .fub_valid        (fub_txreq_valid),
        .fub_ready        (fub_txreq_ready),
        .fub_flit         (fub_txreq_flit),
        .o_flitpend       (m_chi_txreqflitpend),
        .o_flitv          (m_chi_txreqflitv),
        .o_flit           (m_chi_txreqflit),
        .i_lcrdv          (m_chi_txreqlcrdv),
        .o_credits        (txreq_credits),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_all_returned   (),
        /* verilator lint_on PINCONNECTEMPTY */
        .o_busy           (w_txreq_busy),
        .o_credit_starved (w_txreq_starved),
        .o_protocol_error (w_txreq_err)
    );

    chi_tx_channel #(
        .FLIT_W      (RSP_W),
        .MAX_LCREDIT (MAX_LCREDIT),
        .SKID_DEPTH  (SKID_DEPTH)
    ) u_txrsp (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_run            (w_tx_run),
        .i_deact          (w_tx_deact),
        .fub_valid        (fub_txrsp_valid),
        .fub_ready        (fub_txrsp_ready),
        .fub_flit         (fub_txrsp_flit),
        .o_flitpend       (m_chi_txrspflitpend),
        .o_flitv          (m_chi_txrspflitv),
        .o_flit           (m_chi_txrspflit),
        .i_lcrdv          (m_chi_txrsplcrdv),
        .o_credits        (txrsp_credits),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_all_returned   (),
        /* verilator lint_on PINCONNECTEMPTY */
        .o_busy           (w_txrsp_busy),
        .o_credit_starved (w_txrsp_starved),
        .o_protocol_error (w_txrsp_err)
    );

    chi_tx_channel #(
        .FLIT_W      (DAT_W),
        .MAX_LCREDIT (MAX_LCREDIT),
        .SKID_DEPTH  (SKID_DEPTH)
    ) u_txdat (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_run            (w_tx_run),
        .i_deact          (w_tx_deact),
        .fub_valid        (fub_txdat_valid),
        .fub_ready        (fub_txdat_ready),
        .fub_flit         (fub_txdat_flit),
        .o_flitpend       (m_chi_txdatflitpend),
        .o_flitv          (m_chi_txdatflitv),
        .o_flit           (m_chi_txdatflit),
        .i_lcrdv          (m_chi_txdatlcrdv),
        .o_credits        (txdat_credits),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_all_returned   (),
        /* verilator lint_on PINCONNECTEMPTY */
        .o_busy           (w_txdat_busy),
        .o_credit_starved (w_txdat_starved),
        .o_protocol_error (w_txdat_err)
    );

    // ------------------------------------------------------------------
    // Receive channels
    // ------------------------------------------------------------------
    chi_rx_channel #(
        .FLIT_W        (RSP_W),
        .OPCODE_LSB    (rsp_opcode_lsb(NODEID_WIDTH)),
        .OPCODE_W      (RSP_OPCODE_W),
        .TXNID_LSB     (rsp_txnid_lsb(NODEID_WIDTH)),
        .TXNID_W       (CHI_TXNID_W),
        .MAX_LCREDIT   (MAX_LCREDIT),
        .RX_FIFO_DEPTH (RX_FIFO_DEPTH)
    ) u_rxrsp (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_grant_ok       (w_rx_grant_ok),
        .i_flitpend       (m_chi_rxrspflitpend),
        .i_flitv          (m_chi_rxrspflitv),
        .i_flit           (m_chi_rxrspflit),
        .o_lcrdv          (m_chi_rxrsplcrdv),
        .fub_valid        (fub_rxrsp_valid),
        .fub_ready        (fub_rxrsp_ready),
        .fub_flit         (fub_rxrsp_flit),
        .o_outstanding    (rxrsp_outstanding),
        .o_all_returned   (w_rxrsp_all_returned),
        .o_busy           (w_rxrsp_busy),
        .o_protocol_error (w_rxrsp_err)
    );

    chi_rx_channel #(
        .FLIT_W        (DAT_W),
        .OPCODE_LSB    (dat_opcode_lsb(NODEID_WIDTH)),
        .OPCODE_W      (DAT_OPCODE_W),
        .TXNID_LSB     (dat_txnid_lsb(NODEID_WIDTH)),
        .TXNID_W       (CHI_TXNID_W),
        .MAX_LCREDIT   (MAX_LCREDIT),
        .RX_FIFO_DEPTH (RX_FIFO_DEPTH)
    ) u_rxdat (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_grant_ok       (w_rx_grant_ok),
        .i_flitpend       (m_chi_rxdatflitpend),
        .i_flitv          (m_chi_rxdatflitv),
        .i_flit           (m_chi_rxdatflit),
        .o_lcrdv          (m_chi_rxdatlcrdv),
        .fub_valid        (fub_rxdat_valid),
        .fub_ready        (fub_rxdat_ready),
        .fub_flit         (fub_rxdat_flit),
        .o_outstanding    (rxdat_outstanding),
        .o_all_returned   (w_rxdat_all_returned),
        .o_busy           (w_rxdat_busy),
        .o_protocol_error (w_rxdat_err)
    );

    chi_rx_channel #(
        .FLIT_W        (SNP_W),
        .OPCODE_LSB    (snp_opcode_lsb(NODEID_WIDTH)),
        .OPCODE_W      (SNP_OPCODE_W),
        .TXNID_LSB     (snp_txnid_lsb(NODEID_WIDTH)),
        .TXNID_W       (CHI_TXNID_W),
        .MAX_LCREDIT   (MAX_LCREDIT),
        .RX_FIFO_DEPTH (RX_FIFO_DEPTH)
    ) u_rxsnp (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_grant_ok       (w_rx_grant_ok),
        .i_flitpend       (m_chi_rxsnpflitpend),
        .i_flitv          (m_chi_rxsnpflitv),
        .i_flit           (m_chi_rxsnpflit),
        .o_lcrdv          (m_chi_rxsnplcrdv),
        .fub_valid        (fub_rxsnp_valid),
        .fub_ready        (fub_rxsnp_ready),
        .fub_flit         (fub_rxsnp_flit),
        .o_outstanding    (rxsnp_outstanding),
        .o_all_returned   (w_rxsnp_all_returned),
        .o_busy           (w_rxsnp_busy),
        .o_protocol_error (w_rxsnp_err)
    );

    // ------------------------------------------------------------------
    // SACTIVE and status
    // ------------------------------------------------------------------
    logic r_sactive;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_sactive <= 1'b0;
        end else begin
            r_sactive <= fub_sactive || w_tx_want;
        end
    )

    assign m_chi_txsactive = r_sactive || fub_sactive || w_tx_want;

    assign busy = w_tx_want || w_rxrsp_busy || w_rxdat_busy || w_rxsnp_busy ||
                  (tx_link_state != CHI_LINK_STOP) || (rx_link_state != CHI_LINK_STOP);
    assign credit_starved = w_txreq_starved || w_txrsp_starved || w_txdat_starved;
    assign protocol_error = w_txreq_err || w_txrsp_err || w_txdat_err || w_rxrsp_err || w_rxdat_err || w_rxsnp_err;

    assign fub_rxsactive = m_chi_rxsactive;

endmodule : chi_rnf_port
