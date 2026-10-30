// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_rnf_port_monlite
// Purpose: chi_rnf_port with chi_monitor_lite tapping it (amba TASK-050)
//
// Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-30
//
// ============================================================================
// The CHI analogue of cxs_master_monlite: the port is passed through
// untouched; chi_monitor_lite taps its six FUB handshakes and its registered
// status, never a link pin. This is an RN-F port: requests out, completions and snoops in, so the
// monitor's message-direction taps map as req = fub_txreq, cpl_rsp = fub_rxrsp,
// cpl_dat = fub_rxdat, rq_rsp = fub_txrsp, rq_dat = fub_txdat, snp = fub_rxsnp,
// with IS_REQUESTER = 1 naming the port's receive channels for backpressure.
//
// Every core parameter and port is declared here verbatim from chi_rnf_port
// (generated from it) and passed through by name. cfg_monitor_enable gates
// the tap's valids and holds the ocelus clear; cfg_timeout_cycles is in
// MICROSECONDS with 0 = never (mapped to the lite's 16'hFFFF). The monbus
// outputs, when USE_MONITOR = 0, are tied low.
// ============================================================================
`timescale 1ns / 1ps

module chi_rnf_port_monlite
    import chi_pkg::*;
#(
    // ---- Ocelus parameters ----
    parameter bit          USE_MONITOR          = 1'b1,   // 0 = omit the ocelus, tie its outputs
    parameter logic [7:0]  UNIT_ID              = 8'h0B,
    parameter logic [15:0] AGENT_ID             = 16'h00D0,
    parameter int          MAX_TRANSACTIONS     = 8,      // request slots in the ocelus
    parameter int          MAX_SNOOPS           = 4,      // snoop slots in the ocelus
    parameter int          OUT_DEPTH            = 4,      // monbus output queue
    parameter int          ACLK_MHZ             = 100,
    parameter int          CFI_MIN_FREQ_MHZ     = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ     = ACLK_MHZ,
    // ---- Core parameters (verbatim from chi_rnf_port) ----

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
    // ---- Core ports (verbatim from chi_rnf_port) ----

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
    output logic             protocol_error, // sticky OR of every channel's protocol error
    // ---- Ocelus control ----
    input  logic                                  cam_clear,           // sync clear of the ocelus state; legal only while idle
    input  logic                                  cfg_monitor_enable,  // 0 = ocelus inert, state held clear
    input  logic                                  cfg_error_enable,
    input  logic                                  cfg_timeout_enable,
    input  logic                                  cfg_compl_enable,
    input  logic                                  cfg_credit_enable,
    input  logic                                  cfg_channel_enable,
    input  logic                                  cfg_stream_enable,
    input  logic [15:0]                           cfg_timeout_cycles,  // MICROSECONDS (transaction, snoop, credit wait, stuck link); 0 = never
    input  logic [3:0]                            cfg_freq_sel,        // counter_freq_invariant LUT index
    input  logic [15:0]                           cfg_chi_pkt_mask,    // drop mask by packet type
    input  logic [31:0]                           cfg_stall_threshold, // CYCLES of starvation/backpressure before a Credit event; 0 = off
    input  ocelus_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Ocelus bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output ocelus_common_pkg::monitor_packet_t   monbus_packet,
    output ocelus_common_pkg::monbus_timestamp_t monbus_timestamp,
    // ---- Ocelus status ----
    output logic [$clog2(MAX_TRANSACTIONS+1)-1:0] active_count,        // request slots in use
    output logic [31:0]                           txn_count,           // requests retired
    output logic [31:0]                           snoop_count,         // snoops answered
    output logic [15:0]                           error_count,         // error packets emitted
    output logic [15:0]                           dropped_count        // events lost to monbus backpressure since the last report
);

    // ------------------------------------------------------------------------
    // The core, passed through
    // ------------------------------------------------------------------------
    chi_rnf_port #(
        .NODEID_WIDTH          (NODEID_WIDTH),
        .ADDR_WIDTH            (ADDR_WIDTH),
        .DATA_WIDTH            (DATA_WIDTH),
        .REQ_RSVDC_WIDTH       (REQ_RSVDC_WIDTH),
        .DAT_RSVDC_WIDTH       (DAT_RSVDC_WIDTH),
        .MPAM_WIDTH            (MPAM_WIDTH),
        .PBHA_WIDTH            (PBHA_WIDTH),
        .MECID_WIDTH           (MECID_WIDTH),
        .STREAMID_WIDTH        (STREAMID_WIDTH),
        .SECSID1_WIDTH         (SECSID1_WIDTH),
        .DATA_CHECK            (DATA_CHECK),
        .POISON                (POISON),
        .MAX_LCREDIT           (MAX_LCREDIT),
        .LINK_CTRL             (LINK_CTRL),
        .SKID_DEPTH            (SKID_DEPTH),
        .RX_FIFO_DEPTH         (RX_FIFO_DEPTH),
        .LINKACTIVE_SYNC_STAGES(LINKACTIVE_SYNC_STAGES),
        .REQ_W                 (REQ_W),
        .RSP_W                 (RSP_W),
        .SNP_W                 (SNP_W),
        .DAT_W                 (DAT_W),
        .CRW                   (CRW)
    ) u_core (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .cfg_link_enable       (cfg_link_enable),
        .cfg_link_hold         (cfg_link_hold),
        .cfg_idle_cycles       (cfg_idle_cycles),
        .cfg_rx_enable         (cfg_rx_enable),
        .fub_sactive           (fub_sactive),
        .fub_rxsactive         (fub_rxsactive),
        .fub_txreq_valid       (fub_txreq_valid),
        .fub_txreq_ready       (fub_txreq_ready),
        .fub_txreq_flit        (fub_txreq_flit),
        .fub_txrsp_valid       (fub_txrsp_valid),
        .fub_txrsp_ready       (fub_txrsp_ready),
        .fub_txrsp_flit        (fub_txrsp_flit),
        .fub_txdat_valid       (fub_txdat_valid),
        .fub_txdat_ready       (fub_txdat_ready),
        .fub_txdat_flit        (fub_txdat_flit),
        .fub_rxrsp_valid       (fub_rxrsp_valid),
        .fub_rxrsp_ready       (fub_rxrsp_ready),
        .fub_rxrsp_flit        (fub_rxrsp_flit),
        .fub_rxdat_valid       (fub_rxdat_valid),
        .fub_rxdat_ready       (fub_rxdat_ready),
        .fub_rxdat_flit        (fub_rxdat_flit),
        .fub_rxsnp_valid       (fub_rxsnp_valid),
        .fub_rxsnp_ready       (fub_rxsnp_ready),
        .fub_rxsnp_flit        (fub_rxsnp_flit),
        .m_chi_txsactive       (m_chi_txsactive),
        .m_chi_rxsactive       (m_chi_rxsactive),
        .m_chi_txlinkactivereq (m_chi_txlinkactivereq),
        .m_chi_txlinkactiveack (m_chi_txlinkactiveack),
        .m_chi_rxlinkactivereq (m_chi_rxlinkactivereq),
        .m_chi_rxlinkactiveack (m_chi_rxlinkactiveack),
        .m_chi_txreqflitpend   (m_chi_txreqflitpend),
        .m_chi_txreqflitv      (m_chi_txreqflitv),
        .m_chi_txreqflit       (m_chi_txreqflit),
        .m_chi_txreqlcrdv      (m_chi_txreqlcrdv),
        .m_chi_txrspflitpend   (m_chi_txrspflitpend),
        .m_chi_txrspflitv      (m_chi_txrspflitv),
        .m_chi_txrspflit       (m_chi_txrspflit),
        .m_chi_txrsplcrdv      (m_chi_txrsplcrdv),
        .m_chi_txdatflitpend   (m_chi_txdatflitpend),
        .m_chi_txdatflitv      (m_chi_txdatflitv),
        .m_chi_txdatflit       (m_chi_txdatflit),
        .m_chi_txdatlcrdv      (m_chi_txdatlcrdv),
        .m_chi_rxrspflitpend   (m_chi_rxrspflitpend),
        .m_chi_rxrspflitv      (m_chi_rxrspflitv),
        .m_chi_rxrspflit       (m_chi_rxrspflit),
        .m_chi_rxrsplcrdv      (m_chi_rxrsplcrdv),
        .m_chi_rxdatflitpend   (m_chi_rxdatflitpend),
        .m_chi_rxdatflitv      (m_chi_rxdatflitv),
        .m_chi_rxdatflit       (m_chi_rxdatflit),
        .m_chi_rxdatlcrdv      (m_chi_rxdatlcrdv),
        .m_chi_rxsnpflitpend   (m_chi_rxsnpflitpend),
        .m_chi_rxsnpflitv      (m_chi_rxsnpflitv),
        .m_chi_rxsnpflit       (m_chi_rxsnpflit),
        .m_chi_rxsnplcrdv      (m_chi_rxsnplcrdv),
        .busy                  (busy),
        .tx_link_state         (tx_link_state),
        .rx_link_state         (rx_link_state),
        .txreq_credits         (txreq_credits),
        .txrsp_credits         (txrsp_credits),
        .txdat_credits         (txdat_credits),
        .rxrsp_outstanding     (rxrsp_outstanding),
        .rxdat_outstanding     (rxdat_outstanding),
        .rxsnp_outstanding     (rxsnp_outstanding),
        .credit_starved        (credit_starved),
        .protocol_error        (protocol_error)
    );

    // ------------------------------------------------------------------------
    // The tap
    // ------------------------------------------------------------------------
    logic [15:0] w_timeout_cnt;
    logic        w_mon_busy;
    assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        chi_monitor_lite #(
            .UNIT_ID          (UNIT_ID),
            .AGENT_ID         (AGENT_ID),
            .IS_REQUESTER     (1'b1),
            .NODEID_WIDTH     (NODEID_WIDTH),
            .ADDR_WIDTH       (ADDR_WIDTH),
            .DATA_WIDTH       (DATA_WIDTH),
            .MECID_WIDTH      (MECID_WIDTH),
            .REQ_W            (REQ_W),
            .RSP_W            (RSP_W),
            .SNP_W            (SNP_W),
            .DAT_W            (DAT_W),
            .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
            .MAX_SNOOPS       (MAX_SNOOPS),
            .OUT_DEPTH        (OUT_DEPTH),
            .CFI_MIN_FREQ_MHZ (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ (CFI_MAX_FREQ_MHZ)
        ) u_chi_monitor_lite (
            .aclk                (aclk),
            .aresetn             (aresetn),
            .clear               (cam_clear | ~cfg_monitor_enable),
            .i_mon_time          (i_mon_time),
            .req_valid           (fub_txreq_valid & cfg_monitor_enable),
            .req_ready           (fub_txreq_ready),
            .req_flit            (fub_txreq_flit),
            .cpl_rsp_valid       (fub_rxrsp_valid & cfg_monitor_enable),
            .cpl_rsp_ready       (fub_rxrsp_ready),
            .cpl_rsp_flit        (fub_rxrsp_flit),
            .cpl_dat_valid       (fub_rxdat_valid & cfg_monitor_enable),
            .cpl_dat_ready       (fub_rxdat_ready),
            .cpl_dat_flit        (fub_rxdat_flit),
            .rq_rsp_valid        (fub_txrsp_valid & cfg_monitor_enable),
            .rq_rsp_ready        (fub_txrsp_ready),
            .rq_rsp_flit         (fub_txrsp_flit),
            .rq_dat_valid        (fub_txdat_valid & cfg_monitor_enable),
            .rq_dat_ready        (fub_txdat_ready),
            .rq_dat_flit         (fub_txdat_flit),
            .snp_valid           (fub_rxsnp_valid & cfg_monitor_enable),
            .snp_ready           (fub_rxsnp_ready),
            .snp_flit            (fub_rxsnp_flit),
            .tx_link_state       (tx_link_state),
            .rx_link_state       (rx_link_state),
            .credit_starved      (credit_starved),
            .protocol_error      (protocol_error),
            .cfg_freq_sel        (cfg_freq_sel),
            .cfg_timeout_cnt     (w_timeout_cnt),
            .cfg_error_enable    (cfg_error_enable),
            .cfg_timeout_enable  (cfg_timeout_enable),
            .cfg_compl_enable    (cfg_compl_enable),
            .cfg_credit_enable   (cfg_credit_enable),
            .cfg_channel_enable  (cfg_channel_enable),
            .cfg_stream_enable   (cfg_stream_enable),
            .cfg_stall_threshold (cfg_stall_threshold),
            .cfg_chi_pkt_mask    (cfg_chi_pkt_mask),
            .monbus_valid        (monbus_valid),
            .monbus_ready        (monbus_ready),
            .monbus_packet       (monbus_packet),
            .monbus_timestamp    (monbus_timestamp),
            .busy                (w_mon_busy),
            .active_count        (active_count),
            .txn_count           (txn_count),
            .snoop_count         (snoop_count),
            .error_count         (error_count),
            .dropped_count       (dropped_count)
        );
    end else begin : gen_no_monitor
        assign monbus_valid     = 1'b0;
        assign monbus_packet    = '0;
        assign monbus_timestamp = '0;
        assign w_mon_busy       = 1'b0;
        assign active_count     = '0;
        assign txn_count        = '0;
        assign snoop_count      = '0;
        assign error_count      = '0;
        assign dropped_count    = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_cfg = ^{cam_clear, cfg_monitor_enable, cfg_error_enable, cfg_timeout_enable, cfg_compl_enable,
                            cfg_credit_enable, cfg_channel_enable, cfg_stream_enable, cfg_freq_sel, cfg_chi_pkt_mask,
                            cfg_stall_threshold, w_timeout_cnt, i_mon_time, monbus_ready};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_mon_busy;
    assign unused_mon_busy = w_mon_busy;
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : chi_rnf_port_monlite
