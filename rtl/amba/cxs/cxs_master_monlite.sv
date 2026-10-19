// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_master_monlite
// Purpose: cxs_master with cxs_monitor_lite tapping it (amba TASK-044)
//
// Documentation: docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-15
//
// ============================================================================
// The lite-ocelus sibling of cxs_master, in the axis4_*_monlite pattern. The CXS
// transmitter is passed through untouched; cxs_monitor_lite taps the FUB
// handshake (fub_cxs_*) and the core's registered status outputs (link_state,
// credits, credit_starved, protocol_error, parity_error) -- the owner rule that
// a monitor taps the FUB side and never the external link pins -- and emits
// PROTOCOL_CXS packets on the same monbus handshake, UNIT/AGENT ids and
// 128-bit packet as every other ocelus. The monitor drives nothing; an event
// the monbus will not take is dropped and COUNTED.
//
// Every core parameter and port is declared here verbatim from cxs_master
// (generated from it) and passed through by name. cfg_monitor_enable gates
// the tap and holds the ocelus clear; cfg_timeout_cycles is MICROSECONDS,
// 0 = never. No _cg variant: clock gating is an FPGA-only concern here.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"
module cxs_master_monlite
    import cxs_pkg::*;
#(
    // ---- Ocelus parameters ----
    parameter bit          USE_MONITOR          = 1'b1,   // 0 = omit the ocelus, tie its outputs
    parameter logic [7:0]  UNIT_ID              = 8'h0A,
    parameter logic [15:0] AGENT_ID             = 16'h00C0,
    parameter int          OUT_DEPTH            = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ             = 100,
    parameter int          CFI_MIN_FREQ_MHZ     = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ     = ACLK_MHZ,
    // ---- Core parameters (verbatim from cxs_master) ----
    parameter int  CXS_ISSUE              = CXS_ISSUE_D,
    parameter int  CXS_DATA_WIDTH         = 256,
    parameter int  CXS_MAX_PKT_PER_FLIT   = 2,
    parameter int  CXS_START_ALIGN        = 16,
    parameter bit  CXS_HAS_LAST           = 1'b0,
    parameter bit  CXS_HAS_PRCLTYPE       = 1'b0,
    parameter int  CXS_SRCID_WIDTH        = 0,
    parameter int  CXS_TGTID_WIDTH        = 0,
    parameter int  CXS_USER_WIDTH         = 0,
    parameter int  CXS_MAX_CREDIT         = 15,
    parameter bit  CXS_CREDIT_BEYOND_SPEC = 1'b0,   // see cxs_master / cxs_slave
    parameter int  CXS_STREAM_PRCL_BITS   = 0,      // per-stream tracking key (cxs_stream_key)
    parameter int  CXS_STREAM_SRCID_BITS  = 0,
    parameter int  CXS_STREAM_TGTID_BITS  = 0,
    parameter bit  CXS_LINK_CTRL          = 1'b1,
    parameter bit  CXS_CHECK              = 1'b0,
    parameter int  SKID_DEPTH             = 4,
    parameter int  DW                     = CXS_DATA_WIDTH,
    parameter int  N                      = CXS_MAX_PKT_PER_FLIT,
    parameter int  CNTL_W                 = cntl_width(N, DW, CXS_START_ALIGN),
    parameter int  CNTL_PW                = port_w(CNTL_W),
    parameter int  SRCID_PW               = port_w(CXS_SRCID_WIDTH),
    parameter int  TGTID_PW               = port_w(CXS_TGTID_WIDTH),
    parameter int  USER_PW                = port_w(CXS_USER_WIDTH),
    parameter int  DATACHK_W              = chk_width(DW),
    parameter int  CNTLCHK_W              = port_w(chk_width(CNTL_W)),
    parameter int  USERCHK_W              = port_w(chk_width(CXS_USER_WIDTH)),
    parameter int  CRW                    = $clog2(CXS_MAX_CREDIT + 1)
) (
    input  logic                    aclk,
    input  logic                    aresetn,
    input  logic                    cfg_link_enable,
    input  logic                    cfg_link_hold,
    input  logic [7:0]              cfg_idle_cycles,
    input  logic                    fub_cxs_valid,
    output logic                    fub_cxs_ready,
    input  logic [DW-1:0]           fub_cxs_data,
    input  logic [CNTL_PW-1:0]      fub_cxs_cntl,
    input  logic                    fub_cxs_last,
    input  logic [2:0]              fub_cxs_prcltype,
    input  logic [SRCID_PW-1:0]     fub_cxs_srcid,
    input  logic [TGTID_PW-1:0]     fub_cxs_tgtid,
    input  logic [USER_PW-1:0]      fub_cxs_user,
    output logic                    m_cxs_valid,
    output logic [DW-1:0]           m_cxs_data,
    output logic [CNTL_PW-1:0]      m_cxs_cntl,
    output logic                    m_cxs_last,
    output logic [2:0]              m_cxs_prcltype,
    output logic [SRCID_PW-1:0]     m_cxs_srcid,
    output logic [TGTID_PW-1:0]     m_cxs_tgtid,
    output logic [USER_PW-1:0]      m_cxs_user,
    input  logic                    m_cxs_crdgnt,
    output logic                    m_cxs_crdrtn,
    output logic                    m_cxs_activereq,
    input  logic                    m_cxs_activeack,
    input  logic                    m_cxs_deacthint,
    output logic                    m_cxs_validchk,
    output logic [DATACHK_W-1:0]    m_cxs_datachk,
    output logic [CNTLCHK_W-1:0]    m_cxs_cntlchk,
    output logic                    m_cxs_lastchk,
    output logic                    m_cxs_prcltypechk,
    output logic                    m_cxs_srcidchk,
    output logic                    m_cxs_tgtidchk,
    output logic [USERCHK_W-1:0]    m_cxs_userchk,
    input  logic                    m_cxs_crdgntchk,
    output logic                    m_cxs_crdrtnchk,
    output logic                    m_cxs_activereqchk,
    input  logic                    m_cxs_activeackchk,
    output logic                    busy,
    output logic [CRW-1:0]          credits,
    output logic [1:0]              link_state,
    output logic                    in_packet,
    output logic                    credit_starved,
    output logic                    protocol_error,
    output logic                    parity_error,
    // ---- Ocelus control ----
    input  logic                                  cam_clear,           // sync clear of the ocelus state; legal only while idle
    input  logic                                  cfg_monitor_enable,  // 0 = ocelus inert, state held clear
    input  logic                                  cfg_error_enable,
    input  logic                                  cfg_timeout_enable,
    input  logic                                  cfg_compl_enable,
    input  logic                                  cfg_credit_enable,
    input  logic                                  cfg_channel_enable,
    input  logic                                  cfg_stream_enable,
    input  logic [15:0]                           cfg_timeout_cycles,  // MICROSECONDS (credit wait, stuck link, packet gap); 0 = never
    input  logic [3:0]                            cfg_freq_sel,        // counter_freq_invariant LUT index
    input  logic [15:0]                           cfg_cxs_pkt_mask,    // drop mask by packet type
    input  logic [31:0]                           cfg_stall_threshold, // CYCLES of starvation/backpressure before a Credit event; 0 = off
    input  ocelus_common_pkg::monbus_timestamp_t i_mon_time,
    // ---- Ocelus bus ----
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output ocelus_common_pkg::monitor_packet_t   monbus_packet,
    output ocelus_common_pkg::monbus_timestamp_t monbus_timestamp,
    // ---- Ocelus status ----
    output logic [31:0]                           packet_count,        // packets ended on the FUB side
    output logic [31:0]                           flit_count,          // flits on the FUB side
    output logic [15:0]                           error_count,         // error packets emitted
    output logic [15:0]                           dropped_count        // events lost to monbus backpressure since the last report
);
    // ------------------------------------------------------------------------
    // The core, passed through untouched
    // ------------------------------------------------------------------------
    cxs_master #(
        .CXS_ISSUE             (CXS_ISSUE),
        .CXS_DATA_WIDTH        (CXS_DATA_WIDTH),
        .CXS_MAX_PKT_PER_FLIT  (CXS_MAX_PKT_PER_FLIT),
        .CXS_START_ALIGN       (CXS_START_ALIGN),
        .CXS_HAS_LAST          (CXS_HAS_LAST),
        .CXS_HAS_PRCLTYPE      (CXS_HAS_PRCLTYPE),
        .CXS_SRCID_WIDTH       (CXS_SRCID_WIDTH),
        .CXS_TGTID_WIDTH       (CXS_TGTID_WIDTH),
        .CXS_USER_WIDTH        (CXS_USER_WIDTH),
        .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
        .CXS_CREDIT_BEYOND_SPEC(CXS_CREDIT_BEYOND_SPEC),
        .CXS_STREAM_PRCL_BITS  (CXS_STREAM_PRCL_BITS),
        .CXS_STREAM_SRCID_BITS (CXS_STREAM_SRCID_BITS),
        .CXS_STREAM_TGTID_BITS (CXS_STREAM_TGTID_BITS),
        .CXS_LINK_CTRL         (CXS_LINK_CTRL),
        .CXS_CHECK             (CXS_CHECK),
        .SKID_DEPTH            (SKID_DEPTH),
        .DW                    (DW),
        .N                     (N),
        .CNTL_W                (CNTL_W),
        .CNTL_PW               (CNTL_PW),
        .SRCID_PW              (SRCID_PW),
        .TGTID_PW              (TGTID_PW),
        .USER_PW               (USER_PW),
        .DATACHK_W             (DATACHK_W),
        .CNTLCHK_W             (CNTLCHK_W),
        .USERCHK_W             (USERCHK_W),
        .CRW                   (CRW)
    ) u_core (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .cfg_link_enable       (cfg_link_enable),
        .cfg_link_hold         (cfg_link_hold),
        .cfg_idle_cycles       (cfg_idle_cycles),
        .fub_cxs_valid         (fub_cxs_valid),
        .fub_cxs_ready         (fub_cxs_ready),
        .fub_cxs_data          (fub_cxs_data),
        .fub_cxs_cntl          (fub_cxs_cntl),
        .fub_cxs_last          (fub_cxs_last),
        .fub_cxs_prcltype      (fub_cxs_prcltype),
        .fub_cxs_srcid         (fub_cxs_srcid),
        .fub_cxs_tgtid         (fub_cxs_tgtid),
        .fub_cxs_user          (fub_cxs_user),
        .m_cxs_valid           (m_cxs_valid),
        .m_cxs_data            (m_cxs_data),
        .m_cxs_cntl            (m_cxs_cntl),
        .m_cxs_last            (m_cxs_last),
        .m_cxs_prcltype        (m_cxs_prcltype),
        .m_cxs_srcid           (m_cxs_srcid),
        .m_cxs_tgtid           (m_cxs_tgtid),
        .m_cxs_user            (m_cxs_user),
        .m_cxs_crdgnt          (m_cxs_crdgnt),
        .m_cxs_crdrtn          (m_cxs_crdrtn),
        .m_cxs_activereq       (m_cxs_activereq),
        .m_cxs_activeack       (m_cxs_activeack),
        .m_cxs_deacthint       (m_cxs_deacthint),
        .m_cxs_validchk        (m_cxs_validchk),
        .m_cxs_datachk         (m_cxs_datachk),
        .m_cxs_cntlchk         (m_cxs_cntlchk),
        .m_cxs_lastchk         (m_cxs_lastchk),
        .m_cxs_prcltypechk     (m_cxs_prcltypechk),
        .m_cxs_srcidchk        (m_cxs_srcidchk),
        .m_cxs_tgtidchk        (m_cxs_tgtidchk),
        .m_cxs_userchk         (m_cxs_userchk),
        .m_cxs_crdgntchk       (m_cxs_crdgntchk),
        .m_cxs_crdrtnchk       (m_cxs_crdrtnchk),
        .m_cxs_activereqchk    (m_cxs_activereqchk),
        .m_cxs_activeackchk    (m_cxs_activeackchk),
        .busy                  (busy),
        .credits               (credits),
        .link_state            (link_state),
        .in_packet             (in_packet),
        .credit_starved        (credit_starved),
        .protocol_error        (protocol_error),
        .parity_error          (parity_error)
    );

    // ------------------------------------------------------------------------
    // The tap
    // ------------------------------------------------------------------------
    logic        w_mon_valid;
    logic [15:0] w_timeout_cnt;
    logic        w_mon_busy;
    assign w_mon_valid   = fub_cxs_valid & cfg_monitor_enable;
    assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor_lite
        cxs_monitor_lite #(
            .UNIT_ID              (UNIT_ID),
            .AGENT_ID             (AGENT_ID),
            .CXS_DATA_WIDTH       (CXS_DATA_WIDTH),
            .CXS_MAX_PKT_PER_FLIT (CXS_MAX_PKT_PER_FLIT),
            .CXS_START_ALIGN      (CXS_START_ALIGN),
            .CXS_SRCID_WIDTH      (CXS_SRCID_WIDTH),
            .CXS_TGTID_WIDTH      (CXS_TGTID_WIDTH),
            .CXS_MAX_CREDIT       (CXS_MAX_CREDIT),
            .CXS_STREAM_PRCL_BITS (CXS_STREAM_PRCL_BITS),
            .CXS_STREAM_SRCID_BITS(CXS_STREAM_SRCID_BITS),
            .CXS_STREAM_TGTID_BITS(CXS_STREAM_TGTID_BITS),
            .OUT_DEPTH            (OUT_DEPTH),
            .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ)
        ) u_cxs_monitor_lite (
            .aclk                (aclk),
            .aresetn             (aresetn),
            .clear               (cam_clear | ~cfg_monitor_enable),
            .i_mon_time          (i_mon_time),
            .fub_valid           (w_mon_valid),
            .fub_ready           (fub_cxs_ready),
            .fub_cntl            (fub_cxs_cntl),
            .fub_prcltype        (fub_cxs_prcltype),
            .fub_srcid           (fub_cxs_srcid),
            .fub_tgtid           (fub_cxs_tgtid),
            .link_state          (link_state),
            .credits             (credits),
            .credit_starved      (credit_starved),
            .protocol_error      (protocol_error),
            .parity_error        (parity_error),
            .cfg_freq_sel        (cfg_freq_sel),
            .cfg_timeout_cnt     (w_timeout_cnt),
            .cfg_error_enable    (cfg_error_enable),
            .cfg_timeout_enable  (cfg_timeout_enable),
            .cfg_compl_enable    (cfg_compl_enable),
            .cfg_credit_enable   (cfg_credit_enable),
            .cfg_channel_enable  (cfg_channel_enable),
            .cfg_stream_enable   (cfg_stream_enable),
            .cfg_stall_threshold (cfg_stall_threshold),
            .cfg_cxs_pkt_mask    (cfg_cxs_pkt_mask),
            .monbus_valid        (monbus_valid),
            .monbus_ready        (monbus_ready),
            .monbus_packet       (monbus_packet),
            .monbus_timestamp    (monbus_timestamp),
            .busy                (w_mon_busy),
            .packet_count        (packet_count),
            .flit_count          (flit_count),
            .error_count         (error_count),
            .dropped_count       (dropped_count)
        );
    end else begin : gen_no_monitor
        assign monbus_valid     = 1'b0;
        assign monbus_packet    = '0;
        assign monbus_timestamp = '0;
        assign w_mon_busy       = 1'b0;
        assign packet_count     = '0;
        assign flit_count       = '0;
        assign error_count      = '0;
        assign dropped_count    = '0;
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_mon_busy;
    assign unused_mon_busy = w_mon_busy;
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : cxs_master_monlite
