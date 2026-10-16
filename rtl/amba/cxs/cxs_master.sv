// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_master
// Purpose: CXS Transmitter endpoint (Arm IHI 0079, Issues A-D): FUB-side
//          valid/ready flits in, a credited CXS link out
//
// Documentation: docs/markdown/rtl-amba/cxs/cxs_master.md
// Subsystem: amba
//
// The CXS counterpart of axis4_master: a skid buffer between a valid/ready
// FUB port and the link. CXS has no READY -- a flit is sent by spending a
// credit -- so the skid drains one flit per cycle whenever a credit is held
// and the link is in RUN.
//
// Credits (IHI 0079D 2.1.2):
//   - r_credits counts credits held. CXSCRDGNT adds one per cycle; a flit
//     (CXSVALID) or a return (CXSCRDRTN) spends one. Gain and spend in the
//     same cycle leave the count unchanged.
//   - A credit is usable the cycle AFTER its grant: CXSVALID is decoded from
//     r_credits, never from CXSCRDGNT, so there is no CXSCRDGNT -> CXSVALID
//     path. No output depends combinationally on any input (2.1.1).
//
// Link control, CXS_LINK_CTRL = 1 (CXSLINKCONTROL = Explicit_Credit_Return,
// chapter 5). The state is the {CXSACTIVEREQ, CXSACTIVEACK} pair, not an
// FSM: STOP 00, ACTIVATE 10, RUN 11, DEACTIVATE 01. ACTIVEACK is sampled
// into r_ack_q and treated as synchronous, which 5.5 permits a transmitter.
//   - STOP -> ACTIVATE when there is a flit to send (or cfg_link_hold) and
//     cfg_link_enable is set.
//   - Flits go only in RUN (ACTIVEREQ and the registered ACTIVEACK both high);
//     credits that arrive in ACTIVATE (the 5.4 race) are kept.
//   - RUN -> DEACTIVATE when the link is idle: the skid is empty, no packet
//     is open (cxs_cntl_track -- never deactivate mid-packet, 6.1), and one
//     of cfg_link_enable low, CXSDEACTHINT high, or cfg_idle_cycles idle
//     cycles have passed (0 = never on idleness alone).
//   - While ACTIVEREQ is low every held credit is returned on CXSCRDRTN, one
//     per cycle, including late grants. CXSCRDRTN and CXSVALID are therefore
//     never high together (VALID needs ACTIVEREQ).
//   - ACTIVEREQ rises again only after ACTIVEACK has fallen (4-phase).
// With CXS_LINK_CTRL = 0 the link is always in RUN and CXSCRDRTN /
// CXSACTIVEREQ are tied low.
//
// Interface protection, CXS_CHECK = 1 (CXSCHECKTYPE = Odd_Byte_Parity,
// 3.2): the payload check signals are GENERATED here from the outgoing flit
// (protection starts at the interface), as are CXSVALIDCHK, CXSCRDRTNCHK
// and CXSACTIVEREQCHK. CXSCRDGNTCHK and CXSACTIVEACKCHK arrive from the
// receiver and are checked every cycle out of reset; a mismatch sets the
// sticky parity_error.
//
// Payload outputs are zero while CXSVALID is low (recommended, 2.1).
//
// Parameters:
//   - CXS_ISSUE: spec issue, cxs_pkg::CXS_ISSUE_A..D (1..4). Checked at
//     elaboration against every other property (cxs_pkg::config_error)
//   - CXS_DATA_WIDTH: CXSDATAFLITWIDTH
//   - CXS_MAX_PKT_PER_FLIT: CXSMAXPKTPERFLIT, 1..4 (1 = CXS-Lite, no CXSCNTL)
//   - CXS_START_ALIGN: CXS_START_ALIGNMENT in bytes, 16 or 4 (Issue D)
//   - CXS_HAS_LAST / CXS_HAS_PRCLTYPE: CXS_LAST / CXS_PROTOCOL_TYPE (Issue B+)
//   - CXS_SRCID_WIDTH / CXS_TGTID_WIDTH / CXS_USER_WIDTH: Issue D, 0 = absent
//   - CXS_MAX_CREDIT: credits this transmitter can track (15 or 63 max)
//   - CXS_LINK_CTRL: 1 = Explicit_Credit_Return, 0 = None
//   - CXS_CHECK: 1 = Odd_Byte_Parity, 0 = None
//   - SKID_DEPTH: FUB skid buffer depth, 2..8
// Notes:
//   - An absent optional signal keeps a one-bit port, tied low on output and
//     ignored on input, as the axis4/axis5 endpoints do.
//   - The FUB supplies CXSCNTL as-is; this block tracks it, it does not
//     build packets.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_master
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
    // Credit pool beyond the spec's CXS_MAX_CREDIT cap (63, or 15 before
    // Issue C): the one sanctioned departure, for a receiver whose buffer is
    // a whole SRAM. Both ends of the link must be built with it.
    parameter bit CXS_CREDIT_BEYOND_SPEC = 1'b0,
    // Per-stream packet tracking (IHI 0079D 2.5.2): the low bits of
    // CXSPRCLTYPE / CXSSRCID / CXSTGTID that tell interleaved streams apart.
    // 0/0/0 = the link is one stream (no interleave). See cxs_stream_key.
    parameter int CXS_STREAM_PRCL_BITS  = 0,
    parameter int CXS_STREAM_SRCID_BITS = 0,
    parameter int CXS_STREAM_TGTID_BITS = 0,
    parameter bit CXS_LINK_CTRL        = 1'b1,
    parameter bit CXS_CHECK            = 1'b0,
    parameter int SKID_DEPTH           = 4,

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
    // Global Clock and Reset
    input  logic                  aclk,
    input  logic                  aresetn,

    // Configuration
    input  logic                  cfg_link_enable,   // 0 = take the link down when idle, never raise it
    input  logic                  cfg_link_hold,     // 1 = keep the link in RUN with nothing to send
    input  logic [7:0]            cfg_idle_cycles,   // idle RUN cycles before deactivating; 0 = never

    // FUB side (valid/ready flits in)
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

    // CXS check signals (CXS_CHECK = 1)
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
    output logic                  busy,              // any work or link state that is not STOP
    output logic [CRW-1:0]        credits,           // credits held
    output logic [1:0]            link_state,        // {ACTIVEREQ, ACTIVEACK sampled}: 00 STOP 10 ACTIVATE 11 RUN 01 DEACTIVATE
    output logic                  in_packet,         // a packet is open on the link
    output logic                  credit_starved,    // a flit is waiting in RUN with no credit to send it
    output logic                  protocol_error,    // sticky: credit overflow, ACK without REQ, bad CXSCNTL from the FUB
    output logic                  parity_error       // sticky: CXSCRDGNTCHK / CXSACTIVEACKCHK mismatch
);

    // ------------------------------------------------------------------
    // Elaboration-time property check (the one sanctioned guard form)
    // ------------------------------------------------------------------
    localparam int CFG_ERR = config_error(CXS_ISSUE, DW, N, CXS_START_ALIGN,
                                          CXS_HAS_LAST, CXS_HAS_PRCLTYPE,
                                          CXS_SRCID_WIDTH, CXS_TGTID_WIDTH,
                                          CXS_USER_WIDTH, CXS_MAX_CREDIT,
                                          CXS_CREDIT_BEYOND_SPEC);
`ifndef SYNTHESIS
    initial begin : param_check
        if (CFG_ERR != 0)
            $fatal(1, "cxs_master: illegal CXS property set for issue %0d (rule %0d, see cxs_pkg::config_error)",
                   CXS_ISSUE, CFG_ERR);
    end
`endif

    // ------------------------------------------------------------------
    // Skid buffer: {data, cntl, last, prcltype, srcid, tgtid, user}
    // ------------------------------------------------------------------
    localparam int PKT_W = DW + CNTL_PW + 1 + 3 + SRCID_PW + TGTID_PW + USER_PW;

    logic [PKT_W-1:0] w_skid_pkt;
    logic [3:0]       w_skid_count;
    logic             w_skid_valid;
    logic             w_send;
    logic             w_rtn;

    gaxi_skid_buffer #(
        .DEPTH      (SKID_DEPTH),
        .DATA_WIDTH (PKT_W)
    ) u_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_cxs_valid),
        .wr_ready    (fub_cxs_ready),
        .wr_data     ({fub_cxs_data, fub_cxs_cntl, fub_cxs_last, fub_cxs_prcltype,
                       fub_cxs_srcid, fub_cxs_tgtid, fub_cxs_user}),
        .rd_valid    (w_skid_valid),
        .rd_ready    (w_send),
        .rd_count    (w_skid_count),
        .rd_data     (w_skid_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    logic [DW-1:0]       w_data;
    logic [CNTL_PW-1:0]  w_cntl;
    logic                w_last;
    logic [2:0]          w_prcltype;
    logic [SRCID_PW-1:0] w_srcid;
    logic [TGTID_PW-1:0] w_tgtid;
    logic [USER_PW-1:0]  w_user;

    assign {w_data, w_cntl, w_last, w_prcltype, w_srcid, w_tgtid, w_user} = w_skid_pkt;

    // ------------------------------------------------------------------
    // Link control
    // ------------------------------------------------------------------
    logic [CRW-1:0] r_credits;
    logic       r_activereq;
    logic       r_ack_q;
    logic       r_hint_q;
    logic [7:0] r_idle_cnt;
    logic       w_run;
    logic       w_want;
    logic       w_idle_expired;
    logic       w_raise;
    logic       w_drop;
    logic       w_in_packet;
    logic       w_cntl_err;

    assign w_want = fub_cxs_valid || w_skid_valid || cfg_link_hold;

    if (CXS_LINK_CTRL) begin : g_link
        assign w_run          = r_activereq && r_ack_q;
        assign w_idle_expired = (cfg_idle_cycles != 8'd0) && (r_idle_cnt >= cfg_idle_cycles);
        assign w_raise        = !r_activereq && !r_ack_q && cfg_link_enable && w_want;
        assign w_drop         = w_run && !w_skid_valid && !w_in_packet &&
                                (!cfg_link_enable || (r_hint_q && !w_want) ||
                                 (w_idle_expired && !w_want));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_activereq <= 1'b0;
                r_ack_q     <= 1'b0;
                r_hint_q    <= 1'b0;
                r_idle_cnt  <= 8'd0;
            end else begin
                r_ack_q  <= m_cxs_activeack;
                r_hint_q <= m_cxs_deacthint;
                if (w_raise)
                    r_activereq <= 1'b1;
                else if (w_drop)
                    r_activereq <= 1'b0;
                if (!w_run || w_want)
                    r_idle_cnt <= 8'd0;
                else if (r_idle_cnt != 8'hFF)
                    r_idle_cnt <= r_idle_cnt + 8'd1;
            end
        )

        // Every credit held while ACTIVEREQ is low goes back (DEACTIVATE,
        // and any late grant). Needs ACTIVEREQ low, so never with VALID.
        assign w_rtn = !r_activereq && (r_credits != '0);
    end else begin : g_no_link
        assign w_run          = 1'b1;
        assign w_idle_expired = 1'b0;
        assign w_raise        = 1'b0;
        assign w_drop         = 1'b0;
        assign w_rtn          = 1'b0;

        always_comb begin
            r_activereq = 1'b0;
            r_ack_q     = 1'b0;
            r_hint_q    = 1'b0;
            r_idle_cnt  = 8'd0;
        end

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_link;
        assign unused_link = ^{cfg_link_enable, cfg_idle_cycles, m_cxs_activeack,
                               m_cxs_deacthint, w_want, w_idle_expired, w_raise, w_drop,
                               r_hint_q, r_idle_cnt};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    // ------------------------------------------------------------------
    // Credits
    // ------------------------------------------------------------------
    logic           w_credit_ovf;

    assign w_send       = w_skid_valid && w_run && (r_credits != '0);
    assign w_credit_ovf = m_cxs_crdgnt && !w_send && !w_rtn &&
                          (r_credits == CRW'(CXS_MAX_CREDIT));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_credits <= '0;
        end else if (!w_credit_ovf) begin
            r_credits <= r_credits + CRW'(m_cxs_crdgnt) - CRW'(w_send) - CRW'(w_rtn);
        end
    )

    // ------------------------------------------------------------------
    // Packet tracking on the flits actually sent
    // ------------------------------------------------------------------
    localparam int SKEY_W  = CXS_STREAM_PRCL_BITS + CXS_STREAM_SRCID_BITS + CXS_STREAM_TGTID_BITS;
    localparam int SKEY_PW = (SKEY_W > 0) ? SKEY_W : 1;
    logic [SKEY_PW-1:0] w_stream_key;

    cxs_stream_key #(
        .PRCL_BITS  (CXS_STREAM_PRCL_BITS),
        .SRCID_BITS (CXS_STREAM_SRCID_BITS),
        .TGTID_BITS (CXS_STREAM_TGTID_BITS),
        .SRCID_PW   (SRCID_PW),
        .TGTID_PW   (TGTID_PW)
    ) u_stream_key (
        .i_prcltype (w_prcltype),
        .i_srcid    (w_srcid),
        .i_tgtid    (w_tgtid),
        .o_key      (w_stream_key)
    );

    cxs_cntl_track #(
        .N            (N),
        .CNTL_W       (CNTL_W),
        .END_LSB      (end_lsb(N, DW, CXS_START_ALIGN)),
        .ENDERROR_LSB (enderror_lsb(N, DW, CXS_START_ALIGN)),
        .KEY_W        (SKEY_W)
    ) u_track (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .i_valid     (w_send),
        .i_cntl      (w_cntl),
        .i_key       (w_stream_key),
        .o_in_packet (w_in_packet),
        .o_cntl_err  (w_cntl_err)
    );

    // ------------------------------------------------------------------
    // Outputs: payload zero while VALID is low; absent fields tied low
    // ------------------------------------------------------------------
    assign m_cxs_valid     = w_send;
    assign m_cxs_data      = w_send ? w_data : '0;
    assign m_cxs_cntl      = (w_send && CNTL_W > 0) ? w_cntl : '0;
    assign m_cxs_last      = w_send && CXS_HAS_LAST && w_last;
    assign m_cxs_prcltype  = (w_send && CXS_HAS_PRCLTYPE) ? w_prcltype : 3'b000;
    assign m_cxs_srcid     = (w_send && CXS_SRCID_WIDTH > 0) ? w_srcid : '0;
    assign m_cxs_tgtid     = (w_send && CXS_TGTID_WIDTH > 0) ? w_tgtid : '0;
    assign m_cxs_user      = (w_send && CXS_USER_WIDTH > 0) ? w_user : '0;
    assign m_cxs_crdrtn    = w_rtn;
    assign m_cxs_activereq = r_activereq;

    assign busy       = fub_cxs_valid || (w_skid_count != 4'd0) || r_activereq || r_ack_q ||
                        (r_credits != '0);
    assign credits    = r_credits;
    assign link_state = {r_activereq, r_ack_q};
    assign in_packet  = w_in_packet;
    assign credit_starved = w_skid_valid && w_run && (r_credits == '0);

    // ------------------------------------------------------------------
    // Protocol errors (sticky)
    // ------------------------------------------------------------------
    logic w_proto_err;
    assign w_proto_err = w_credit_ovf || w_cntl_err ||
                         (CXS_LINK_CTRL && m_cxs_activeack && !r_activereq && !r_ack_q);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            protocol_error <= 1'b0;
        end else if (w_proto_err) begin
            protocol_error <= 1'b1;
        end
    )

    // ------------------------------------------------------------------
    // Interface protection (Odd_Byte_Parity)
    // ------------------------------------------------------------------
    if (CXS_CHECK) begin : g_check
        logic [CNTLCHK_W-1:0] w_cntlchk;
        logic [USERCHK_W-1:0] w_userchk;

        /* verilator lint_off PINCONNECTEMPTY */
        cxs_odd_byte_parity #(.WIDTH(DW)) u_datachk (
            .data (m_cxs_data), .chk_in ('0), .chk_out (m_cxs_datachk), .chk_err ());
        cxs_odd_byte_parity #(.WIDTH(CNTL_PW)) u_cntlchk (
            .data (m_cxs_cntl), .chk_in ('0), .chk_out (w_cntlchk), .chk_err ());
        cxs_odd_byte_parity #(.WIDTH(3)) u_prcltypechk (
            .data (m_cxs_prcltype), .chk_in ('0), .chk_out (m_cxs_prcltypechk), .chk_err ());
        cxs_odd_byte_parity #(.WIDTH(SRCID_PW)) u_srcidchk (
            .data (m_cxs_srcid), .chk_in ('0), .chk_out (m_cxs_srcidchk), .chk_err ());
        cxs_odd_byte_parity #(.WIDTH(TGTID_PW)) u_tgtidchk (
            .data (m_cxs_tgtid), .chk_in ('0), .chk_out (m_cxs_tgtidchk), .chk_err ());
        cxs_odd_byte_parity #(.WIDTH(USER_PW)) u_userchk (
            .data (m_cxs_user), .chk_in ('0), .chk_out (w_userchk), .chk_err ());
        /* verilator lint_on PINCONNECTEMPTY */

        assign m_cxs_cntlchk      = (CNTL_W > 0) ? w_cntlchk : '0;
        assign m_cxs_userchk      = (CXS_USER_WIDTH > 0) ? w_userchk : '0;
        assign m_cxs_lastchk      = ~m_cxs_last;
        assign m_cxs_validchk     = ~m_cxs_valid;
        assign m_cxs_crdrtnchk    = ~m_cxs_crdrtn;
        assign m_cxs_activereqchk = ~m_cxs_activereq;

        // Receiver-driven single-bit checks, enabled every cycle out of
        // reset (Check enable = RESETn, Table 3-2)
        logic w_ctrl_err;
        assign w_ctrl_err = (m_cxs_crdgntchk == m_cxs_crdgnt) ||
                            (CXS_LINK_CTRL && (m_cxs_activeackchk == m_cxs_activeack));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                parity_error <= 1'b0;
            end else if (w_ctrl_err) begin
                parity_error <= 1'b1;
            end
        )
    end else begin : g_no_check
        assign m_cxs_validchk     = 1'b0;
        assign m_cxs_datachk      = '0;
        assign m_cxs_cntlchk      = '0;
        assign m_cxs_lastchk      = 1'b0;
        assign m_cxs_prcltypechk  = 1'b0;
        assign m_cxs_srcidchk     = 1'b0;
        assign m_cxs_tgtidchk     = 1'b0;
        assign m_cxs_userchk      = '0;
        assign m_cxs_crdrtnchk    = 1'b0;
        assign m_cxs_activereqchk = 1'b0;
        assign parity_error       = 1'b0;

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_chk_inputs;
        assign unused_chk_inputs = ^{m_cxs_crdgntchk, m_cxs_activeackchk};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_fields;
    assign unused_fields = ^{w_last, w_prcltype, w_srcid, w_tgtid, w_user, w_cntl};
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : cxs_master
