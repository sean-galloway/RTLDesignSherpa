// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_slave
// Purpose: CXS Receiver endpoint (Arm IHI 0079, Issues A-D): a credited CXS
//          link in, FUB-side valid/ready flits out
//
// Documentation: docs/markdown/rtl-amba/cxs/cxs_slave.md
// Subsystem: amba
//
// The CXS counterpart of axis4_slave. Every credit is a promise of one FIFO
// slot (IHI 0079D 2.1.2: "the Receiver must guarantee that it can receive
// one flit of data for each credit that it grants"), so the receive FIFO is
// the credit pool:
//
//   r_out    credits granted and not yet spent (CXSVALID) or returned
//            (CXSCRDRTN), counting the grant on the wire this cycle
//   grant    another credit when, after this edge,
//              FIFO occupancy + r_out < RX_FIFO_DEPTH  and  r_out < CXS_MAX_CREDIT
//
// CXSCRDGNT is registered (r_crdgnt) from registered state and this cycle's
// VALID / CRDRTN / FUB pop, so a credit spent or returned in cycle t is
// granted again at t+1 at the earliest -- the reuse rule of 2.1.2 -- and no
// output depends combinationally on any input.
//
// Link control, CXS_LINK_CTRL = 1 (chapter 5). CXSACTIVEREQ "must be treated
// by the Receiver as an asynchronous signal" (5.5): it crosses through
// glitch_free_n_dff_arn (ACTIVEREQ_SYNC_STAGES flops, with its check bit) --
// 0 stages is allowed for a known-synchronous system.
//   - ACTIVATE -> RUN: raise CXSACTIVEACK when ACTIVEREQ is seen and
//     cfg_rx_enable is set. Credits are granted only in RUN.
//   - DEACTIVATE: stop granting; flits still in flight are accepted (5.4);
//     drop ACTIVEACK only when every credit is home (r_out reaches 0), so the
//     transmitter never sees ACK low while it holds a credit.
//   - CXSDEACTHINT is cfg_deact_hint, registered.
// With CXS_LINK_CTRL = 0 credits are granted whenever there is room and
// cfg_rx_enable is set, and CXSACTIVEACK / CXSDEACTHINT are tied low.
//
// Interface protection, CXS_CHECK = 1 (3.2): payload check signals are
// checked when CXSVALID is high, for the signals the interface has;
// CXSVALIDCHK, CXSCRDRTNCHK and CXSACTIVEREQCHK every cycle out of reset
// (ACTIVEREQCHK after the same synchronizer as ACTIVEREQ). A mismatch sets
// the sticky parity_error. CXSCRDGNTCHK and CXSACTIVEACKCHK are generated.
//
// Parameters: as cxs_master, plus
//   - RX_FIFO_DEPTH: receive FIFO depth = the credit pool; default
//     CXS_MAX_CREDIT. A depth below the credit round trip throttles the link
//     (2.1.2: the credit count must cover the credit latency for full rate)
//   - ACTIVEREQ_SYNC_STAGES: synchronizer flops on CXSACTIVEREQ, 0 or >= 2
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_slave
    import cxs_pkg::*;
#(
    parameter int CXS_ISSUE             = CXS_ISSUE_D,
    parameter int CXS_DATA_WIDTH        = 256,
    parameter int CXS_MAX_PKT_PER_FLIT  = 2,
    parameter int CXS_START_ALIGN       = 16,
    parameter bit CXS_HAS_LAST          = 1'b0,
    parameter bit CXS_HAS_PRCLTYPE      = 1'b0,
    parameter int CXS_SRCID_WIDTH       = 0,
    parameter int CXS_TGTID_WIDTH       = 0,
    parameter int CXS_USER_WIDTH        = 0,
    parameter int CXS_MAX_CREDIT        = 15,
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
    parameter bit CXS_LINK_CTRL         = 1'b1,
    parameter bit CXS_CHECK             = 1'b0,
    parameter int RX_FIFO_DEPTH         = CXS_MAX_CREDIT,
    parameter int ACTIVEREQ_SYNC_STAGES = 2,

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
    input  logic                  cfg_rx_enable,     // 0 = never activate, never grant
    input  logic                  cfg_deact_hint,    // drives CXSDEACTHINT (registered)

    // CXS Receiver interface
    input  logic                  s_cxs_valid,
    input  logic [DW-1:0]         s_cxs_data,
    input  logic [CNTL_PW-1:0]    s_cxs_cntl,
    input  logic                  s_cxs_last,
    input  logic [2:0]            s_cxs_prcltype,
    input  logic [SRCID_PW-1:0]   s_cxs_srcid,
    input  logic [TGTID_PW-1:0]   s_cxs_tgtid,
    input  logic [USER_PW-1:0]    s_cxs_user,
    output logic                  s_cxs_crdgnt,
    input  logic                  s_cxs_crdrtn,
    input  logic                  s_cxs_activereq,
    output logic                  s_cxs_activeack,
    output logic                  s_cxs_deacthint,

    // CXS check signals (CXS_CHECK = 1)
    input  logic                  s_cxs_validchk,
    input  logic [DATACHK_W-1:0]  s_cxs_datachk,
    input  logic [CNTLCHK_W-1:0]  s_cxs_cntlchk,
    input  logic                  s_cxs_lastchk,
    input  logic                  s_cxs_prcltypechk,
    input  logic                  s_cxs_srcidchk,
    input  logic                  s_cxs_tgtidchk,
    input  logic [USERCHK_W-1:0]  s_cxs_userchk,
    output logic                  s_cxs_crdgntchk,
    input  logic                  s_cxs_crdrtnchk,
    input  logic                  s_cxs_activereqchk,
    output logic                  s_cxs_activeackchk,

    // FUB side (valid/ready flits out)
    output logic                  fub_cxs_valid,
    input  logic                  fub_cxs_ready,
    output logic [DW-1:0]         fub_cxs_data,
    output logic [CNTL_PW-1:0]    fub_cxs_cntl,
    output logic                  fub_cxs_last,
    output logic [2:0]            fub_cxs_prcltype,
    output logic [SRCID_PW-1:0]   fub_cxs_srcid,
    output logic [TGTID_PW-1:0]   fub_cxs_tgtid,
    output logic [USER_PW-1:0]    fub_cxs_user,

    // Status
    output logic                  busy,                // any work or link state that is not STOP
    output logic [CRW-1:0]        credits_outstanding, // granted, not yet spent or returned
    output logic [1:0]            link_state,          // {ACTIVEREQ synced, ACTIVEACK}
    output logic                  in_packet,           // a packet is open on the link
    output logic                  credit_starved,      // RUN, no credit out and none grantable: the FIFO holds every slot (the FUB is the bottleneck)
    output logic                  protocol_error,      // sticky: flit/return without a credit, VALID with CRDRTN, bad CXSCNTL, overflow
    output logic                  parity_error         // sticky: a received check signal mismatched
);

    // ------------------------------------------------------------------
    // Elaboration-time property check
    // ------------------------------------------------------------------
    localparam int CFG_ERR = config_error(CXS_ISSUE, DW, N, CXS_START_ALIGN,
                                          CXS_HAS_LAST, CXS_HAS_PRCLTYPE,
                                          CXS_SRCID_WIDTH, CXS_TGTID_WIDTH,
                                          CXS_USER_WIDTH, CXS_MAX_CREDIT,
                                          CXS_CREDIT_BEYOND_SPEC);
`ifndef SYNTHESIS
    initial begin : param_check
        if (CFG_ERR != 0)
            $fatal(1, "cxs_slave: illegal CXS property set for issue %0d (rule %0d, see cxs_pkg::config_error)",
                   CXS_ISSUE, CFG_ERR);
        if (RX_FIFO_DEPTH < 1)
            $fatal(1, "cxs_slave: RX_FIFO_DEPTH must be >= 1 (got %0d)", RX_FIFO_DEPTH);
        if (ACTIVEREQ_SYNC_STAGES == 1)
            $fatal(1, "cxs_slave: ACTIVEREQ_SYNC_STAGES is 0 (synchronous) or >= 2");
    end
`endif

    localparam int PKT_W = DW + CNTL_PW + 1 + 3 + SRCID_PW + TGTID_PW + USER_PW;
    // gaxi_fifo_sync needs DEPTH >= 2 (its counters go zero-width at 1), but
    // one credit with a one-flit buffer is a legal CXS receiver
    // (CXS_MAX_CREDIT = 1). The FIFO is built at least 2 deep; the credit
    // accounting below still uses RX_FIFO_DEPTH, so the spare slot is never
    // granted against.
    localparam int FIFO_D = (RX_FIFO_DEPTH < 2) ? 2 : RX_FIFO_DEPTH;
    localparam int AW     = $clog2(FIFO_D);
    localparam int OW    = ((AW + 1) > (CRW + 1)) ? (AW + 2) : (CRW + 2);   // sum width, no wrap

    // ------------------------------------------------------------------
    // Received fields: absent signals read as 0
    // ------------------------------------------------------------------
    logic [CNTL_PW-1:0]  w_cntl;
    logic                w_last;
    logic [2:0]          w_prcltype;
    logic [SRCID_PW-1:0] w_srcid;
    logic [TGTID_PW-1:0] w_tgtid;
    logic [USER_PW-1:0]  w_user;

    assign w_cntl     = (CNTL_W > 0)          ? s_cxs_cntl     : '0;
    assign w_last     = CXS_HAS_LAST          && s_cxs_last;
    assign w_prcltype = CXS_HAS_PRCLTYPE      ? s_cxs_prcltype : 3'b000;
    assign w_srcid    = (CXS_SRCID_WIDTH > 0) ? s_cxs_srcid    : '0;
    assign w_tgtid    = (CXS_TGTID_WIDTH > 0) ? s_cxs_tgtid    : '0;
    assign w_user     = (CXS_USER_WIDTH > 0)  ? s_cxs_user     : '0;

    // ------------------------------------------------------------------
    // Receive FIFO (the credit pool)
    // ------------------------------------------------------------------
    logic [AW:0]      w_fifo_count;
    logic             w_fifo_wr_ready;
    logic [PKT_W-1:0] w_fifo_rd_data;
    logic             w_push;
    logic             w_pop;

    assign w_push = s_cxs_valid;
    assign w_pop  = fub_cxs_valid && fub_cxs_ready;

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (PKT_W),
        .DEPTH      (FIFO_D)
    ) u_rx_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_push),
        .wr_ready    (w_fifo_wr_ready),
        .wr_data     ({s_cxs_data, w_cntl, w_last, w_prcltype, w_srcid, w_tgtid, w_user}),
        .rd_ready    (fub_cxs_ready),
        .count       (w_fifo_count),
        .rd_valid    (fub_cxs_valid),
        .rd_data     (w_fifo_rd_data)
    );

    assign {fub_cxs_data, fub_cxs_cntl, fub_cxs_last, fub_cxs_prcltype,
            fub_cxs_srcid, fub_cxs_tgtid, fub_cxs_user} = w_fifo_rd_data;

    // ------------------------------------------------------------------
    // Link control
    // ------------------------------------------------------------------
    logic w_req_s;       // CXSACTIVEREQ in this clock domain
    logic w_reqchk_s;    // CXSACTIVEREQCHK, same crossing
    logic r_ack;
    logic r_hint;
    logic w_grant_ok;

    logic [CRW-1:0] r_out;
    logic           r_crdgnt;
    logic [OW-1:0]  w_out_next;
    logic [OW-1:0]  w_occ_next;
    logic           w_can_grant;

    if (CXS_LINK_CTRL) begin : g_link
        if (ACTIVEREQ_SYNC_STAGES >= 2) begin : g_sync
            // The check bit crosses INVERTED: the flops reset to 0, and a
            // reset-low ACTIVEREQ's correct check is 1. Carried true, the
            // pair would read {0,0} -- a parity error -- for every cycle the
            // synchronizer is still flushing after reset.
            logic w_reqchk_n_s;
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (ACTIVEREQ_SYNC_STAGES),
                .WIDTH      (2)
            ) u_req_sync (
                .clk   (aclk),
                .rst_n (aresetn),
                .d     ({s_cxs_activereq, ~s_cxs_activereqchk}),
                .q     ({w_req_s, w_reqchk_n_s})
            );
            assign w_reqchk_s = ~w_reqchk_n_s;
        end else begin : g_nosync
            assign w_req_s    = s_cxs_activereq;
            assign w_reqchk_s = s_cxs_activereqchk;
        end

        assign w_grant_ok = w_req_s && r_ack;

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_ack  <= 1'b0;
                r_hint <= 1'b0;
            end else begin
                r_hint <= cfg_deact_hint;
                if (w_req_s && !r_ack && cfg_rx_enable)
                    r_ack <= 1'b1;                       // ACTIVATE -> RUN
                else if (!w_req_s && r_ack && (w_out_next == '0))
                    r_ack <= 1'b0;                       // DEACTIVATE -> STOP, all credits home
            end
        )
    end else begin : g_no_link
        assign w_req_s    = 1'b0;
        assign w_reqchk_s = 1'b1;
        assign w_grant_ok = cfg_rx_enable;

        always_comb begin
            r_ack  = 1'b0;
            r_hint = 1'b0;
        end

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_link;
        assign unused_link = ^{s_cxs_activereq, s_cxs_activereqchk, cfg_deact_hint};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    // ------------------------------------------------------------------
    // Credits
    // ------------------------------------------------------------------
    // After this edge, before any new grant: the grant on the wire now has
    // joined r_out, a flit or a return has left it, and the FIFO has taken
    // the push and given up the pop.
    assign w_out_next = OW'(r_out) + OW'(r_crdgnt) - OW'(w_push) - OW'(s_cxs_crdrtn);
    assign w_occ_next = OW'(w_fifo_count) + OW'(w_push) - OW'(w_pop);

    // Underflow (a flit or return with no credit) wraps w_out_next high,
    // which also blocks a grant until reset; it is flagged below.
    assign w_can_grant = w_grant_ok &&
                         (w_out_next < OW'(CXS_MAX_CREDIT)) &&
                         ((w_occ_next + w_out_next) < OW'(RX_FIFO_DEPTH));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_out    <= '0;
            r_crdgnt <= 1'b0;
        end else begin
            r_crdgnt <= w_can_grant;
            if (w_out_next <= OW'(CXS_MAX_CREDIT))
                r_out <= CRW'(w_out_next);
        end
    )

    assign s_cxs_crdgnt    = r_crdgnt;
    assign s_cxs_activeack = r_ack;
    assign s_cxs_deacthint = r_hint;

    // ------------------------------------------------------------------
    // Packet tracking on the flits received
    // ------------------------------------------------------------------
    logic w_in_packet;
    logic w_cntl_err;

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
        .i_valid     (w_push),
        .i_cntl      (w_cntl),
        .i_key       (w_stream_key),
        .o_in_packet (w_in_packet),
        .o_cntl_err  (w_cntl_err)
    );

    // ------------------------------------------------------------------
    // Status and protocol errors
    // ------------------------------------------------------------------
    assign busy = s_cxs_valid || fub_cxs_valid || r_ack || w_req_s ||
                  (r_out != '0) || r_crdgnt;
    assign credits_outstanding = r_out;
    assign link_state          = {w_req_s, r_ack};
    assign in_packet           = w_in_packet;
    assign credit_starved      = w_grant_ok && (r_out == '0) && !r_crdgnt && !w_can_grant;

    logic w_proto_err;
    assign w_proto_err = (w_push && (r_out == '0)) ||
                         (s_cxs_crdrtn && (r_out == '0)) ||
                         (w_push && s_cxs_crdrtn) ||
                         (w_push && !w_fifo_wr_ready) ||
                         w_cntl_err;

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
        logic w_data_err, w_cntl_chk_err, w_prcl_err, w_srcid_err, w_tgtid_err, w_user_err;
        logic w_payload_err, w_ctrl_err;

        /* verilator lint_off PINCONNECTEMPTY */
        cxs_odd_byte_parity #(.WIDTH(DW)) u_datachk (
            .data (s_cxs_data), .chk_in (s_cxs_datachk), .chk_out (), .chk_err (w_data_err));
        cxs_odd_byte_parity #(.WIDTH(CNTL_PW)) u_cntlchk (
            .data (s_cxs_cntl), .chk_in (s_cxs_cntlchk), .chk_out (), .chk_err (w_cntl_chk_err));
        cxs_odd_byte_parity #(.WIDTH(3)) u_prcltypechk (
            .data (s_cxs_prcltype), .chk_in (s_cxs_prcltypechk), .chk_out (), .chk_err (w_prcl_err));
        cxs_odd_byte_parity #(.WIDTH(SRCID_PW)) u_srcidchk (
            .data (s_cxs_srcid), .chk_in (s_cxs_srcidchk), .chk_out (), .chk_err (w_srcid_err));
        cxs_odd_byte_parity #(.WIDTH(TGTID_PW)) u_tgtidchk (
            .data (s_cxs_tgtid), .chk_in (s_cxs_tgtidchk), .chk_out (), .chk_err (w_tgtid_err));
        cxs_odd_byte_parity #(.WIDTH(USER_PW)) u_userchk (
            .data (s_cxs_user), .chk_in (s_cxs_userchk), .chk_out (), .chk_err (w_user_err));
        /* verilator lint_on PINCONNECTEMPTY */

        // Payload checks: Check enable = CXSVALID, only for signals present
        assign w_payload_err = s_cxs_valid && (
            w_data_err ||
            ((CNTL_W > 0)          && w_cntl_chk_err) ||
            (CXS_HAS_LAST          && (s_cxs_lastchk == s_cxs_last)) ||
            (CXS_HAS_PRCLTYPE      && w_prcl_err) ||
            ((CXS_SRCID_WIDTH > 0) && w_srcid_err) ||
            ((CXS_TGTID_WIDTH > 0) && w_tgtid_err) ||
            ((CXS_USER_WIDTH > 0)  && w_user_err));

        // Single-bit controls: Check enable = RESETn
        assign w_ctrl_err = (s_cxs_validchk == s_cxs_valid) ||
                            (CXS_LINK_CTRL && (s_cxs_crdrtnchk == s_cxs_crdrtn)) ||
                            (CXS_LINK_CTRL && (w_reqchk_s == w_req_s));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                parity_error <= 1'b0;
            end else if (w_payload_err || w_ctrl_err) begin
                parity_error <= 1'b1;
            end
        )

        assign s_cxs_crdgntchk    = ~s_cxs_crdgnt;
        assign s_cxs_activeackchk = ~s_cxs_activeack;
    end else begin : g_no_check
        assign parity_error       = 1'b0;
        assign s_cxs_crdgntchk    = 1'b0;
        assign s_cxs_activeackchk = 1'b0;

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_chk_inputs;
        assign unused_chk_inputs = ^{s_cxs_validchk, s_cxs_datachk, s_cxs_cntlchk,
                                     s_cxs_lastchk, s_cxs_prcltypechk, s_cxs_srcidchk,
                                     s_cxs_tgtidchk, s_cxs_userchk, s_cxs_crdrtnchk,
                                     w_reqchk_s};
        /* verilator lint_on UNUSEDSIGNAL */
    end

endmodule : cxs_slave
