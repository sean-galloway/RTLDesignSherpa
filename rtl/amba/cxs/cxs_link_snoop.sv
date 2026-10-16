// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_link_snoop
// Purpose: Passive model of one CXS link from its wires alone: credits in
//          flight, link state and the credit/link protocol checks
//
// Documentation: docs/markdown/rtl-amba/cxs/README.md
// Subsystem: amba
//
// Every port is an input but the outputs: this block watches a link it is
// not an endpoint of and drives nothing onto it
// (vault/handbook/design/observers-do-not-drive.md). It gives an observer
// what an endpoint gives its own monitor:
//
//   credits      grants not yet spent by a flit or returned (the credits the
//                transmitter holds, seen from the wire)
//   link_state   {CXSACTIVEREQ, CXSACTIVEACK}: 00 STOP, 10 ACTIVATE, 11 RUN,
//                01 DEACTIVATE
//   run_no_credit  RUN with no credit held: the receiver is throttling, a
//                flit cannot be sent. A passive tap cannot see whether the
//                transmitter WANTS to send, so this is the observable half
//                of credit starvation
//   protocol_error (sticky until clear) any of:
//                - CXSVALID with no credit held (2.1.2)
//                - CXSCRDRTN with no credit held
//                - CXSVALID and CXSCRDRTN in the same cycle
//                - a grant past CXS_MAX_CREDIT
//                - CXSCNTL malformed or a packet framed illegally for its
//                  stream (cxs_cntl_track, per-stream key as the endpoints)
//
// A grant is usable the cycle after it arrives, so a flit or a return in the
// grant's own cycle spends a credit that was already held.
//
// Parameters:
//   - CXS_DATA_WIDTH / CXS_MAX_PKT_PER_FLIT / CXS_START_ALIGN: CXSCNTL layout
//   - CXS_SRCID_WIDTH / CXS_TGTID_WIDTH: the ID ports (0 = absent)
//   - CXS_MAX_CREDIT: the link's credit limit (beyond 63 is legal here: the
//     snoop only checks what the link was built with)
//   - CXS_STREAM_*_BITS: per-stream framing key (cxs_stream_key)
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_link_snoop
    import cxs_pkg::*;
#(
    parameter int CXS_DATA_WIDTH        = 256,
    parameter int CXS_MAX_PKT_PER_FLIT  = 2,
    parameter int CXS_START_ALIGN       = 16,
    parameter int CXS_SRCID_WIDTH       = 0,
    parameter int CXS_TGTID_WIDTH       = 0,
    parameter int CXS_MAX_CREDIT        = 15,
    parameter int CXS_STREAM_PRCL_BITS  = 0,
    parameter int CXS_STREAM_SRCID_BITS = 0,
    parameter int CXS_STREAM_TGTID_BITS = 0,
    // Short and calculated params
    parameter int N        = CXS_MAX_PKT_PER_FLIT,
    parameter int CNTL_W   = cntl_width(N, CXS_DATA_WIDTH, CXS_START_ALIGN),
    parameter int CNTL_PW  = port_w(CNTL_W),
    parameter int SRCID_PW = port_w(CXS_SRCID_WIDTH),
    parameter int TGTID_PW = port_w(CXS_TGTID_WIDTH),
    parameter int CRW      = $clog2(CXS_MAX_CREDIT + 2)    // one spare: room to see an overflow
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: drop the sticky error

    // The observed link (all inputs)
    input  logic                  cxs_valid,
    input  logic [CNTL_PW-1:0]    cxs_cntl,
    input  logic [2:0]            cxs_prcltype,
    input  logic [SRCID_PW-1:0]   cxs_srcid,
    input  logic [TGTID_PW-1:0]   cxs_tgtid,
    input  logic                  cxs_crdgnt,
    input  logic                  cxs_crdrtn,
    input  logic                  cxs_activereq,
    input  logic                  cxs_activeack,

    output logic [CRW-1:0]        credits,
    output logic [1:0]            link_state,
    output logic                  run_no_credit,
    output logic                  in_packet,      // some stream has a packet open
    output logic                  protocol_error  // sticky
);

    logic [CRW-1:0] r_credits;
    logic           r_err;
    logic           w_spend, w_spend_err, w_rtn_err, w_both_err, w_ovf_err, w_cntl_err;

    assign w_spend     = cxs_valid || cxs_crdrtn;
    assign w_spend_err = cxs_valid  && (r_credits == '0);
    assign w_rtn_err   = cxs_crdrtn && (r_credits == '0);
    assign w_both_err  = cxs_valid  && cxs_crdrtn;
    assign w_ovf_err   = cxs_crdgnt && !w_spend && (r_credits >= CRW'(CXS_MAX_CREDIT));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_credits <= '0;
        end else begin
            // a spend with nothing held is an error above, not a wrap here
            r_credits <= r_credits + CRW'(cxs_crdgnt)
                       - CRW'(cxs_valid  && (r_credits != '0))
                       - CRW'(cxs_crdrtn && (r_credits != '0) && !cxs_valid);
        end
    )

    // Per-stream packet framing, keyed like the endpoints
    localparam int SKEY_W  = CXS_STREAM_PRCL_BITS + CXS_STREAM_SRCID_BITS + CXS_STREAM_TGTID_BITS;
    localparam int SKEY_PW = (SKEY_W > 0) ? SKEY_W : 1;
    logic [SKEY_PW-1:0] w_key;

    cxs_stream_key #(
        .PRCL_BITS  (CXS_STREAM_PRCL_BITS),
        .SRCID_BITS (CXS_STREAM_SRCID_BITS),
        .TGTID_BITS (CXS_STREAM_TGTID_BITS),
        .SRCID_PW   (SRCID_PW),
        .TGTID_PW   (TGTID_PW)
    ) u_stream_key (
        .i_prcltype (cxs_prcltype),
        .i_srcid    (cxs_srcid),
        .i_tgtid    (cxs_tgtid),
        .o_key      (w_key)
    );

    cxs_cntl_track #(
        .N            (N),
        .CNTL_W       (CNTL_W),
        .END_LSB      (end_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN)),
        .ENDERROR_LSB (enderror_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN)),
        .KEY_W        (SKEY_W)
    ) u_track (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .i_valid     (cxs_valid),
        .i_cntl      (cxs_cntl),
        .i_key       (w_key),
        .o_in_packet (in_packet),
        .o_cntl_err  (w_cntl_err)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_err <= 1'b0;
        else if (clear)                  r_err <= 1'b0;
        else if (w_spend_err || w_rtn_err || w_both_err || w_ovf_err || w_cntl_err)
                                         r_err <= 1'b1;
    )

    assign credits        = r_credits;
    assign link_state     = {cxs_activereq, cxs_activeack};
    assign run_no_credit  = cxs_activereq && cxs_activeack && (r_credits == '0);
    assign protocol_error = r_err;

endmodule : cxs_link_snoop
