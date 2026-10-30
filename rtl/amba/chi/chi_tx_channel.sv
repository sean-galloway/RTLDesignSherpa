// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_tx_channel
// Purpose: One credited CHI transmit channel (REQ, RSP, DAT or SNP): FUB
//          valid/ready flits in, FLITPEND / FLITV / FLIT out against
//          L-Credits granted on LCRDV
//
// Documentation: docs/markdown/rtl-amba/chi/README.md
// Subsystem: amba
//
// The CHI counterpart of cxs_master's datapath, one per channel. CHI has no
// READY: a flit is sent by spending an L-Credit (B14.2.1.1). A skid buffer
// sits between the FUB port and the link and drains one flit per cycle
// whenever a credit is held and the link direction is in RUN.
//
// Credits (B14.2.1.1):
//   - r_credits counts credits held. LCRDV adds one per cycle; a flit
//     (FLITV) spends one. "An L-Credit cannot be used in the same cycle as
//     being received": FLITV is decoded from r_credits, never from LCRDV,
//     so a grant in cycle t is spendable in t+1 and no output depends
//     combinationally on any input.
//   - The receiver never grants more than MAX_LCREDIT; a grant beyond that
//     is a protocol error, counted and the credit dropped.
//
// FLITPEND (B14.4): "asserted exactly one cycle before a flit is sent", may
// be asserted without a credit, may be asserted and then not followed by a
// flit. FLITPEND is w_pend_next, decoded from registered state only (the
// skid's flop-based rd_valid, the registered direction state, r_credits):
// a flit could go next cycle. r_pend registers it, and FLITV in a cycle
// requires r_pend, i.e. FLITPEND high in the previous cycle. A pend that
// does not turn into a flit (the credit never came, the direction changed)
// is permitted.
//
// Link direction state comes from chi_link_tx (one pair of LINKACTIVE
// signals covers every channel of a direction, B14.5.1.3):
//   - i_run:   flits may be sent
//   - i_deact: DEACTIVATE; every held credit goes back as an LCrdReturn, a
//              Link flit with Opcode 0 and TxnID 0 (B13.11): the all-zero
//              word. Each return spends one credit like any flit. Late
//              grants are returned too.
//   - neither: STOP or ACTIVATE; nothing is sent, grants are still counted
//              (the ACTIVATE race of Table B14.2).
//
// Parameters:
//   - FLIT_W: the channel's flit width (chi_pkg::*_flit_w)
//   - MAX_LCREDIT: 1..15 (B14.2.1.1)
//   - SKID_DEPTH: FUB skid buffer depth, 2..8
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module chi_tx_channel #(
    parameter int FLIT_W      = 137,
    parameter int MAX_LCREDIT = 15,
    parameter int SKID_DEPTH  = 4,
    parameter int CRW         = $clog2(MAX_LCREDIT + 1)
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Link direction state (chi_link_tx)
    input  logic              i_run,
    input  logic              i_deact,

    // FUB side (valid/ready flits in)
    input  logic              fub_valid,
    output logic              fub_ready,
    input  logic [FLIT_W-1:0] fub_flit,

    // CHI channel (transmit)
    output logic              o_flitpend,
    output logic              o_flitv,
    output logic [FLIT_W-1:0] o_flit,
    input  logic              i_lcrdv,

    // Status
    output logic [CRW-1:0]    o_credits,          // credits held
    output logic              o_all_returned,     // no credit held (DEACTIVATE may complete)
    output logic              o_busy,             // a flit is queued or in the skid
    output logic              o_credit_starved,   // a flit waits in RUN with no credit
    output logic              o_protocol_error    // sticky: a grant beyond MAX_LCREDIT
);

    // ------------------------------------------------------------------
    // Skid buffer
    // ------------------------------------------------------------------
    logic [FLIT_W-1:0] w_skid_flit;
    logic [3:0]        w_skid_count;
    logic              w_skid_valid;
    logic              w_send;
    logic              w_rtn;

    gaxi_skid_buffer #(
        .DEPTH      (SKID_DEPTH),
        .DATA_WIDTH (FLIT_W)
    ) u_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fub_valid),
        .wr_ready    (fub_ready),
        .wr_data     (fub_flit),
        .rd_valid    (w_skid_valid),
        .rd_ready    (w_send),
        .rd_count    (w_skid_count),
        .rd_data     (w_skid_flit),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------
    // Credits and FLITPEND
    // ------------------------------------------------------------------
    logic [CRW-1:0] r_credits;
    logic           r_pend;
    logic           w_have_credit;
    logic           w_pend_next;
    logic           w_credit_ovf;

    assign w_have_credit = (r_credits != '0);
    // a flit could go next cycle: a protocol flit in RUN, or a credit to
    // return in DEACTIVATE (FLITPEND without a credit is permitted, B14.4)
    assign w_pend_next   = (i_run && w_skid_valid) || (i_deact && w_have_credit);
    assign w_send        = r_pend && i_run && w_skid_valid && w_have_credit;
    assign w_rtn         = r_pend && i_deact && w_have_credit;
    assign w_credit_ovf  = i_lcrdv && !w_send && !w_rtn && (r_credits == CRW'(MAX_LCREDIT));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_credits <= '0;
            r_pend    <= 1'b0;
        end else begin
            r_pend <= w_pend_next;
            if (!w_credit_ovf)
                r_credits <= r_credits + CRW'(i_lcrdv) - CRW'(w_send) - CRW'(w_rtn);
        end
    )

    // ------------------------------------------------------------------
    // Outputs: an LCrdReturn is the all-zero flit (Opcode 0, TxnID 0)
    // ------------------------------------------------------------------
    assign o_flitpend = w_pend_next;
    assign o_flitv    = w_send || w_rtn;
    assign o_flit     = w_send ? w_skid_flit : '0;

    assign o_credits        = r_credits;
    assign o_all_returned   = !w_have_credit;
    assign o_busy           = fub_valid || (w_skid_count != 4'd0);
    assign o_credit_starved = w_skid_valid && i_run && !w_have_credit;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_protocol_error <= 1'b0;
        end else if (w_credit_ovf) begin
            o_protocol_error <= 1'b1;
        end
    )

endmodule : chi_tx_channel
