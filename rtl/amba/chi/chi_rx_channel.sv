// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_rx_channel
// Purpose: One credited CHI receive channel (REQ, RSP, DAT or SNP): FLITPEND
//          / FLITV / FLIT in, L-Credits granted on LCRDV, FUB valid/ready
//          flits out
//
// Documentation: docs/markdown/rtl-amba/chi/README.md
// Subsystem: amba
//
// The CHI counterpart of cxs_slave's datapath, one per channel. Every
// credit is a promise of one FIFO slot ("a Receiver must guarantee that it
// can accept all the flits for which it has issued L-Credits", B14.2.1.1),
// so the receive FIFO is the credit pool:
//
//   r_out    credits granted and not yet spent (a protocol flit) or returned
//            (an LCrdReturn), counting the grant on the wire this cycle
//   grant    another credit when, after this edge,
//              FIFO occupancy + r_out < RX_FIFO_DEPTH  and  r_out < MAX_LCREDIT
//
// LCRDV is registered (r_lcrdv) from registered state and this cycle's
// FLITV / FUB pop, so a credit spent in cycle t is granted again at t+1 at
// the earliest and no output depends combinationally on any input.
//
// An LCrdReturn (Opcode 0, B13.11) is a Link flit: it gives a credit back
// and is NOT delivered to the FUB. Credits are granted only while the
// direction is in RUN (i_grant_ok from chi_link_rx); flits are accepted in
// any state (the DEACTIVATE race of Table B14.2).
//
// Protocol errors (sticky o_protocol_error): FLITV without FLITPEND the
// cycle before (B14.4), a flit or return with no credit outstanding, an
// LCrdReturn with a non-zero TxnID.
//
// Parameters:
//   - FLIT_W, OPCODE_LSB, OPCODE_W, TXNID_LSB: the channel's layout
//     (chi_pkg)
//   - MAX_LCREDIT: 1..15
//   - RX_FIFO_DEPTH: the credit pool; default MAX_LCREDIT. A depth below the
//     credit round trip throttles the link. gaxi_fifo_sync needs DEPTH >= 2;
//     a one-credit receiver is built 2 deep and grants against 1.
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module chi_rx_channel #(
    parameter int FLIT_W        = 137,
    parameter int OPCODE_LSB    = 50,
    parameter int OPCODE_W      = 7,
    parameter int TXNID_LSB     = 18,
    parameter int TXNID_W       = 12,
    parameter int MAX_LCREDIT   = 15,
    parameter int RX_FIFO_DEPTH = MAX_LCREDIT,
    parameter int CRW           = $clog2(MAX_LCREDIT + 1)
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Link direction state (chi_link_rx): credits may be granted
    input  logic              i_grant_ok,

    // CHI channel (receive)
    input  logic              i_flitpend,
    input  logic              i_flitv,
    input  logic [FLIT_W-1:0] i_flit,
    output logic              o_lcrdv,

    // FUB side (valid/ready flits out)
    output logic              fub_valid,
    input  logic              fub_ready,
    output logic [FLIT_W-1:0] fub_flit,

    // Status
    output logic [CRW-1:0]    o_outstanding,      // credits granted and not yet home
    output logic              o_all_returned,     // every credit home (DEACTIVATE may complete)
    output logic              o_busy,             // a flit is buffered
    output logic              o_protocol_error    // sticky, see header
);

    localparam int FIFO_D = (RX_FIFO_DEPTH < 2) ? 2 : RX_FIFO_DEPTH;
    localparam int AW     = $clog2(FIFO_D);
    localparam int OW     = ((AW + 1) > (CRW + 1)) ? (AW + 2) : (CRW + 2);   // sum width, no wrap

    // ------------------------------------------------------------------
    // Link flit decode
    // ------------------------------------------------------------------
    logic w_is_lcrd_return;
    logic w_txnid_nonzero;
    logic w_push;
    logic w_rtn;
    logic w_pop;

    assign w_is_lcrd_return = (i_flit[OPCODE_LSB +: OPCODE_W] == '0);
    assign w_txnid_nonzero  = (i_flit[TXNID_LSB +: TXNID_W] != '0);
    assign w_push = i_flitv && !w_is_lcrd_return;
    assign w_rtn  = i_flitv &&  w_is_lcrd_return;
    assign w_pop  = fub_valid && fub_ready;

    // ------------------------------------------------------------------
    // Receive FIFO (the credit pool)
    // ------------------------------------------------------------------
    logic [AW:0]       w_fifo_count;
    logic              w_fifo_wr_ready;

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (FLIT_W),
        .DEPTH      (FIFO_D)
    ) u_rx_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_push),
        .wr_ready    (w_fifo_wr_ready),
        .wr_data     (i_flit),
        .rd_ready    (fub_ready),
        .count       (w_fifo_count),
        .rd_valid    (fub_valid),
        .rd_data     (fub_flit)
    );

    // ------------------------------------------------------------------
    // Credits
    // ------------------------------------------------------------------
    logic [CRW-1:0] r_out;
    logic           r_lcrdv;
    logic           r_pend_q;
    logic [OW-1:0]  w_out_next;
    logic [OW-1:0]  w_occ_next;
    logic           w_can_grant;
    logic           w_underflow;

    // After this edge, before any new grant: the grant on the wire now has
    // joined r_out, a flit or a return has left it, and the FIFO has taken
    // the push and given up the pop.
    assign w_out_next  = OW'(r_out) + OW'(r_lcrdv) - OW'(w_push) - OW'(w_rtn);
    assign w_occ_next  = OW'(w_fifo_count) + OW'(w_push) - OW'(w_pop);
    // A flit with no credit outstanding. The grant on the wire THIS cycle
    // does not count: "an L-Credit cannot be used in the same cycle as being
    // received" (B14.2.1.1), so a flit against it is the same violation.
    assign w_underflow = i_flitv && (r_out == '0);

    assign w_can_grant = i_grant_ok && !w_underflow &&
                         (w_out_next < OW'(MAX_LCREDIT)) &&
                         ((w_occ_next + w_out_next) < OW'(RX_FIFO_DEPTH));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_out    <= '0;
            r_lcrdv  <= 1'b0;
            r_pend_q <= 1'b0;
        end else begin
            r_lcrdv  <= w_can_grant;
            r_pend_q <= i_flitpend;
            if (!w_underflow)
                r_out <= CRW'(w_out_next);
        end
    )

    assign o_lcrdv        = r_lcrdv;
    assign o_outstanding  = r_out;
    assign o_all_returned = (r_out == '0) && !r_lcrdv;
    assign o_busy         = (w_fifo_count != '0);

    // ------------------------------------------------------------------
    // Protocol errors (sticky)
    // ------------------------------------------------------------------
    logic w_proto_err;
    assign w_proto_err = (i_flitv && !r_pend_q) || w_underflow || (w_rtn && w_txnid_nonzero);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_protocol_error <= 1'b0;
        end else if (w_proto_err) begin
            o_protocol_error <= 1'b1;
        end
    )

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused;
    assign unused = w_fifo_wr_ready;
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : chi_rx_channel
