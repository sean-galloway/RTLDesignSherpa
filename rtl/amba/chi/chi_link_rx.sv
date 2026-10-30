// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_link_rx
// Purpose: RXLINKACTIVEACK controller for the receive direction of a CHI
//          port: one LINKACTIVE pair covers every RX channel (B14.5)
//
// Documentation: docs/markdown/rtl-amba/chi/README.md
// Subsystem: amba
//
// The state is the {RXLINKACTIVEREQ, RXLINKACTIVEACK} pair (Table B14.1).
// RXLINKACTIVEREQ comes from the other component; it crosses through
// glitch_free_n_dff_arn (LINKACTIVE_SYNC_STAGES flops) and 0 stages is
// allowed for a known-synchronous system.
//
//   - ACTIVATE -> RUN: raise ACK when REQ is seen and cfg_rx_enable is set.
//     Credits are granted only in RUN (o_grant_ok); the receiver "must
//     assert LINKACTIVEACK and move to the RUN state before sending credits"
//     (Table B14.2).
//   - DEACTIVATE -> STOP: stop granting once the synchronized REQ is seen
//     low (o_grant_ok low); because of the synchronizer and the registered
//     LCRDV in chi_rx_channel, up to LINKACTIVE_SYNC_STAGES + 1 grants can
//     still leave after the pin fell. Table B14.2 permits that ("the
//     Receiver is permitted, but not required, to send credits when first
//     entering this state"; B14.5.1.1: it "could take some time to react");
//     the transmitter returns them. Flits still in flight are accepted by
//     the channels; ACK drops only when every channel reports its credits
//     home (i_all_returned), so the transmitter never sees ACK low while
//     it holds a credit.
//
// B14.6.3.4 ordering with this port's TX direction: RXACK rises only after
// TXREQ has risen (i_tx_req high) and falls only after TXREQ has fallen
// (i_tx_req low). chi_link_tx raises TXREQ when this direction leaves
// STOP, so a remote activation completes without the Protocol layer
// doing anything.
//
// cfg_rx_enable gates the activation only: once in RUN, credits flow until
// the link deactivates (a receiver must grant "in a timely manner" while
// the link is active, B14.2.1.1). The port top gives the same input to
// chi_link_tx, which will not start a handshake this side cannot finish.
//
// LINKACTIVE_SYNC_STAGES is 0 (known-synchronous system) or >= 2; the port
// top rejects 1 at elaboration. TXLINKACTIVEACK is sampled once in
// chi_link_tx: the pair is synchronous to CLK unless a clock-domain
// crossing bridge sits between the components (B14.7.1 says the same of
// SACTIVE), and that bridge, not this block, owns the synchronization.
//
// With LINK_CTRL = 0 credits are granted whenever cfg_rx_enable is set and
// ACK is tied low.
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module chi_link_rx
    import chi_pkg::*;
#(
    parameter bit LINK_CTRL             = 1'b1,
    parameter int LINKACTIVE_SYNC_STAGES = 2
) (
    input  logic       aclk,
    input  logic       aresetn,

    // Configuration
    input  logic       cfg_rx_enable,     // 0 = never acknowledge an activation (so never RUN)

    // From the channels and the transmit direction
    input  logic       i_all_returned,    // every RX channel has its credits home
    input  logic       i_tx_req,          // TXLINKACTIVEREQ this port drives

    // LINKACTIVE pair
    input  logic       i_req,             // RXLINKACTIVEREQ
    output logic       o_ack,             // RXLINKACTIVEACK

    // Direction state for the channels
    output logic       o_req_s,           // REQ in this clock domain (for chi_link_tx)
    output logic       o_grant_ok,        // channels may grant credits (RUN)
    output logic [1:0] o_state            // {REQ sampled, ACK}
);

    logic w_req_s;
    logic w_ack;

    if (LINK_CTRL) begin : g_link
        logic r_ack;

        if (LINKACTIVE_SYNC_STAGES >= 2) begin : g_sync
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (LINKACTIVE_SYNC_STAGES),
                .WIDTH      (1)
            ) u_req_sync (
                .clk   (aclk),
                .rst_n (aresetn),
                .d     (i_req),
                .q     (w_req_s)
            );
        end else begin : g_nosync
            assign w_req_s = i_req;
        end

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_ack <= 1'b0;
            end else begin
                if (w_req_s && !r_ack && cfg_rx_enable && i_tx_req)
                    r_ack <= 1'b1;                                   // ACTIVATE -> RUN
                else if (!w_req_s && r_ack && i_all_returned && !i_tx_req)
                    r_ack <= 1'b0;                                   // DEACTIVATE -> STOP
            end
        )

        assign w_ack      = r_ack;
        assign o_grant_ok = w_req_s && r_ack;
    end else begin : g_no_link
        assign w_req_s    = 1'b0;
        assign w_ack      = 1'b0;
        assign o_grant_ok = cfg_rx_enable;

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_link;
        assign unused_link = ^{aclk, aresetn, i_req, i_all_returned, i_tx_req};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    assign o_ack   = w_ack;
    assign o_req_s = w_req_s;
    // Without link control the direction IS in RUN; the pins stay low but the
    // status says what the channels see
    assign o_state = LINK_CTRL ? {w_req_s, w_ack} : CHI_LINK_RUN;

endmodule : chi_link_rx
