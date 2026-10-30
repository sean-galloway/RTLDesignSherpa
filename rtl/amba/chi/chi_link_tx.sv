// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_link_tx
// Purpose: TXLINKACTIVEREQ controller for the transmit direction of a CHI
//          port: one LINKACTIVE pair covers every TX channel (B14.5)
//
// Documentation: docs/markdown/rtl-amba/chi/README.md
// Subsystem: amba
//
// The state is the {TXLINKACTIVEREQ, TXLINKACTIVEACK} pair, not an FSM
// (Table B14.1): STOP 00, ACTIVATE 10, RUN 11, DEACTIVATE 01. ACK is
// sampled into r_ack_q and treated as synchronous.
//
//   - STOP -> ACTIVATE (raise REQ) when there is a flit to send (i_want),
//     when cfg_link_hold is set with cfg_link_enable, or when the receive
//     direction of this port has left STOP (B14.6.1: when the RXLINK
//     activates, the TXLINK must also activate in a timely manner). Every
//     raise also needs cfg_rx_enable: a port whose receive side will not
//     acknowledge must not start a handshake it can never finish (the
//     remote TX would wait in ACTIVATE, and B14.6.3.4 forbids dropping
//     TXREQ before RXACK has risen).
//   - RUN -> DEACTIVATE (drop REQ) when the receive direction has entered
//     DEACTIVATE (B14.6.1, the Transmitter "must not delay its own state
//     change"), or when nothing is queued, cfg_link_hold is clear, and one
//     of cfg_link_enable low or cfg_idle_cycles idle RUN cycles have passed
//     (0 = never on idleness alone).
//   So cfg_link_enable = 0 means "do not keep the link up": it drops as soon
//   as idle and is not held, but queued flits and a remote activation still
//   bring it up, which B14.7.2 and B14.6.1 require.
//   - Credits are returned by the channels while REQ is low (chi_tx_channel
//     with i_deact); the receiver drops ACK once they are all home.
//
// B14.6.3.4 ordering between this port's two outputs: TXREQ rises only
// after RXACK has fallen (i_rx_ack low) and falls only after RXACK has
// risen (i_rx_ack high). The four-phase rule of the pair itself: REQ
// rises only with ACK low and falls only with ACK high.
//
// With LINK_CTRL = 0 the direction is always in RUN and REQ is tied low.
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module chi_link_tx
    import chi_pkg::*;
#(
    parameter bit LINK_CTRL = 1'b1
) (
    input  logic       aclk,
    input  logic       aresetn,

    // Configuration
    input  logic       cfg_link_enable,   // 0 = do not keep the link up: drop when idle, never hold
    input  logic       cfg_link_hold,     // 1 = keep the link in RUN with nothing to send
    input  logic [7:0] cfg_idle_cycles,   // idle RUN cycles before deactivating; 0 = never
    input  logic       cfg_rx_enable,     // the receive side's enable: no raise without it

    // From the channels and the receive direction
    input  logic       i_want,            // any TX channel has a flit queued
    input  logic       i_rx_req,          // RXLINKACTIVEREQ as seen by chi_link_rx
    input  logic       i_rx_ack,          // RXLINKACTIVEACK this port drives

    // LINKACTIVE pair
    output logic       o_req,             // TXLINKACTIVEREQ
    input  logic       i_ack,             // TXLINKACTIVEACK

    // Direction state for the channels
    output logic       o_run,
    output logic       o_deact,
    output logic [1:0] o_state            // {REQ, ACK sampled}
);

    logic       w_req;
    logic       w_ack_q;

    if (LINK_CTRL) begin : g_link
        logic       r_req;
        logic       r_ack_q;
        logic [7:0] r_idle_cnt;
        logic       w_rx_left_stop;
        logic       w_rx_deact;
        logic       w_idle_expired;
        logic       w_raise;
        logic       w_drop;

        assign w_rx_left_stop = i_rx_req || i_rx_ack;              // ACTIVATE, RUN or DEACTIVATE
        assign w_rx_deact     = !i_rx_req && i_rx_ack;
        assign w_idle_expired = (cfg_idle_cycles != 8'd0) && (r_idle_cnt >= cfg_idle_cycles);
        assign w_raise        = !r_req && !r_ack_q && !i_rx_ack && cfg_rx_enable &&
                                (i_want || (cfg_link_hold && cfg_link_enable) || w_rx_left_stop);
        assign w_drop         = r_req && r_ack_q && i_rx_ack &&
                                (w_rx_deact ||
                                 (!i_want && !(cfg_link_hold && cfg_link_enable) &&
                                  (!cfg_link_enable || w_idle_expired)));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_req      <= 1'b0;
                r_ack_q    <= 1'b0;
                r_idle_cnt <= 8'd0;
            end else begin
                r_ack_q <= i_ack;
                if (w_raise)
                    r_req <= 1'b1;
                else if (w_drop)
                    r_req <= 1'b0;
                if (!(r_req && r_ack_q) || i_want)
                    r_idle_cnt <= 8'd0;
                else if (r_idle_cnt != 8'hFF)
                    r_idle_cnt <= r_idle_cnt + 8'd1;
            end
        )

        assign w_req   = r_req;
        assign w_ack_q = r_ack_q;
        assign o_run   = r_req && r_ack_q;
        assign o_deact = !r_req && r_ack_q;
    end else begin : g_no_link
        assign w_req   = 1'b0;
        assign w_ack_q = 1'b0;
        assign o_run   = 1'b1;
        assign o_deact = 1'b0;

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_link;
        assign unused_link = ^{aclk, aresetn, cfg_link_enable, cfg_link_hold, cfg_idle_cycles,
                               cfg_rx_enable, i_want, i_rx_req, i_rx_ack, i_ack};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    assign o_req   = w_req;
    // Without link control the direction IS in RUN; the pins stay low but the
    // status says what the channels see
    assign o_state = LINK_CTRL ? {w_req, w_ack_q} : CHI_LINK_RUN;

endmodule : chi_link_tx
