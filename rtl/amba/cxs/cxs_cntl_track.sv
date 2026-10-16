// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_cntl_track
// Purpose: Per-stream packet-open tracking and CXSCNTL format checks for one
//          CXS link
//
// Documentation: docs/markdown/rtl-amba/cxs/README.md
// Subsystem: amba
//
// Counts the packets a flit starts (popcount START) and ends (popcount END)
// to keep one bit of state PER STREAM: a packet of that stream has started
// and not yet ended. A CXS stream is the flits that share CXSPRCLTYPE,
// CXSSRCID and CXSTGTID (IHI 0079D 2.5.2), and flits of different streams
// may interleave, so packet framing is legal or not per stream, not per
// link. i_key selects the stream's bit: the caller builds it from the low
// bits of those three fields (KEY_W = 0 tracks the whole link as one
// stream). Streams that differ only in bits outside the key share a bit,
// so the key must cover every stream that can have a packet open at once.
// o_in_packet is "any stream has a packet open": the transmitter uses it
// so it never deactivates the link mid-packet (6.1); the receiver reports
// it. With one packet per flit (CXS-Lite, CNTL_W = 0) every flit is a whole
// packet and the bit is always 0.
//
// Format checks, qualified by i_valid (IHI 0079D Table 4-4):
//   - START and END are thermometer codes ("if any bit is 1, all lower bits
//     must be 1")
//   - ENDERROR[n] requires END[n]
//   - the open count of the flit's stream stays 0 or 1: a flit cannot end a
//     packet that never started, and at most one packet of a stream can be
//     left open at the end of a flit
// Pointer placement (monotonic, aligned) is the BFM monitor's job, not
// this block's.
//
// Parameters:
//   - N:      CXSMAXPKTPERFLIT, 1..4
//   - CNTL_W: CXSCNTLWIDTH (0 when N = 1)
//   - END_LSB / ENDERROR_LSB: field offsets from cxs_pkg
//   - KEY_W:  stream key width; 2**KEY_W bits of state (0 = one stream)
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_cntl_track #(
    parameter int N            = 2,
    parameter int CNTL_W       = 14,
    parameter int END_LSB      = 4,
    parameter int ENDERROR_LSB = 6,
    parameter int KEY_W        = 0,
    parameter int CNTL_PW      = (CNTL_W > 0) ? CNTL_W : 1,
    parameter int KEY_PW       = (KEY_W > 0) ? KEY_W : 1
) (
    input  logic               aclk,
    input  logic               aresetn,
    input  logic               i_valid,     // a flit crosses the link this cycle
    input  logic [CNTL_PW-1:0] i_cntl,
    input  logic [KEY_PW-1:0]  i_key,       // the flit's stream (ignored when KEY_W = 0)
    output logic               o_in_packet, // some stream has a packet open after the last flit
    output logic               o_cntl_err   // this flit's CXSCNTL is malformed (combinational)
);

    if (N > 1) begin : g_track
        logic [N-1:0] w_start, w_end, w_enderr;
        logic [2:0]   w_starts, w_ends;
        logic [3:0]   w_open_next;
        localparam int NS = 1 << KEY_W;
        logic [NS-1:0] r_open;          // per stream: a packet started, not yet ended
        logic          w_open_cur;
        logic         w_thermo_err, w_enderr_err, w_count_err;

        if (KEY_W > 0) begin : g_keyed
            assign w_open_cur = r_open[i_key];
        end else begin : g_one
            assign w_open_cur = r_open[0];
            /* verilator lint_off UNUSEDSIGNAL */
            logic unused_key;
            assign unused_key = ^i_key;
            /* verilator lint_on UNUSEDSIGNAL */
        end

        assign w_start  = i_cntl[0 +: N];
        assign w_end    = i_cntl[END_LSB +: N];
        assign w_enderr = i_cntl[ENDERROR_LSB +: N];
        assign w_starts = 3'($countones(w_start));
        assign w_ends   = 3'($countones(w_end));

        // the stream's open count after this flit: open before + started - ended
        assign w_open_next = 4'(w_open_cur) + 4'(w_starts) - 4'(w_ends);

        assign w_thermo_err = ((w_start & (w_start + N'(1))) != '0) ||
                              ((w_end   & (w_end   + N'(1))) != '0);
        assign w_enderr_err = (w_enderr & ~w_end) != '0;
        // underflow wraps 4'(...) to >= 8, overflow is >= 2: both are > 1
        assign w_count_err  = (w_open_next > 4'd1);

        // The START/END pointers are not needed to count packets
        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_ptrs;
        assign unused_ptrs = ^i_cntl;
        /* verilator lint_on UNUSEDSIGNAL */

        assign o_cntl_err  = i_valid && (w_thermo_err || w_enderr_err || w_count_err);
        assign o_in_packet = |r_open;

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_open <= '0;
            end else if (i_valid && !w_count_err) begin
                r_open[(KEY_W > 0) ? int'(i_key) : 0] <= w_open_next[0];
            end
        )
    end else begin : g_lite
        assign o_in_packet = 1'b0;
        assign o_cntl_err  = 1'b0;

        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_lite;
        assign unused_lite = ^{aclk, aresetn, i_valid, i_cntl, i_key};
        /* verilator lint_on UNUSEDSIGNAL */
    end

endmodule : cxs_cntl_track
