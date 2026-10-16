// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis_to_cxs
// Purpose: AXI-Stream beats -> CXS flits (one packet per TLAST run), for the
//          FUB side of a cxs_master
//
// Documentation: projects/components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/17_axis_to_cxs.md
// Subsystem: converters
//
// One AXIS beat is one CXS flit; one TLAST-delimited AXIS packet is one CXS
// packet. The valid/ready handshake passes straight through (combinational:
// this block adds no stage). Mapping:
//
//   CXSDATA   = TDATA
//   CXSCNTL   = START at pointer 0 on the first beat of a packet;
//               END on the TLAST beat, END0PTR = the last 4-byte word that
//               carries a strobe (a CXS packet ends on a 4-byte boundary)
//   CXSSRCID  = TID,  CXSTGTID = TDEST
//   CXSUSER   = {TUSER, TSTRB}  -- the byte strobes ride in the user bits, so
//               a packet of any byte length or offset survives the 4-byte
//               CXS granularity exactly (cxs_to_axis restores TSTRB from them)
//
// Packets are framed PER STREAM: AXIS may interleave packets of different
// TID/TDEST, and CXS lets flits of different streams (CXSSRCID / CXSTGTID)
// interleave too (IHI 0079D 2.5.2), so START goes on the first beat of each
// stream's packet, not the first beat after any TLAST. STREAM_ID_BITS /
// STREAM_DEST_BITS name the low TID / TDEST bits that tell interleaved
// packets apart (0/0: the input never interleaves; one state bit). The far
// end must track the same streams (cxs_slave CXS_STREAM_SRCID_BITS /
// CXS_STREAM_TGTID_BITS).
//
// A flit never carries more than one packet, so CXSMAXPKTPERFLIT >= 2 is
// enough (2 is the minimum that has CXSCNTL). With TSTRB in CXSUSER the link
// needs Issue D (CXS_USER_WIDTH = DW/8 + TUSER width, at most 128).
//
// Parameters:
//   - DATA_WIDTH: TDATA / CXSDATAFLITWIDTH
//   - ID_WIDTH / DEST_WIDTH / USER_WIDTH: TID / TDEST / TUSER (0 legal)
//   - CXS_MAX_PKT_PER_FLIT / CXS_START_ALIGN: size the CXSCNTL layout
//   - STREAM_ID_BITS / STREAM_DEST_BITS: per-stream framing key (see above)
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis_to_cxs
    import cxs_pkg::*;
#(
    parameter int DATA_WIDTH           = 512,
    parameter int ID_WIDTH             = 8,
    parameter int DEST_WIDTH           = 4,
    parameter int USER_WIDTH           = 1,
    parameter int CXS_MAX_PKT_PER_FLIT = 2,
    parameter int CXS_START_ALIGN      = 16,
    parameter bit CARRY_TUSER          = 1'b1,  // 0: CXSUSER = TSTRB only (CXSUSER is at most 128 bits)
    parameter int STREAM_ID_BITS       = 0,     // low TID bits that separate interleaved packets
    parameter int STREAM_DEST_BITS     = 0,     // low TDEST bits that separate interleaved packets
    // Short and calculated params
    parameter int DW       = DATA_WIDTH,
    parameter int SW       = DW / 8,
    parameter int N        = CXS_MAX_PKT_PER_FLIT,
    parameter int IW       = port_w(ID_WIDTH),
    parameter int DESTW    = port_w(DEST_WIDTH),
    parameter int UW       = port_w(USER_WIDTH),
    parameter int CNTL_W   = cntl_width(N, DW, CXS_START_ALIGN),
    parameter int CNTL_PW  = port_w(CNTL_W),
    parameter int CXS_UW   = SW + (CARRY_TUSER ? UW : 0),
    parameter int EPW      = end_ptr_w(DW)
) (
    input  logic                aclk,
    input  logic                aresetn,

    // AXI-Stream in
    input  logic [DW-1:0]       s_axis_tdata,
    input  logic [SW-1:0]       s_axis_tstrb,
    input  logic                s_axis_tlast,
    input  logic [IW-1:0]       s_axis_tid,
    input  logic [DESTW-1:0]    s_axis_tdest,
    input  logic [UW-1:0]       s_axis_tuser,
    input  logic                s_axis_tvalid,
    output logic                s_axis_tready,

    // CXS flit out (to cxs_master's fub_cxs_*)
    output logic                cxs_valid,
    input  logic                cxs_ready,
    output logic [DW-1:0]       cxs_data,
    output logic [CNTL_PW-1:0]  cxs_cntl,
    output logic [IW-1:0]       cxs_srcid,
    output logic [DESTW-1:0]    cxs_tgtid,
    output logic [CXS_UW-1:0]   cxs_user
);

`ifndef SYNTHESIS
    initial begin : param_check
        if (N < 2)
            $fatal(1, "axis_to_cxs: CXSMAXPKTPERFLIT must be >= 2 (TLAST framing needs CXSCNTL)");
    end
`endif

    // ------------------------------------------------------------------
    // First beat of a packet: no beat of this stream accepted since its
    // last TLAST. One bit per stream key (cxs_stream_key: {TID, TDEST} low
    // bits, CXSPRCLTYPE not used).
    // ------------------------------------------------------------------
    localparam int SKEY_W  = STREAM_ID_BITS + STREAM_DEST_BITS;
    localparam int SKEY_PW = (SKEY_W > 0) ? SKEY_W : 1;
    localparam int NS      = 1 << SKEY_W;
    logic [SKEY_PW-1:0] w_key;
    logic [NS-1:0]      r_in_packet;
    logic               w_in_packet;

    cxs_stream_key #(
        .PRCL_BITS  (0),
        .SRCID_BITS (STREAM_ID_BITS),
        .TGTID_BITS (STREAM_DEST_BITS),
        .SRCID_PW   (IW),
        .TGTID_PW   (DESTW)
    ) u_stream_key (
        .i_prcltype (3'b000),
        .i_srcid    (s_axis_tid),
        .i_tgtid    (s_axis_tdest),
        .o_key      (w_key)
    );

    assign w_in_packet = r_in_packet[(SKEY_W > 0) ? int'(w_key) : 0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_in_packet <= '0;
        end else if (s_axis_tvalid && cxs_ready) begin
            r_in_packet[(SKEY_W > 0) ? int'(w_key) : 0] <= !s_axis_tlast;
        end
    )

    // ------------------------------------------------------------------
    // END0PTR: the highest 4-byte word with any strobe set (0 if none)
    // ------------------------------------------------------------------
    localparam int WORDS = DW / 32;
    logic [EPW-1:0] w_end_ptr;

    always_comb begin
        w_end_ptr = '0;
        for (int k = 0; k < WORDS; k++) begin
            if (|s_axis_tstrb[4*k +: 4]) w_end_ptr = EPW'(k);
        end
    end

    // ------------------------------------------------------------------
    // CXSCNTL: one packet at most per flit -- START[0] (pointer 0) on the
    // first beat, END[0] with END0PTR on the TLAST beat; ENDERROR never set
    // ------------------------------------------------------------------
    logic [CNTL_PW-1:0] w_cntl;

    always_comb begin
        w_cntl = '0;
        w_cntl[0] = !w_in_packet;                                   // START[0], START0PTR = 0
        w_cntl[end_lsb(N, DW, CXS_START_ALIGN)] = s_axis_tlast;     // END[0]
        if (s_axis_tlast)
            w_cntl[end_ptr_lsb(N, DW, CXS_START_ALIGN) +: EPW] = w_end_ptr;
    end

    assign cxs_valid     = s_axis_tvalid;
    assign s_axis_tready = cxs_ready;
    assign cxs_data      = s_axis_tdata;
    assign cxs_cntl      = w_cntl;
    assign cxs_srcid     = s_axis_tid;
    assign cxs_tgtid     = s_axis_tdest;
    if (CARRY_TUSER) begin : g_user
        assign cxs_user = {s_axis_tuser, s_axis_tstrb};
    end else begin : g_strb_only
        assign cxs_user = s_axis_tstrb;
        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_tuser;
        assign unused_tuser = ^s_axis_tuser;
        /* verilator lint_on UNUSEDSIGNAL */
    end

endmodule : axis_to_cxs
