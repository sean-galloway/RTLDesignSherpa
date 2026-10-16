// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_to_axis
// Purpose: CXS flits (from a cxs_slave's FUB side) -> AXI-Stream beats; the
//          inverse of axis_to_cxs
//
// Documentation: projects/components/utility-ip/converters/docs/converter_mas/ch03_protocol_blocks/17_axis_to_cxs.md
// Subsystem: converters
//
//   TDATA = CXSDATA,  TID = CXSSRCID,  TDEST = CXSTGTID
//   {TUSER, TSTRB} = CXSUSER          (the strobes axis_to_cxs carried)
//   TLAST = END[0] of the flit's CXSCNTL
//
// Combinational, stateless, handshake passed through. AXIS has one TLAST per
// beat, so a flit may carry at most one packet boundary: the only flits this
// block can represent are the ones axis_to_cxs makes (a packet starts at
// pointer 0, at most one START and one END per flit). Anything else -- a CXS
// transmitter that packs two packets into one flit -- sets the sticky
// `unsupported` flag; the beat is still passed on, with TLAST from END[0].
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_to_axis
    import cxs_pkg::*;
#(
    parameter int DATA_WIDTH           = 512,
    parameter int ID_WIDTH             = 8,
    parameter int DEST_WIDTH           = 4,
    parameter int USER_WIDTH           = 1,
    parameter int CXS_MAX_PKT_PER_FLIT = 2,
    parameter int CXS_START_ALIGN      = 16,
    parameter bit CARRY_TUSER          = 1'b1,  // 0: CXSUSER = TSTRB only (CXSUSER is at most 128 bits)
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
    parameter int SPW      = port_w(start_ptr_w(DW, CXS_START_ALIGN))
) (
    input  logic                aclk,
    input  logic                aresetn,

    // CXS flit in (from cxs_slave's fub_cxs_*)
    input  logic                cxs_valid,
    output logic                cxs_ready,
    input  logic [DW-1:0]       cxs_data,
    input  logic [CNTL_PW-1:0]  cxs_cntl,
    input  logic [IW-1:0]       cxs_srcid,
    input  logic [DESTW-1:0]    cxs_tgtid,
    input  logic [CXS_UW-1:0]   cxs_user,

    // AXI-Stream out
    output logic [DW-1:0]       m_axis_tdata,
    output logic [SW-1:0]       m_axis_tstrb,
    output logic                m_axis_tlast,
    output logic [IW-1:0]       m_axis_tid,
    output logic [DESTW-1:0]    m_axis_tdest,
    output logic [UW-1:0]       m_axis_tuser,
    output logic                m_axis_tvalid,
    input  logic                m_axis_tready,

    output logic                unsupported     // sticky: a flit AXIS cannot carry
);

`ifndef SYNTHESIS
    initial begin : param_check
        if (N < 2)
            $fatal(1, "cxs_to_axis: CXSMAXPKTPERFLIT must be >= 2 (TLAST framing needs CXSCNTL)");
    end
`endif

    logic [N-1:0]   w_start, w_end;
    logic [SPW-1:0] w_start0_ptr;
    logic           w_bad;

    assign w_start      = cxs_cntl[0 +: N];
    assign w_end        = cxs_cntl[end_lsb(N, DW, CXS_START_ALIGN) +: N];
    assign w_start0_ptr = cxs_cntl[N +: SPW];

    // More than one START or END, or a packet starting past byte 0
    assign w_bad = cxs_valid && ((|w_start[N-1:1]) || (|w_end[N-1:1]) ||
                                 (w_start[0] && (w_start0_ptr != '0)));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            unsupported <= 1'b0;
        end else if (w_bad) begin
            unsupported <= 1'b1;
        end
    )

    assign m_axis_tvalid = cxs_valid;
    assign cxs_ready     = m_axis_tready;
    assign m_axis_tdata  = cxs_data;
    assign m_axis_tstrb  = cxs_user[0 +: SW];
    if (CARRY_TUSER) begin : g_user
        assign m_axis_tuser = cxs_user[SW +: UW];
    end else begin : g_no_user
        assign m_axis_tuser = '0;
    end
    assign m_axis_tlast  = w_end[0];
    assign m_axis_tid    = cxs_srcid;
    assign m_axis_tdest  = cxs_tgtid;

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_cntl;
    assign unused_cntl = ^cxs_cntl;     // ENDERROR and the END pointers carry nothing AXIS can use
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : cxs_to_axis
