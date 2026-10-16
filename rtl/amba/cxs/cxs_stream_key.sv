// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_stream_key
// Purpose: The tracked part of a flit's CXS stream identity
//
// Documentation: docs/markdown/rtl-amba/cxs/README.md
// Subsystem: amba
//
// A CXS stream is the flits that share CXSPRCLTYPE, CXSSRCID and CXSTGTID
// (IHI 0079D 2.5.2); packet framing is per stream. Tracking every stream
// would cost 2**19 bits, so a block tracks the low P/S/T bits of the three
// fields:
//
//   o_key = {prcltype[P-1:0], srcid[S-1:0], tgtid[T-1:0]}
//
// Streams that differ only above those bits share one packet-open state,
// so the key must cover every stream that can have a packet open at once
// (RAPIDS: the channel bits of CXSSRCID). P = S = T = 0 is a one-stream
// link (KEY_W = 0, the output is a constant 0).
//
// Parameters:
//   - PRCL_BITS / SRCID_BITS / TGTID_BITS: bits tracked from each field
//   - SRCID_PW / TGTID_PW: the field port widths
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

module cxs_stream_key #(
    parameter int PRCL_BITS  = 0,
    parameter int SRCID_BITS = 0,
    parameter int TGTID_BITS = 0,
    parameter int SRCID_PW   = 1,
    parameter int TGTID_PW   = 1,
    parameter int KEY_W      = PRCL_BITS + SRCID_BITS + TGTID_BITS,
    parameter int KEY_PW     = (KEY_W > 0) ? KEY_W : 1
) (
    input  logic [2:0]          i_prcltype,
    input  logic [SRCID_PW-1:0] i_srcid,
    input  logic [TGTID_PW-1:0] i_tgtid,
    output logic [KEY_PW-1:0]   o_key
);

`ifndef SYNTHESIS
    initial begin : param_check
        if (PRCL_BITS < 0 || PRCL_BITS > 3 || SRCID_BITS < 0 || SRCID_BITS > SRCID_PW ||
            TGTID_BITS < 0 || TGTID_BITS > TGTID_PW)
            $fatal(1, "cxs_stream_key: key bits P=%0d S=%0d T=%0d exceed the fields (3, %0d, %0d)",
                   PRCL_BITS, SRCID_BITS, TGTID_BITS, SRCID_PW, TGTID_PW);
    end
`endif

    always_comb begin
        o_key = '0;
        for (int i = 0; i < TGTID_BITS; i++) o_key[i]                           = i_tgtid[i];
        for (int i = 0; i < SRCID_BITS; i++) o_key[TGTID_BITS + i]              = i_srcid[i];
        for (int i = 0; i < PRCL_BITS;  i++) o_key[TGTID_BITS + SRCID_BITS + i] = i_prcltype[i];
    end

    // Bits above the key are by definition not tracked
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_fields;
    assign unused_fields = ^{i_prcltype, i_srcid, i_tgtid};
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : cxs_stream_key
