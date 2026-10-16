// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_pkg
// Purpose: CXS (Credited eXtensible Stream, Arm IHI 0079) widths, CXSCNTL
//          field layout and per-issue property legality
//
// Documentation: docs/markdown/rtl-amba/cxs/README.md
// Subsystem: amba
//
// One parameterised family covers every published issue of the spec. Each
// issue is a strict superset of the one before it, so an issue is a set of
// LEGAL PROPERTY VALUES, not a different wire protocol:
//
//   A (2018)  CXSDATAFLITWIDTH 256/512/1024, CXSMAXPKTPERFLIT 2..4,
//             CXS_MAX_CREDIT <= 15, CXSCHECKTYPE, CXSLINKCONTROL
//   B (2020)  + CXSLAST, CXSPRCLTYPE (and their check signals)
//   C (2023)  + CXSMAXPKTPERFLIT 1 (CXSCNTL absent, width 8..2048),
//             CXS_MAX_CREDIT 1..63
//   D (2025)  + 2048-bit flits with several packets, CXS_START_ALIGNMENT 4,
//             CXSSRCID / CXSTGTID (0..8), CXSUSER (0..128), CXS-Lite
//
// CXSCNTL layout (IHI 0079D Tables 4-5 and 4-7), N = CXSMAXPKTPERFLIT:
//   START[N-1:0] | START0..N-1PTR | END[N-1:0] | ENDERROR[N-1:0] | END0..N-1PTR
//   from bit 0 upward. A start pointer is log2(W/128) bits with 16-byte
//   start alignment and log2(W/32) with 4-byte; an end pointer is always
//   log2(W/32). Width = N * (3 + start_ptr_w + end_ptr_w), which reproduces
//   every row of both tables (14, 18, 22, 27, 33, 36, 44 ... 60) and 0 when
//   N = 1.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

package cxs_pkg;

    // Spec issue codes for the CXS_ISSUE parameter
    localparam int CXS_ISSUE_A = 1;
    localparam int CXS_ISSUE_B = 2;
    localparam int CXS_ISSUE_C = 3;
    localparam int CXS_ISSUE_D = 4;

    // ------------------------------------------------------------------
    // Widths
    // ------------------------------------------------------------------
    function automatic int start_ptr_w(int dw, int align);
        return (align == 4) ? $clog2(dw / 32) : $clog2(dw / 128);
    endfunction

    function automatic int end_ptr_w(int dw);
        return $clog2(dw / 32);
    endfunction

    // CXSCNTLWIDTH; 0 when there is one packet per flit (CXS-Lite)
    function automatic int cntl_width(int n, int dw, int align);
        if (n <= 1) return 0;
        return n * (3 + start_ptr_w(dw, align) + end_ptr_w(dw));
    endfunction

    // Odd_Byte_Parity check width: one bit per byte, the top bit covering
    // the short remainder (IHI 0079D 3.2)
    function automatic int chk_width(int w);
        return (w <= 0) ? 0 : (w + 7) / 8;
    endfunction

    // A port of zero width is carried as one tied bit
    function automatic int port_w(int w);
        return (w > 0) ? w : 1;
    endfunction

    // ------------------------------------------------------------------
    // CXSCNTL field offsets (bit position of each field's LSB)
    // ------------------------------------------------------------------
    function automatic int end_lsb(int n, int dw, int align);
        return n + n * start_ptr_w(dw, align);
    endfunction

    function automatic int enderror_lsb(int n, int dw, int align);
        return 2 * n + n * start_ptr_w(dw, align);
    endfunction

    function automatic int end_ptr_lsb(int n, int dw, int align);
        return 3 * n + n * start_ptr_w(dw, align);
    endfunction

    // ------------------------------------------------------------------
    // Property legality for an issue. Returns 0 when the combination is
    // legal, else the number of the first rule broken (see the case list
    // in docs/markdown/rtl-amba/cxs/README.md, "Configuration checks").
    // ------------------------------------------------------------------
    function automatic int config_error(int issue, int dw, int n, int align,
                                        bit has_last, bit has_prcltype,
                                        int srcid_w, int tgtid_w, int user_w,
                                        int max_credit, bit credit_beyond_spec);
        if (issue < CXS_ISSUE_A || issue > CXS_ISSUE_D)          return 1;
        if (n < 1 || n > 4)                                      return 2;
        if (n == 1 && issue < CXS_ISSUE_C)                       return 3;
        if (n == 1) begin
            if (dw < 8 || dw > 2048 || (dw % 8) != 0)            return 4;
            if (has_last || has_prcltype)                        return 5;
        end else begin
            if (!(dw == 256 || dw == 512 || dw == 1024 ||
                  (dw == 2048 && issue >= CXS_ISSUE_D)))         return 6;
            if (dw == 256 && n > 2 &&
                !(align == 4 && issue >= CXS_ISSUE_D))           return 7;
        end
        if (align != 4 && align != 16)                           return 8;
        if (align == 4 && issue < CXS_ISSUE_D)                   return 9;
        if ((has_last || has_prcltype) && issue < CXS_ISSUE_B)   return 10;
        if (max_credit < 1)                                      return 11;
        // credit_beyond_spec: the one sanctioned departure from the spec -- a
        // credit pool deeper than CXS_MAX_CREDIT allows (a receiver whose
        // buffer is a whole SRAM). Both ends must be built with it.
        if (!credit_beyond_spec &&
            max_credit > ((issue >= CXS_ISSUE_C) ? 63 : 15))     return 12;
        if (srcid_w < 0 || srcid_w > 8 ||
            tgtid_w < 0 || tgtid_w > 8 ||
            user_w  < 0 || user_w  > 128)                        return 13;
        if ((srcid_w > 0 || tgtid_w > 0 || user_w > 0) &&
            issue < CXS_ISSUE_D)                                 return 14;
        return 0;
    endfunction

endpackage : cxs_pkg
