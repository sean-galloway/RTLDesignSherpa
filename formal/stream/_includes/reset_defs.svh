// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: reset_defs
// Purpose: FIFO Imports module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

// reset_defs.svh
`ifndef RESET_DEFS_SVH
`define RESET_DEFS_SVH

// -----------------------------------------------------------------------------
// Build-time switches (set with compiler flags):
//   -DUSE_ASYNC_RESET        → include reset in sensitivity list
//   -DRESET_ACTIVE_HIGH      → active-HIGH reset (default is active-LOW)
// -----------------------------------------------------------------------------

// Helper: detect reset assertion level in procedural code
`ifdef RESET_ACTIVE_HIGH
    `define RST_ASSERTED(rst) ( (rst) )
`else
    `define RST_ASSERTED(rst) ( !(rst) )
`endif

// NOTE: These macros do NOT add their own 'begin/end'.
//       BODY must be a single procedural statement (e.g. 'if (...) begin ... end'
//       or an explicit block 'begin ... end').

`define ALWAYS_FF_RST_LO(clk, rst, BODY)                             \
    `ifdef USE_ASYNC_RESET                                           \
        always_ff @(posedge (clk) or negedge (rst)) BODY             \
    `else                                                            \
        always_ff @(posedge (clk)) BODY                              \
    `endif

`define ALWAYS_FF_RST_HI(clk, rst, BODY)                             \
    `ifdef USE_ASYNC_RESET                                           \
        always_ff @(posedge (clk) or posedge (rst)) BODY             \
    `else                                                            \
        always_ff @(posedge (clk)) BODY                              \
    `endif

`ifdef RESET_ACTIVE_HIGH
    `define ALWAYS_FF_RST(clk, rst, BODY) `ALWAYS_FF_RST_HI(clk, rst, BODY)
`else
    `define ALWAYS_FF_RST(clk, rst, BODY) `ALWAYS_FF_RST_LO(clk, rst, BODY)
`endif

`endif // RESET_DEFS_SVH
