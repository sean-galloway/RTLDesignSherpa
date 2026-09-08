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
// RESET IS ASYNCHRONOUS ON ASSERTION. ALWAYS. There is no switch for it.
//
// It used to be conditional on -DUSE_ASYNC_RESET, defaulting to SYNCHRONOUS,
// and the result was that the tools disagreed about what the design even was:
// `make lint` set the define (make/fpga_flow.mk LINT_DEFINES) and saw async,
// while 277 of 325 cocotb test files and every synthesis flow but one left it
// unset and saw sync. Lint was checking a design nobody built. Corrected
// 2026-09-06 (Sean: "All must be asynchronous on assertion").
//
// A flop that needs a clock edge before it will reset is not reset -- it is
// waiting. That is the wrong behaviour at power-on, on a stopped or gated
// clock, and on any domain whose clock is not yet running when reset asserts,
// which is exactly when reset matters.
//
// USE_ASYNC_RESET is now a no-op. Builds that still pass it are harmless and
// can drop it at leisure; nothing needs to be added anywhere.
//
// Build-time switches (set with compiler flags):
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

// Async assert, sync deassert -- the reset reaches the sensitivity list, and
// reset_sync is what makes the RELEASE synchronous. No `ifdef: see above.
`define ALWAYS_FF_RST_LO(clk, rst, BODY)                             \
    always_ff @(posedge (clk) or negedge (rst)) BODY

`define ALWAYS_FF_RST_HI(clk, rst, BODY)                             \
    always_ff @(posedge (clk) or posedge (rst)) BODY

`ifdef RESET_ACTIVE_HIGH
    `define ALWAYS_FF_RST(clk, rst, BODY) `ALWAYS_FF_RST_HI(clk, rst, BODY)
`else
    `define ALWAYS_FF_RST(clk, rst, BODY) `ALWAYS_FF_RST_LO(clk, rst, BODY)
`endif

`endif // RESET_DEFS_SVH
