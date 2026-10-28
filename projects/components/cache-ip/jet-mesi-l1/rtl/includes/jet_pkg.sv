// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_pkg
// Purpose:
//   jet-mesi-l1 package: extends the shared cache-ip l1_pkg with the
//   MSHR/writeback geometry and control types added by the J1/J5 rulings.
//   J1: MSHR_COUNT 2–16, default 8.  J5: VICTIM_DEPTH 1–4, default 2.
//   Geometry (FILL_BEATS, line/set/tag widths, MESI encodings) is imported
//   from l1_pkg unchanged so amber and jet share one source of truth.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_has/ch05_parameters/01_parameters.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

package jet_pkg;

    import l1_pkg::*;

    // ------------------------------------------------------------------
    // Jet geometry parameters (J1, J5). Modules take these as their own
    // parameter defaults; elaboration may override them.
    // ------------------------------------------------------------------
    parameter int MSHR_COUNT   = 8;   // J1: outstanding misses, range 2-16
    parameter int VICTIM_DEPTH = 2;   // J5: writeback buffer rows, range 1-4

    // ------------------------------------------------------------------
    // Derived quantities. The response-sequencer depth is the number of
    // in-flight CPU requests (MSHR_COUNT + hit-pipeline depth), rounded
    // to the next convenient power-of-two boundary for the tag CAM.
    // ------------------------------------------------------------------
    parameter int RSP_DEPTH = MSHR_COUNT + 2;
    parameter int SEQ_W     = $clog2(RSP_DEPTH);
    parameter int MW        = $clog2(MSHR_COUNT);

    // ------------------------------------------------------------------
    // Fill request class issued by jet to the memory/interconnect port.
    // Mirrors the amber read-miss classes but is kept jet-specific so
    // future multi-fill-ID work can extend it without touching l1_pkg.
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        JET_CLS_RNSD = 2'b00,   // ReadNotSharedDirty (shared intent)
        JET_CLS_RU   = 2'b01    // ReadUnique (exclusive intent)
    } jet_fill_class_t;

    // ------------------------------------------------------------------
    // Pending snoop effect on an in-flight MSHR entry: what the snoop
    // must do to the expected post-fill state before the line commits.
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        JET_PEND_NONE         = 2'b00,   // no pending effect
        JET_PEND_DOWNGRADE_S  = 2'b01,   // downgrade expected state to Shared
        JET_PEND_INVALIDATE_I = 2'b10    // invalidate expected state
    } jet_pend_eff_t;

endpackage : jet_pkg
