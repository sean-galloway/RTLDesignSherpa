// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_pkg
// Purpose:
//   Shared package for the amber MESI L1 cache: geometry parameter defaults
//   (HAS Table 5.0), derived quantities, MESI state encodings, snoop type
//   encodings, replacement / write policy enums, and the HAS Table 3.0
//   snoop CRRESP / next-state decode. Single source of truth for RTL and
//   DV; the kmap workbook and the Python reference model both diff against
//   what is declared here.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_has/ch05_parameters/01_parameters.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

package amber_pkg;

    // ------------------------------------------------------------------
    // Geometry parameter defaults (amber HAS Table 5.0). Modules take
    // these as their own parameter defaults; elaboration may override
    // them (the tiny formal config SETS=16 / WAYS=2 is one such
    // elaboration, not a different source).
    // ------------------------------------------------------------------
    parameter int AMBER_ADDR_WIDTH = 32;
    parameter int AMBER_SETS       = 128;
    parameter int AMBER_WAYS       = 4;
    parameter int AMBER_LINE_BYTES = 64;
    parameter int AMBER_BUS_WIDTH  = 64;

    // ------------------------------------------------------------------
    // Derived quantities at the default geometry. Modules that override
    // the geometry recompute their own equivalents as localparams; these
    // exist so DV and documentation have one place to read.
    // ------------------------------------------------------------------
    localparam int AMBER_SET_INDEX_WIDTH   = $clog2(AMBER_SETS);
    localparam int AMBER_LINE_OFFSET_WIDTH = $clog2(AMBER_LINE_BYTES);
    localparam int AMBER_TAG_WIDTH         = AMBER_ADDR_WIDTH
                                             - AMBER_SET_INDEX_WIDTH
                                             - AMBER_LINE_OFFSET_WIDTH;
    localparam int AMBER_FILL_BEATS        = AMBER_LINE_BYTES / (AMBER_BUS_WIDTH / 8);
    localparam int AMBER_BEAT_INDEX_WIDTH  = $clog2(AMBER_FILL_BEATS);
    localparam int AMBER_TAG_STATE_WIDTH   = AMBER_TAG_WIDTH + 3;
    localparam int AMBER_DATA_MEM_DEPTH    = AMBER_SETS * AMBER_FILL_BEATS;

    // ------------------------------------------------------------------
    // MESI line state (PRD D6): 3-bit field, MESI now with the Owned slot
    // reserved as MOESI headroom. The low 2 bits enumerate {I,S,E,M}; the
    // kmap workbook axes use that 2-bit encoding.
    // ------------------------------------------------------------------
    typedef enum logic [2:0] {
        AMBER_STATE_I    = 3'b000,
        AMBER_STATE_S    = 3'b001,
        AMBER_STATE_E    = 3'b010,
        AMBER_STATE_M    = 3'b011,
        AMBER_STATE_O    = 3'b100,   // reserved: MOESI upgrade path
        AMBER_STATE_RSV5 = 3'b101,
        AMBER_STATE_RSV6 = 3'b110,
        AMBER_STATE_RSV7 = 3'b111
    } cache_state_t;

    // ------------------------------------------------------------------
    // Snoop types: the six IHI0022 AC snoop encodings used by amber, in
    // the compact 3-bit order the kmap workbook axes use. CleanUnique and
    // MakeUnique are transactions a master ISSUES, not snoop types, so
    // they do not appear here (HAS Table 3.0 note). Codes 6/7 are not
    // IHI0022 snoop encodings; amber_control never generates them and the
    // decode functions below contract them to the safe default.
    // ------------------------------------------------------------------
    typedef enum logic [2:0] {
        AMBER_SNOOP_READ_SHARED   = 3'b000,
        AMBER_SNOOP_READ_ONCE     = 3'b001,
        AMBER_SNOOP_READ_UNIQUE   = 3'b010,
        AMBER_SNOOP_CLEAN_SHARED  = 3'b011,
        AMBER_SNOOP_CLEAN_INVALID = 3'b100,
        AMBER_SNOOP_MAKE_INVALID  = 3'b101
    } amber_snoop_t;

    // ------------------------------------------------------------------
    // Replacement policy (PRD D7) and write policy (PRD D5) selectors.
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        AMBER_REPL_LRU       = 2'b00,
        AMBER_REPL_TREE_PLRU = 2'b01,   // timing fallback; no cache_sim golden
        AMBER_REPL_FIFO      = 2'b10,
        AMBER_REPL_RANDOM    = 2'b11
    } amber_repl_t;

    typedef enum logic [0:0] {
        AMBER_WRITE_WB_WA = 1'b0,   // write-back / write-allocate
        AMBER_WRITE_WT_NA = 1'b1    // write-through / no-allocate bring-up
    } amber_write_policy_t;

    // ------------------------------------------------------------------
    // CRRESP (IHI0022): bit 0 = DataTransfer, 1 = Error, 2 = PassDirty,
    // 3 = IsShared, 4 = WasUnique. (The kmap TB carries the same order;
    // the framework CRRESPBit enum in cocotb-framework 1.2.0 is the
    // authority this was cross-checked against.) Error is always 0 in the
    // Table 3.0 matrix -- amber has no snoop-responder error path in v1.0.
    // ------------------------------------------------------------------
    localparam int AMBER_CRRESP_WIDTH = 5;
    localparam int AMBER_CRRESP_DT    = 0;
    localparam int AMBER_CRRESP_ERR   = 1;
    localparam int AMBER_CRRESP_PD    = 2;
    localparam int AMBER_CRRESP_IS    = 3;
    localparam int AMBER_CRRESP_WU    = 4;

    // HAS Table 3.0: CRRESP as a function of the probed line's current
    // state and the snoop type. This is the amber MESI interpretation of
    // the cocotb-framework 1.2.0 ACE BFM default handler, bit for bit,
    // including the release-corrected MakeInvalid-on-Modified behavior
    // (invalidate, no data transfer). Reserved states (incl. Owned) and
    // snoop codes 6/7 return the safe default, matching the don't-care
    // marking in the kmap workbook.
    function automatic logic [AMBER_CRRESP_WIDTH-1:0]
    amber_snoop_crresp(input logic [2:0] state, input logic [2:0] snoop);
        logic dt, pd, is, wu;
        dt = 1'b0;
        pd = 1'b0;
        is = 1'b0;
        wu = 1'b0;
        case (state)
            AMBER_STATE_M: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_CLEAN_SHARED,
                    AMBER_SNOOP_CLEAN_INVALID: begin
                        dt = 1'b1; pd = 1'b1; is = 1'b1;
                    end
                    AMBER_SNOOP_READ_ONCE,
                    AMBER_SNOOP_READ_UNIQUE: begin
                        dt = 1'b1; pd = 1'b1;
                    end
                    default: ;  // MakeInvalid: no transfer (IHI0022 forbids DT)
                endcase
            end
            AMBER_STATE_E: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_READ_ONCE: begin
                        dt = 1'b1; is = 1'b1; wu = 1'b1;
                    end
                    AMBER_SNOOP_READ_UNIQUE: begin
                        dt = 1'b1; wu = 1'b1;
                    end
                    AMBER_SNOOP_CLEAN_SHARED: begin
                        is = 1'b1; wu = 1'b1;   // stays Exclusive per Table 3.0
                    end
                    default: ;  // CleanInvalid / MakeInvalid
                endcase
            end
            AMBER_STATE_S: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_READ_ONCE: begin
                        is = 1'b1;
                    end
                    default: ;  // ReadUnique / CleanShared / CleanInvalid / MakeInvalid
                endcase
            end
            default: ;  // Invalid and reserved states: miss, no data
        endcase
        // IHI0022 bit order: {WasUnique[4], IsShared[3], PassDirty[2],
        // Error[1], DataTransfer[0]}.
        return {wu, is, pd, 1'b0, dt};
    endfunction

    // HAS Table 3.0: next state of the probed line. Same authority and
    // same reserved-cell contract as amber_snoop_crresp.
    function automatic logic [2:0]
    amber_snoop_next_state(input logic [2:0] state, input logic [2:0] snoop);
        logic [2:0] nxt;
        nxt = AMBER_STATE_I;
        case (state)
            AMBER_STATE_M: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_CLEAN_SHARED: nxt = AMBER_STATE_S;
                    default:                  nxt = AMBER_STATE_I;
                endcase
            end
            AMBER_STATE_E: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_READ_ONCE:    nxt = AMBER_STATE_S;
                    AMBER_SNOOP_CLEAN_SHARED: nxt = AMBER_STATE_E;
                    default:                  nxt = AMBER_STATE_I;
                endcase
            end
            AMBER_STATE_S: begin
                case (snoop)
                    AMBER_SNOOP_READ_SHARED,
                    AMBER_SNOOP_READ_ONCE,
                    AMBER_SNOOP_CLEAN_SHARED: nxt = AMBER_STATE_S;
                    default:                  nxt = AMBER_STATE_I;
                endcase
            end
            default: nxt = AMBER_STATE_I;
        endcase
        return nxt;
    endfunction

endpackage : amber_pkg
