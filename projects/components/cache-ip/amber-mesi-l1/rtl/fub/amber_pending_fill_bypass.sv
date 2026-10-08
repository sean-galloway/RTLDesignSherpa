// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_pending_fill_bypass
// Purpose:
//   Pending-fill / load-miss bypass register for the amber MESI L1 (MAS
//   ch02_blocks/02): while a fill is outstanding, a snoop for the same
//   line is answered with the post-fill state and the beats already
//   received, before the tag/data arrays are updated. Built as a leaf
//   (DECISION D-2: MAS ch02 calls it a control sub-block) so the Task 13
//   formal proof discharges it standalone; integrated in amber_control.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/02_pending_fill_bypass.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_pending_fill_bypass
//==============================================================================
// Description:
//   The register holds exactly the four MAS ch02_blocks/02 fields:
//
//     pf_addr        line address {tag, set} of the outstanding fill
//     pf_state       state that will be installed when the fill completes
//                    (READ_SHARED -> STATE_S, READ_UNIQUE -> STATE_M; an
//                    upgrade carries no fill data and never loads this
//                    register -- MAS ch02/02, MINOR-1 decision)
//     pf_data_valid  per-beat mask: bit[i] set when fill beat i has been
//                    received (written into the data array, MAS ch02/06)
//     pf_active      register valid and the fill still outstanding
//
//   pf_load arms the register for a new fill (CTRL_MISS_FILL launch);
//   pf_clear retires it at fill commit (CTRL_FILL_WRITE). pf_beat_set(i)
//   with pf_beat_idx accumulates the received-beat mask. The snoop side
//   consumes pf_match combinationally: pf_active && (snoop line address ==
//   pf_addr); the line offset is ignored. The state-accuracy property
//   (MAS ch02/02): the bypass answers at the post-fill pf_state, never
//   the pre-fill Invalid state.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (HAS Table 5.0)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - pf_load / pf_clear / a beat strobe are mutually exclusive by FSM
//     construction (load in CTRL_MISS_FILL, clear in CTRL_FILL_WRITE,
//     beats only while the fill partner is delivering); load and clear
//     take priority over a beat strobe defensively.
//   - The post-commit snoop effect (downgrade/invalidation applied after
//     the fill commits) is control-side context, not a register field:
//     MAS ch02/02 names exactly the four fields above. See amber_control
//     (pend_vld/pend_state) and gem5_mapping_notes.md divergences 3/8.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_control
//   - Package: amber_pkg (cache_state_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py
//   Plan: dv/testplans/amber_pending_fill_bypass_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py -v
//   (integration scenarios; Task 13 proves the leaf standalone)
//
//==============================================================================

module amber_pending_fill_bypass
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int LINE_ADDR_WIDTH   = ADDR_WIDTH - LINE_OFFSET_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // load: arm the register for a newly launched fill (CTRL_MISS_FILL)
    input  logic                        pf_load,
    input  logic [LINE_ADDR_WIDTH-1:0]  pf_load_addr,
    input  logic [2:0]                  pf_load_state,

    // per-beat received strobes (amber_fill beat interface, MAS ch02/06)
    input  logic                        pf_beat_set,
    input  logic [BEAT_INDEX_WIDTH-1:0] pf_beat_idx,

    // match + field observability (snoop side, combinatorial)
    input  logic [LINE_ADDR_WIDTH-1:0]  pf_snoop_addr,
    output logic                        pf_match,
    output logic                        pf_active,
    output logic [LINE_ADDR_WIDTH-1:0]  pf_addr,
    output logic [2:0]                  pf_state,
    output logic [FILL_BEATS-1:0]       pf_data_valid,
    output logic                        pf_beat_valid,   // pf_beat(pf_beat_idx)

    // commit/clear at CTRL_FILL_WRITE
    input  logic                        pf_clear
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_pending_fill_bypass: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_pending_fill_bypass: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_pending_fill_bypass: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_pending_fill_bypass: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // Register fields (MAS ch02_blocks/02)
    // ------------------------------------------------------------------
    logic                       pf_active_q;
    logic [LINE_ADDR_WIDTH-1:0] pf_addr_q;
    logic [2:0]                 pf_state_q;
    logic [FILL_BEATS-1:0]      pf_data_valid_q;

    assign pf_active     = pf_active_q;
    assign pf_addr       = pf_addr_q;
    assign pf_state      = pf_state_q;
    assign pf_data_valid = pf_data_valid_q;

    // match: line address (tag + set) equality; the line offset is ignored
    assign pf_match      = pf_active_q && (pf_snoop_addr == pf_addr_q);
    assign pf_beat_valid = pf_data_valid_q[32'(pf_beat_idx)];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pf_active_q     <= 1'b0;
            pf_addr_q       <= '0;
            pf_state_q      <= AMBER_STATE_I;
            pf_data_valid_q <= '0;
        end else begin
            if (pf_load) begin
                pf_active_q     <= 1'b1;
                pf_addr_q       <= pf_load_addr;
                pf_state_q      <= pf_load_state;
                pf_data_valid_q <= '0;
            end else if (pf_clear) begin
                pf_active_q <= 1'b0;
            end else if (pf_beat_set) begin
                pf_data_valid_q[32'(pf_beat_idx)] <= 1'b1;
            end
        end
    )

endmodule : amber_pending_fill_bypass
