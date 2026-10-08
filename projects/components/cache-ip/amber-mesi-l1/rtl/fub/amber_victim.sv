// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_victim
// Purpose:
//   Depth-1 victim buffer for the amber MESI L1 (MAS ch02_blocks/05): holds
//   one dirty cache line while its write-back (drain) is outstanding. The
//   depth-1 size matches the single-outstanding-miss model -- there can be
//   only one dirty victim at a time because the pipeline blocks on the miss
//   until it resolves. Built as a leaf (DECISION D-2 pattern, same as
//   amber_pending_fill_bypass) so the Task 13 formal proof discharges it
//   standalone; instantiated in amber_control.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/05_amber_victim.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_victim
//==============================================================================
// Description:
//   The register holds exactly the three MAS ch02_blocks/05 fields:
//
//     victim_addr   full line address (for AW)
//     victim_data   dirty line data (LINE_BYTES*8)
//     victim_valid  buffer is occupied
//
//   victim_load stages a newly gathered dirty victim: per DECISION D-5 the
//   line is gathered over FILL_BEATS data-array port-A read cycles, so the
//   load strobe is the gather-complete (final-beat) pulse from
//   CTRL_MISS_VICTIM -- MAS ch02's single-cycle full-line load is
//   unreachable (the array port is BUS_WIDTH wide, MAS ch03). The payload is
//   registered and stable from the strobe cycle on. victim_clear retires
//   the buffer when the write-back completes (drain done). victim_busy ==
//   victim_valid and victim_empty == !victim_valid are the MAS handshake
//   status. The snoop side consumes the bypass match in amber_control:
//   victim_valid && (snoop line address == victim_addr), line offset
//   ignored; CD beats are sourced from victim_data while the drain is
//   outstanding.
//
//   The buffer is NEVER loaded while busy (MAS ch02_blocks/05, Review Focus
//   2): the single-outstanding property guarantees the strobe cannot arrive
//   before the previous victim retired, and the load is additionally
//   guarded by !victim_busy here -- a protocol violation can never
//   overwrite a victim whose write-back is still in flight.
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
//   - victim_load / victim_clear are mutually exclusive by FSM construction
//     (load in CTRL_MISS_VICTIM, clear on the drain-done pulse in
//     CTRL_MISS_DRAIN); clear wins defensively if both ever coincided.
//   - victim_clear is the RTL addition over the MAS ch02/05 handshake table:
//     the register lives here, so the retire strobe is a leaf input driven
//     from amber_control's ctrl_drain_done (same pattern as the pf leaf's
//     pf_clear). Recorded in the testplan + Task 14 errata.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_control
//   - Package: amber_pkg (geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py
//   Plan: dv/testplans/amber_victim_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py -v
//   (integration scenarios; Task 13 proves the leaf standalone)
//
//==============================================================================

module amber_victim
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int LINE_WIDTH        = LINE_BYTES * 8
)(
    input  logic clk,
    input  logic rst_n,

    // load: stage a freshly gathered dirty victim (CTRL_MISS_VICTIM
    // gather-complete strobe, DECISION D-5)
    input  logic                      victim_load,
    input  logic [ADDR_WIDTH-1:0]     victim_addr_in,
    input  logic [LINE_WIDTH-1:0]     victim_data_in,

    // clear: the write-back completed (ctrl_drain_done)
    input  logic                      victim_clear,

    // status + field observability (MAS ch02_blocks/05 handshake)
    output logic                      victim_busy,
    output logic                      victim_empty,
    output logic                      victim_valid,
    output logic [ADDR_WIDTH-1:0]     victim_addr,
    output logic [LINE_WIDTH-1:0]     victim_data
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_victim: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_victim: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_victim: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_victim: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // Register fields (MAS ch02_blocks/05)
    // ------------------------------------------------------------------
    logic                    victim_valid_q;
    logic [ADDR_WIDTH-1:0]   victim_addr_q;
    logic [LINE_WIDTH-1:0]   victim_data_q;

    assign victim_valid = victim_valid_q;
    assign victim_busy  = victim_valid_q;
    assign victim_empty = !victim_valid_q;
    assign victim_addr  = victim_addr_q;
    assign victim_data  = victim_data_q;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            victim_valid_q <= 1'b0;
            victim_addr_q  <= '0;
            victim_data_q  <= '0;
        end else begin
            if (victim_clear) begin
                victim_valid_q <= 1'b0;
            end else if (victim_load && !victim_valid_q) begin
                // the !victim_valid_q guard is the depth-1 safety net: a
                // load requested while busy is ignored, never overwriting
                // a victim whose write-back is still in flight (MAS
                // ch02_blocks/05). The control FSM never requests it.
                victim_valid_q <= 1'b1;
                victim_addr_q  <= victim_addr_in;
                victim_data_q  <= victim_data_in;
            end
        end
    )

endmodule : amber_victim
