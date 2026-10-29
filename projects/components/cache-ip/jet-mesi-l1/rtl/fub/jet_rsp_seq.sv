// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_rsp_seq
// Purpose:
//   Response sequencer for the jet MESI L1 (MAS ch02_blocks/04).  GAXI has no
//   ID field, so responses must leave in request-accept order while fills and
//   merges complete out of order internally.  The sequencer is a CAM-free ring
//   of per-tag completion records: every accepted request is stamped with a
//   monotonic sequence tag, completion data is written into that tag's slot,
//   and a release pointer walks the tags in order.  An incomplete head blocks
//   only the response port; rsp_ready_i low holds only the release pointer.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch02_blocks/04_jet_rsp_seq.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_rsp_seq
//==============================================================================
// Description:
//   RSP_DEPTH-deep ring of completion records.  The front-end tag allocator
//   grants tag_req_i when at least one slot is free, taking a same-cycle
//   release into account so a freed slot is reusable immediately.  The granted
//   tag appears on tag_o combinationally and r_alloc_tag advances on the next
//   clock edge.  Completion deposits (lookup hits and commit pipeline) write
//   cpl_data_i into the slot selected by cpl_tag_i and mark it valid; this
//   path is independent of rsp_ready_i.  The response port presents the record
//   at the release pointer (r_rel_tag); when rsp_ready_i is asserted the
//   pointer advances and the slot is cleared.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   RSP_DEPTH:
//     Description: Sequencer ring depth (J4)
//     Type: int
//     Range: 2 to 32 (elaboration $error outside)
//     Default: jet_pkg.RSP_DEPTH (10)
//
//   BUS_WIDTH:
//     Description: Response data width
//     Type: int
//     Default: l1_pkg.AMBER_BUS_WIDTH (64)
//
//   SEQ_W:
//     Description: Sequence-tag width ($clog2(RSP_DEPTH))
//     Type: int
//     Default: jet_pkg.SEQ_W
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - A granted alloc and a release can occur in the same cycle; the net
//     occupancy change is zero and the freed tag is immediately reusable.
//   - Deposit is never gated by rsp_ready_i (the deadlock-freedom property).
//   - When a completion is deposited to the current release pointer in the
//     same cycle that rsp_ready_i is high, the newly arrived data is released
//     immediately (deposit is ordered before release in the sequential block).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: jet_rsp_seq_th (unit DV); jet_control (Tasks 5-7)
//   - Package: jet_pkg (RSP_DEPTH, SEQ_W), l1_pkg (BUS_WIDTH default)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_rsp_seq.py
//   Plan: dv/testplans/jet_rsp_seq_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_rsp_seq.py -v
//
//==============================================================================

module jet_rsp_seq
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int RSP_DEPTH = jet_pkg::RSP_DEPTH,
    parameter int BUS_WIDTH = l1_pkg::AMBER_BUS_WIDTH,
    parameter int SEQ_W     = jet_pkg::SEQ_W,
    localparam int OCC_W    = $clog2(RSP_DEPTH + 1)
)(
    input  logic                 clk,
    input  logic                 rst_n,

    // Tag alloc (front end)
    input  logic                 tag_req_i,
    output logic                 tag_gnt_o,
    output logic [SEQ_W-1:0]     tag_o,

    // Deposit (lookup hits and commit pipeline)
    input  logic                 cpl_i,
    input  logic [SEQ_W-1:0]     cpl_tag_i,
    input  logic [BUS_WIDTH-1:0] cpl_data_i,

    // Release (GAXI response channel)
    output logic                 rsp_valid_o,
    output logic [BUS_WIDTH-1:0] rsp_data_o,
    input  logic                 rsp_ready_i
);

    // ------------------------------------------------------------------
    // Elaboration-time range checks (house idiom).
    // ------------------------------------------------------------------
    initial begin
        if (RSP_DEPTH < 2 || RSP_DEPTH > 32)
            $error("jet_rsp_seq: RSP_DEPTH must be in 2..32 (J4)");
        if (BUS_WIDTH < 8 || BUS_WIDTH > 512)
            $error("jet_rsp_seq: BUS_WIDTH out of supported range");
    end

    // ------------------------------------------------------------------
    // Entry storage: one completion record per tag.
    // ------------------------------------------------------------------
    logic [RSP_DEPTH-1:0]       r_valid;
    logic [BUS_WIDTH-1:0]       r_data  [RSP_DEPTH];

    // ------------------------------------------------------------------
    // Ring pointers and occupancy.
    // ------------------------------------------------------------------
    logic [SEQ_W-1:0] r_alloc_tag;
    logic [SEQ_W-1:0] r_rel_tag;
    logic [OCC_W-1:0] r_occupancy;

    // ------------------------------------------------------------------
    // Combinational response port and release event.
    // ------------------------------------------------------------------
    wire w_release = rsp_ready_i & rsp_valid_o;

    assign rsp_valid_o = r_valid[r_rel_tag];
    assign rsp_data_o  = r_data[r_rel_tag];

    // ------------------------------------------------------------------
    // Tag alloc: grant when a slot is free, including a slot freed this cycle.
    // ------------------------------------------------------------------
    assign tag_gnt_o = tag_req_i & ((r_occupancy < OCC_W'(RSP_DEPTH)) | w_release);
    assign tag_o     = r_alloc_tag;

    // ------------------------------------------------------------------
    // Sequential update.
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid     <= '0;
            r_alloc_tag <= '0;
            r_rel_tag   <= '0;
            r_occupancy <= '0;
            for (int s = 0; s < RSP_DEPTH; s++) begin
                r_data[s] <= '0;
            end
        end else begin
            // Deposit first, so a same-cycle deposit+release to the head
            // releases the newly arrived data.
            if (cpl_i) begin
                r_valid[cpl_tag_i] <= 1'b1;
                r_data[cpl_tag_i]  <= cpl_data_i;
            end

            // Release: advance the pointer and free the slot.
            if (w_release) begin
                r_valid[r_rel_tag] <= 1'b0;
                r_rel_tag <= SEQ_W'((int'(r_rel_tag) + 1) % RSP_DEPTH);
            end

            // Tag alloc: advance the alloc pointer on a grant.
            if (tag_req_i && tag_gnt_o) begin
                r_alloc_tag <= SEQ_W'((int'(r_alloc_tag) + 1) % RSP_DEPTH);
            end

            // Occupancy tracks the net of alloc and release.
            r_occupancy <= r_occupancy
                           + OCC_W'(tag_req_i & tag_gnt_o)
                           - OCC_W'(w_release);
        end
    )

endmodule : jet_rsp_seq
