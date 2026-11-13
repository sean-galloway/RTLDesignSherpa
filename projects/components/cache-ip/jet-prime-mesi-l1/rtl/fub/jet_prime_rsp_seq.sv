// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_prime_rsp_seq
// Purpose:
//   Response sequencer for the jet MESI L1 (MAS ch02_blocks/04).  GAXI has no
//   ID field, so responses must leave in request-accept order while fills and
//   merges complete out of order internally.  The sequencer is a CAM-free ring
//   of per-tag completion records: every accepted request is stamped with a
//   monotonic sequence tag, completion data is written into that tag's slot,
//   and a release pointer walks the tags in order.  An incomplete head blocks
//   only the response port; rsp_ready_i low holds only the release pointer.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch02_blocks/04_jet_prime_rsp_seq.md
// Subsystem: jet-prime (forked from jet at 2be919254, 2026-11-12 -- jet-prime TASK-001)
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_prime_rsp_seq
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
//     Default: jet_prime_pkg.RSP_DEPTH (10)
//
//   BUS_WIDTH:
//     Description: Response data width
//     Type: int
//     Default: l1_pkg.AMBER_BUS_WIDTH (64)
//
//   SEQ_W:
//     Description: Sequence-tag width ($clog2(RSP_DEPTH))
//     Type: int
//     Default: jet_prime_pkg.SEQ_W
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - A granted alloc and a release can occur in the same cycle; the net
//     occupancy change is zero and the freed tag is immediately reusable.
//   - Deposit is never gated by rsp_ready_i (the deadlock-freedom property).
//   - A deposit to the current (not-yet-valid) release pointer completes
//     that record AND presents it in the deposit cycle (the head-deposit
//     bypass, TASK-003 step 3, 2026-11-10): rsp_valid_o rises with cpl_i
//     and rsp_data_o carries cpl_data_i, so with rsp_ready_i high the
//     record is released on the deposit edge and never occupies the slot
//     (the slot's valid bit stays clear).  With rsp_ready_i low it lands
//     as before and is released later from the slot.  The bypass release
//     is NOT offered to the tag allocator as a same-cycle re-grant (only a
//     release from the slot is): that keeps the deposit cone out of the
//     accept path.  A deposit to a VALID head tag in its release cycle
//     (the freed slot re-granted and immediately completed by the lookup
//     stage) survives: the release retires the old record, the deposit
//     creates the new one (the sequential block orders release before
//     deposit for exactly this).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: jet_prime_rsp_seq_th (unit DV); jet_prime_control (Tasks 5-7)
//   - Package: jet_prime_pkg (RSP_DEPTH, SEQ_W), l1_pkg (BUS_WIDTH default)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_rsp_seq.py
//   Plan: dv/testplans/jet_prime_rsp_seq_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_rsp_seq.py -v
//
//==============================================================================

module jet_prime_rsp_seq
    import jet_prime_pkg::*;
    import l1_pkg::*;
#(
    parameter int RSP_DEPTH = jet_prime_pkg::RSP_DEPTH,
    parameter int BUS_WIDTH = l1_pkg::AMBER_BUS_WIDTH,
    parameter int SEQ_W     = jet_prime_pkg::SEQ_W,
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
            $error("jet_prime_rsp_seq: RSP_DEPTH must be in 2..32 (J4)");
        if (BUS_WIDTH < 8 || BUS_WIDTH > 512)
            $error("jet_prime_rsp_seq: BUS_WIDTH out of supported range");
    end

    // ------------------------------------------------------------------
    // Entry storage: one completion record per tag.
    // ------------------------------------------------------------------
    logic [RSP_DEPTH-1:0]       r_valid;
    // completion payload: one word per tag, written by the deposit and read
    // at the release pointer -- a distributed RAM, no reset (every word is
    // qualified by r_valid, which IS reset; GLOBAL_REQUIREMENTS 1.4 shape).
    // The async-cleared version was the reset synchronizer's worst recovery
    // path once the larger stores were gone (jet bin 7, FPGA review
    // 2026-11-07).
    (* ram_style = "distributed" *)
    /* synthesis ramstyle = "MLAB" */
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
    logic w_release;
    logic w_head_vld;   // the head slot holds a completed record
    logic w_head_dep;   // this cycle's deposit completes the (empty) head slot
    assign w_head_vld  = r_valid[r_rel_tag];
    assign w_head_dep  = cpl_i & (cpl_tag_i == r_rel_tag) & ~w_head_vld;
    assign w_release   = rsp_ready_i & rsp_valid_o;

    // head-deposit bypass: the completing head is presented in its deposit
    // cycle; a stored head is presented from its slot
    assign rsp_valid_o = w_head_vld | w_head_dep;
    assign rsp_data_o  = w_head_vld ? r_data[r_rel_tag] : cpl_data_i;

    // ------------------------------------------------------------------
    // Tag alloc: grant when a slot is free, including a slot freed from the
    // ring this cycle (a bypass release frees nothing: its slot was never
    // occupied, and the occupancy it carried is returned at the edge).
    // ------------------------------------------------------------------
    assign tag_gnt_o = tag_req_i & ((r_occupancy < OCC_W'(RSP_DEPTH))
                                    | (rsp_ready_i & w_head_vld));
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
        end else begin
            // Release: advance the pointer and free the slot.  Ordered
            // BEFORE the deposit so a same-cycle deposit to the re-granted
            // tag survives: when the ring is full, tag_gnt_o grants the
            // slot being freed by this very release, and the new request's
            // completion may land on that tag immediately (the lookup
            // stage deposits hits in the accept cycle) -- the release
            // retires the OLD record (its response left on the wire this
            // cycle), the deposit creates the NEW one.
            if (w_release) begin
                r_valid[r_rel_tag] <= 1'b0;
                if (r_rel_tag == SEQ_W'(RSP_DEPTH - 1))
                    r_rel_tag <= '0;
                else
                    r_rel_tag <= r_rel_tag + 1'b1;
            end

            // Deposit: write the completion record.  A deposit to the empty
            // head slot that is released in this same cycle (the bypass)
            // leaves the slot clear -- the record left on the wire; any
            // other deposit marks its slot (a not-yet-deposited head never
            // releases: w_release is gated by rsp_valid_o).
            if (cpl_i & ~(w_head_dep & rsp_ready_i)) begin
                r_valid[cpl_tag_i] <= 1'b1;
                // (the word lands in the reset-free payload block below)
            end

            // Tag alloc: advance the alloc pointer on a grant.
            if (tag_req_i && tag_gnt_o) begin
                if (r_alloc_tag == SEQ_W'(RSP_DEPTH - 1))
                    r_alloc_tag <= '0;
                else
                    r_alloc_tag <= r_alloc_tag + 1'b1;
            end

            // Occupancy tracks the net of alloc and release.
            r_occupancy <= r_occupancy
                           + OCC_W'(tag_req_i & tag_gnt_o)
                           - OCC_W'(w_release);
        end
    )

    // pragma translate_off
    // (the cast needs SEQ_W+1 bits: RSP_DEPTH itself does not fit in
    // SEQ_W when RSP_DEPTH is a power of two -- MSHR_COUNT=2 gives
    // RSP_DEPTH=4, SEQ_W=2, and 2'(4) == 0 would fire on every deposit)
    assert property (@(posedge clk) disable iff (!rst_n)
        (cpl_i |-> ({1'b0, cpl_tag_i} < (SEQ_W+1)'(RSP_DEPTH))))
        else $error("jet_prime_rsp_seq: cpl_tag_i out of range (%0d >= %0d)",
                    cpl_tag_i, RSP_DEPTH);
    // pragma translate_on

    // payload store (see the declaration): deposit writes the tag's word
    always_ff @(posedge clk) begin
        if (cpl_i) begin
            r_data[cpl_tag_i] <= cpl_data_i;
        end
    end

endmodule : jet_prime_rsp_seq
