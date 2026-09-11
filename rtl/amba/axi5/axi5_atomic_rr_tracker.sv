`timescale 1ns / 1ps

`include "reset_defs.svh"
//
// axi5_atomic_rr_tracker: per-ID return routing for read-return atomics
// (BRIDGE-002 A5-3b)
//
// A read-return atomic (AWATOP[5] == 1: AtomicLoad, AtomicSwap and
// AtomicCompare) is issued on the write address channel and answers with the
// location's original data on the READ data channel, using the AW's ID. A
// fabric whose R-return trackers learn only from ARs has no entry for that
// response, so it would never be routed. This block is that entry.
//
//   - alloc / alloc_id / alloc_data: an accepted read-return atomic AW at a
//     slave-side boundary. Records (ID -> routing tag). The caller must not
//     allocate while `full`; gate the AW handshake on it.
//   - lookup_id -> hit / hit_data: combinational, from the RID being
//     presented. hit means this R beat belongs to a tracked atomic and
//     hit_data is where it goes.
//   - release_beat: the R handshake on its last beat. Frees the matching
//     entry when hit is set; ignored otherwise (the beat was not ours).
//
// Keyed on ID alone. That is sound because AXI5 forbids an atomic from
// sharing its ID with any transaction outstanding from the same Manager.
// Two Managers may still present the same ID at one Subordinate; that
// aliasing is a property of the surrounding fabric (BRIDGE-010), not of
// this block, and the generated adapter checks for it in simulation.
//
// No protocol state machine: a valid vector, two small arrays and two
// priority encoders. Allocate and release can land in the same cycle and
// never on the same slot, since release needs a live entry and allocate
// needs a free one.

module axi5_atomic_rr_tracker #(
    parameter int AXI_ID_WIDTH = 4,
    parameter int DATA_WIDTH   = 1,   // routing tag carried per entry
    parameter int DEPTH        = 4,
    parameter int IW           = AXI_ID_WIDTH,
    parameter int DW           = DATA_WIDTH
) (
    input  logic          aclk,
    input  logic          aresetn,

    // Allocation: an accepted read-return atomic AW
    input  logic          alloc,
    input  logic [IW-1:0] alloc_id,
    input  logic [DW-1:0] alloc_data,
    output logic          full,

    // Lookup: the R beat being presented
    input  logic [IW-1:0] lookup_id,
    output logic          hit,
    output logic [DW-1:0] hit_data,

    // Release: the last beat of an R handshake (qualified by hit inside)
    input  logic          release_beat
);

    logic [DEPTH-1:0] r_valid;
    logic [IW-1:0]    r_id   [DEPTH];
    logic [DW-1:0]    r_data [DEPTH];

    // -----------------------------------------------------------------
    // Match vector against the presented RID.
    // -----------------------------------------------------------------
    logic [DEPTH-1:0] w_match;
    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            w_match[i] = r_valid[i] && (r_id[i] == lookup_id);
        end
    end

    assign hit  = |w_match;
    assign full = &r_valid;

    // -----------------------------------------------------------------
    // Lowest free slot for allocation; lowest matching slot for lookup.
    // Live IDs are unique by the AXI rule above, so the lowest match is
    // the only match.
    // -----------------------------------------------------------------
    localparam int SLOT_W = (DEPTH > 1) ? $clog2(DEPTH) : 1;
    logic [SLOT_W-1:0] w_free_loc;
    logic [SLOT_W-1:0] w_hit_loc;
    always_comb begin
        w_free_loc = '0;
        w_hit_loc  = '0;
        for (int i = DEPTH-1; i >= 0; i--) begin
            if (!r_valid[i]) w_free_loc = SLOT_W'(i);
            if (w_match[i])  w_hit_loc  = SLOT_W'(i);
        end
    end

    assign hit_data = hit ? r_data[w_hit_loc] : '0;

    wire w_do_alloc   = alloc && !full;
    wire w_do_release = release_beat && hit;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_valid <= '0;
        end else begin
            if (w_do_release) begin
                r_valid[w_hit_loc] <= 1'b0;
            end
            if (w_do_alloc) begin
                r_valid[w_free_loc] <= 1'b1;
                r_id[w_free_loc]    <= alloc_id;
                r_data[w_free_loc]  <= alloc_data;
            end
        end
    )

endmodule : axi5_atomic_rr_tracker
