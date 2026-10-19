`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: bridge_cam
// Description: Content Addressable Memory for AXI bridge transaction tracking
//
// Purpose:
//   Stores transaction IDs with associated routing metadata (master_index).
//   Supports two operational modes:
//   - Mode 1 (ALLOW_DUPLICATES=0): Block duplicate IDs via cam_hit signal
//   - Mode 2 (ALLOW_DUPLICATES=1): Allow duplicates with FIFO ordering via count
//
// Key Features:
//   - Two CAM lookup ports: Entry and Eviction
//   - Store transaction ID + associated data (master_index)
//   - Deallocation returns associated data in same cycle
//   - CAM hit detection (always reports if tag exists)
//   - Full/empty status flags
//   - Occupancy counter
//   - FPGA-friendly synthesis (distributed RAM)
//   - Single CAM search loop with match vectors (timing optimized)
//   - Optional pipeline stage on eviction for complex operations
//
// Parameters:
//   TAG_WIDTH        - Width of transaction ID (default: 8 bits)
//   DATA_WIDTH       - Width of associated data/master index (default: 8 bits)
//   DEPTH            - Number of CAM entries (default: 16)
//   ALLOW_DUPLICATES - 0=Mode 1 (simple), 1=Mode 2 (FIFO with count)
//   PIPELINE_EVICT   - 0=Combinational evict, 1=Pipelined (adds 1 cycle latency)
//   PIPELINE_ALLOC   - 0=Combinational insert, 1=Registered insert. allocate
//                      only captures tag/data; the tag match, duplicate count
//                      and entry write happen the next cycle, off a flop, so
//                      the caller's handshake logic (a crossbar's arbitrated
//                      ID) no longer drives the 16-way match + popcount.
//                      The pending entry is visible to the eviction port the
//                      whole time (a response may follow its request by one
//                      cycle), and tags_full counts it.
//   PIPELINE_FREE    - 0=Combinational free, 1=Registered free. The lookup
//                      stays combinational (deallocate_valid / _data route the
//                      response in the same cycle); the entry free and the
//                      same-tag count decrements are applied the next cycle.
//                      Until then every lookup sees the post-free state: the
//                      freed entry no longer matches and pending decrements
//                      are already in the counts. Occupancy drops a cycle
//                      later (tags_full is conservative for one cycle).
//                      A response that takes a still-pending insert, and a
//                      same-tag retire beside an insert, go through the same
//                      registered free, so no storage write enable or count
//                      value depends on the response ID's lookup.
//
// Mode 1 Usage (Simple - Block Duplicates):
//   External arbiter checks cam_hit and blocks allocation if tag exists.
//   CAM prevents same transaction ID from being allocated twice.
//
// Mode 2 Usage (Complex - Out-of-Order Slave Responses):
//   Allows duplicate transaction IDs with FIFO ordering via count field.
//   Handles out-of-order slave responses by always deallocating count=0 first.
//
// Version: 1.5 (PIPELINE_FREE also carries pending takes and same-tag
//               retires: no write enable depends on the response ID)
// Author: RTL Design Sherpa
// Date: 2025-10-26 (1.3: 2026-10-16, 1.5: 2026-10-18)
//==============================================================================

module bridge_cam #(
    parameter int TAG_WIDTH = 8,           // Transaction ID width
    parameter int DATA_WIDTH = 8,          // Master index width
    parameter int DEPTH = 16,              // Number of CAM entries
    parameter int ALLOW_DUPLICATES = 0,    // 0=Mode 1, 1=Mode 2
    parameter int PIPELINE_EVICT = 0,      // 0=Comb, 1=Pipelined (for timing)
    parameter int PIPELINE_ALLOC = 0,      // 0=Comb, 1=Registered insert (for timing)
    parameter int PIPELINE_FREE  = 0       // 0=Comb, 1=Registered free (for timing)
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // === ENTRY PORT (Allocation) ===
    // Store new transaction ID with associated data
    input  logic                        allocate,
    input  logic [TAG_WIDTH-1:0]        allocate_tag,       // Transaction ID to store
    input  logic [DATA_WIDTH-1:0]       allocate_data,      // Associated data (master_index)

    // === EVICTION PORT (Deallocation) ===
    // Free CAM entry when transaction completes, returns associated data
    input  logic                        deallocate,
    input  logic [TAG_WIDTH-1:0]        deallocate_tag,     // Transaction ID to free
    output logic                        deallocate_valid,   // Tag found and freed
    output logic [DATA_WIDTH-1:0]       deallocate_data,    // Retrieved data (master_index)
    output logic [$clog2(DEPTH):0]      deallocate_count,   // Ordering counter (Mode 2 only)

    // === STATUS ===
    output logic                        cam_hit,            // Tag exists in CAM (both modes)
    output logic                        tags_empty,         // No active transactions
    output logic                        tags_full,          // Physical capacity only
    output logic [$clog2(DEPTH):0]      tags_count          // Current occupancy
);

    //==========================================================================
    // Internal Storage Arrays
    //==========================================================================

    localparam int COUNT_WIDTH = $clog2(DEPTH) + 1;

    // Tag array: Stores transaction IDs
    `ifdef XILINX
        (* ram_style = "distributed" *)  // Small CAM uses LUT RAM
    `elsif SYNTH_PRAGMA
        /* synthesis ramstyle = "MLAB" */
    `endif
    logic [TAG_WIDTH-1:0] r_tag_array [DEPTH];

    // Data array: Stores associated metadata (master_index)
    `ifdef XILINX
        (* ram_style = "distributed" *)
    `elsif SYNTH_PRAGMA
        /* synthesis ramstyle = "MLAB" */
    `endif
    logic [DATA_WIDTH-1:0] r_data_array [DEPTH];

    // Counter array: Stores ordering counter for duplicate tags (Mode 2 only)
    `ifdef XILINX
        (* ram_style = "distributed" *)
    `elsif SYNTH_PRAGMA
        /* synthesis ramstyle = "MLAB" */
    `endif
    logic [COUNT_WIDTH-1:0] r_count_array [DEPTH];

    // Valid bits: Entry occupied flags
    logic [DEPTH-1:0] r_valid;

    // Occupancy counter
    logic [COUNT_WIDTH-1:0] r_count;

    //==========================================================================
    // Internal Wires
    //==========================================================================

    integer i, j, k, m, n, p, q;

    // Match vectors - TWO CAM lookup ports only
    logic [DEPTH-1:0] w_entry_matches;      // Which entries match allocate_tag (Entry port)
    logic [DEPTH-1:0] w_evict_matches;      // Which entries match deallocate_tag (Eviction port)

    // Optional pipeline stage for eviction
    logic [DEPTH-1:0] w_evict_matches_active;
    logic w_deallocate_active;
    logic [TAG_WIDTH-1:0] w_deallocate_tag_active;

    // Priority encoder outputs
    integer w_next_free_loc;
    logic w_has_free_slot;

    // Eviction match outputs
    integer w_evict_match_loc;
    integer w_evict_count0_loc;

    // Status flags
    logic w_evict_match_found;
    logic w_evict_count0_found;

    // Insert port: what is written this cycle (the allocate itself, or the
    // registered one under PIPELINE_ALLOC), and the pending-entry bypass.
    logic                  w_alloc_fire;    // allocate accepted this cycle
    logic                  w_ins_v;         // an entry is written this cycle
    logic [TAG_WIDTH-1:0]  w_ins_tag;
    logic [DATA_WIDTH-1:0] w_ins_data;
    logic                  w_pend_v;        // a registered insert is pending
    logic [TAG_WIDTH-1:0]  w_pend_tag;
    logic [DATA_WIDTH-1:0] w_pend_data;
    logic                  w_pend_hit;      // the eviction port takes the pending entry
    logic [DEPTH-1:0]      w_alloc_matches; // allocate_tag vs stored (cam_hit only)

    // Free port: what this cycle's deallocate frees (w_free_*), what is
    // applied to storage this cycle (w_apply_*: the same, or last cycle's
    // under PIPELINE_FREE), and the storage as lookups must see it.
    logic                   w_free_now;
    logic [DEPTH-1:0]       w_free_oh;      // the entry freed
    logic [DEPTH-1:0]       w_free_dec;     // same-tag entries stepping down (Mode 2)
    logic                   w_apply_free;
    logic [DEPTH-1:0]       w_apply_oh;
    logic [DEPTH-1:0]       w_apply_dec;
    logic [DEPTH-1:0]       w_valid_eff;
    logic [COUNT_WIDTH-1:0] w_count_eff [DEPTH];


    //==========================================================================
    // Single CAM Search Loop - TWO Lookup Ports
    //==========================================================================
    // ONE loop, TWO ports: Entry and Eviction

    always_comb begin
        for (i = 0; i < DEPTH; i++) begin
            w_entry_matches[i] = w_valid_eff[i] && (w_ins_tag == r_tag_array[i]);
            w_alloc_matches[i] = w_valid_eff[i] && (allocate_tag == r_tag_array[i]);
            w_evict_matches[i] = w_valid_eff[i] && (deallocate_tag == r_tag_array[i]);
        end
    end

    //==========================================================================
    // Insert Port: combinational or registered (PIPELINE_ALLOC)
    //==========================================================================
    assign w_alloc_fire = allocate && !tags_full;

    generate
        if (PIPELINE_ALLOC == 1) begin : gen_alloc_pipe
            logic                  r_pend_v;
            logic [TAG_WIDTH-1:0]  r_pend_tag;
            logic [DATA_WIDTH-1:0] r_pend_data;
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_pend_v    <= 1'b0;
                    r_pend_tag  <= '0;
                    r_pend_data <= '0;
                end else begin
                    r_pend_v <= w_alloc_fire;
                    if (w_alloc_fire) begin
                        r_pend_tag  <= allocate_tag;
                        r_pend_data <= allocate_data;
                    end
                end
            )
            assign w_pend_v    = r_pend_v;
            assign w_pend_tag  = r_pend_tag;
            assign w_pend_data = r_pend_data;
            // The pending entry is written this cycle unless the eviction
            // port takes it (its response arrived before it reached the CAM).
            // Under PIPELINE_FREE it is written regardless and the take frees
            // its slot through the registered free (w_free_oh below): the
            // write enable then comes off r_pend_v alone, not off the
            // response ID's full match (the 13-15 level worst path into the
            // array clock enables, bridge W12).
            assign w_ins_v    = r_pend_v && ((PIPELINE_FREE == 1) || !(w_pend_hit && w_deallocate_active));
            assign w_ins_tag  = r_pend_tag;
            assign w_ins_data = r_pend_data;
        end else begin : gen_alloc_comb
            assign w_pend_v    = 1'b0;
            assign w_pend_tag  = '0;
            assign w_pend_data = '0;
            assign w_ins_v     = w_alloc_fire;
            assign w_ins_tag   = allocate_tag;
            assign w_ins_data  = allocate_data;
        end
    endgenerate

    //==========================================================================
    // Optional Pipeline Stage for Eviction (Timing Optimization)
    //==========================================================================

    generate
        if (PIPELINE_EVICT == 1) begin : gen_evict_pipe
            logic [DEPTH-1:0] r_evict_matches_pipe;
            logic r_deallocate_pipe;
            logic [TAG_WIDTH-1:0] r_deallocate_tag_pipe;

            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_evict_matches_pipe <= '0;
                    r_deallocate_pipe <= 1'b0;
                    r_deallocate_tag_pipe <= '0;
                end else begin
                    r_evict_matches_pipe <= w_evict_matches;
                    r_deallocate_pipe <= deallocate;
                    r_deallocate_tag_pipe <= deallocate_tag;
                end
            )

            assign w_evict_matches_active = r_evict_matches_pipe;
            assign w_deallocate_active = r_deallocate_pipe;
            assign w_deallocate_tag_active = r_deallocate_tag_pipe;
        end else begin : gen_evict_comb
            assign w_evict_matches_active = w_evict_matches;
            assign w_deallocate_active = deallocate;
            assign w_deallocate_tag_active = deallocate_tag;
        end
    endgenerate

    //==========================================================================
    // Entry Port: CAM Hit Detection
    //==========================================================================

    // cam_hit reports allocate_tag against the stored entries (plus a
    // pending insert of the same tag), whichever insert mode is built.
    assign cam_hit = |w_alloc_matches || (w_pend_v && (w_pend_tag == allocate_tag));

    //==========================================================================
    // Priority Encoder: Find Next Free Slot
    //==========================================================================
    // Scan from high to low, last match wins (returns lowest free index)

    logic [DEPTH-1:0] w_next_free_oh;   // one-hot of w_next_free_loc
    always_comb begin
        w_next_free_loc = -1;
        w_has_free_slot = 1'b0;
        for (m = DEPTH-1; m >= 0; m--) begin
            if (r_valid[m] == 1'b0) begin
                w_next_free_loc = m;
                w_has_free_slot = 1'b1;
            end
        end
        w_next_free_oh = '0;
        for (m = 0; m < DEPTH; m++) begin
            w_next_free_oh[m] = (m == w_next_free_loc);
        end
    end

    //==========================================================================
    // Entry Port: Duplicate Count (Mode 2 only)
    //==========================================================================
    // The entries holding one tag always carry the counts 0..k-1 (a newcomer
    // takes k, the count-0 entry retires and the rest step down), so the
    // count the newcomer needs is simply how many entries match: a popcount
    // of the match vector, an adder tree a few LUTs deep. This used to be a
    // serial "max count over the matching entries" scan -- DEPTH chained
    // comparators, which Vivado built as a 35-level chain hanging off the
    // arbitrated ARID straight out of the crossbar: 32 ns on an Artix-7 -1,
    // the whole bridge capped at ~31 MHz (bridge TASK-006 (was BRIDGE-017) synthesis run,
    // 2026-09-11). Same value, shallow structure.

    logic [COUNT_WIDTH-1:0] w_dup_count;
    always_comb begin
        w_dup_count = '0;
        if (ALLOW_DUPLICATES == 1) begin
            for (n = 0; n < DEPTH; n++) begin
                w_dup_count = w_dup_count + COUNT_WIDTH'(w_entry_matches[n]);
            end
        end
    end

    //==========================================================================
    // Eviction Port: Match Processing
    //==========================================================================
    // Use match vector to find entries to deallocate

    // Mode 1: Find any matching entry
    always_comb begin
        w_evict_match_loc = -1;
        w_evict_match_found = 1'b0;
        for (p = 0; p < DEPTH; p++) begin
            if (w_evict_matches_active[p]) begin
                w_evict_match_loc = p;
                w_evict_match_found = 1'b1;
            end
        end
    end

    // Mode 2: Find entry with matching tag AND count=0 (oldest). Exactly one
    // entry per tag holds count 0, so the hit vector is one-hot and the
    // index is an OR of the hit positions -- a flat reduction, not the
    // DEPTH-long priority chain a last-match-wins loop synthesizes to.
    logic [DEPTH-1:0] w_evict_count0_hits;
    always_comb begin
        w_evict_count0_loc = 0;
        w_evict_count0_found = 1'b0;
        w_evict_count0_hits = '0;
        if (ALLOW_DUPLICATES == 1) begin
            for (q = 0; q < DEPTH; q++) begin
                w_evict_count0_hits[q] = w_evict_matches_active[q] && (w_count_eff[q] == 0);
            end
            w_evict_count0_found = |w_evict_count0_hits;
            for (q = 0; q < DEPTH; q++) begin
                if (w_evict_count0_hits[q]) w_evict_count0_loc = w_evict_count0_loc | q;
            end
        end
    end

    // Mode 2: an allocate and a successful deallocate of the SAME tag in one
    // cycle. The new entry's count comes from w_dup_count, which counts the
    // entries before this cycle's retire lands, so it would be one too high
    // and the tag's counts would hold a gap ({0,2} instead of {0,1}). The
    // entry behind the gap is then unreachable: no deallocate ever finds it
    // at count 0. On the bridge that is bready never rising for a valid B
    // (found by the full-depth arbitration tests, 2026-09-10).
    logic w_same_tag_retire;
    assign w_same_tag_retire = (ALLOW_DUPLICATES == 1) &&
                               w_deallocate_active && w_evict_count0_found &&
                               (w_deallocate_tag_active == w_ins_tag);

    // Pending-entry bypass (PIPELINE_ALLOC). A response may follow its request
    // by one cycle, before the registered insert reaches the CAM. It belongs
    // to the pending entry only if no stored entry carries that tag: a stored
    // one is older (Mode 2: its count-0 entry retires first; Mode 1: any
    // match). Taken, the pending entry is never written.
    logic w_cam_evict_found;
    assign w_cam_evict_found = (ALLOW_DUPLICATES == 0) ? w_evict_match_found : w_evict_count0_found;
    assign w_pend_hit = w_pend_v && !w_cam_evict_found &&
                        (w_deallocate_tag_active == w_pend_tag);

    // Eviction port outputs
    assign deallocate_valid = w_cam_evict_found || w_pend_hit;

    logic [DATA_WIDTH-1:0] w_evict_count0_data;
    always_comb begin
        w_evict_count0_data = '0;
        for (int qd = 0; qd < DEPTH; qd++) begin
            if (w_evict_count0_hits[qd]) w_evict_count0_data = w_evict_count0_data | r_data_array[qd];
        end
    end
    assign deallocate_data = w_pend_hit ? w_pend_data
                           : (ALLOW_DUPLICATES == 0)
                           ? (w_evict_match_found ? r_data_array[w_evict_match_loc] : '0)
                           : w_evict_count0_data;
    // the retiring entry is the count-0 one by construction
    assign deallocate_count = '0;

    //==========================================================================
    // CAM Storage Management
    //==========================================================================
    // Handle allocations and deallocations
    // NOTE: Both can occur in same cycle (independent if blocks)

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid <= '0;
            r_count <= '0;
            for (k = 0; k < DEPTH; k++) begin
                r_tag_array[k] <= '0;
                r_data_array[k] <= '0;
                r_count_array[k] <= '0;
            end
        end else begin
            // Allocate: Store new transaction
            if (w_ins_v) begin
                r_tag_array[w_next_free_loc] <= w_ins_tag;
                r_data_array[w_next_free_loc] <= w_ins_data;
                r_valid[w_next_free_loc] <= 1'b1;

                if (ALLOW_DUPLICATES == 1) begin
                    // Mode 2: order behind the existing duplicates (count =
                    // how many there are). If the oldest of them retires this
                    // very cycle, every survivor steps down by one, so the
                    // newcomer takes one less: here when the free is
                    // combinational, and through the registered decrement
                    // under PIPELINE_FREE (w_free_dec below), which keeps the
                    // response ID's match out of this write.
                    r_count_array[w_next_free_loc] <= (PIPELINE_FREE == 0 && w_same_tag_retire)
                        ? (w_dup_count - 1'b1) : w_dup_count;
                end
            end

            // Free: the entry w_apply_oh leaves, same-tag survivors step
            // down (Mode 2). Independent from the insert: the insert writes a
            // free slot, the decrements touch only live entries.
            if (w_apply_free) begin
                for (j = 0; j < DEPTH; j++) begin
                    if (w_apply_oh[j]) begin
                        r_valid[j]       <= 1'b0;
                        r_tag_array[j]   <= '0;   // waveform clarity
                        r_data_array[j]  <= '0;
                        r_count_array[j] <= '0;
                    end else if (w_apply_dec[j]) begin
                        r_count_array[j] <= r_count_array[j] - 1'b1;
                    end
                end
            end

            // Occupancy counter update
            // (A pending entry taken by the eviction port is neither
            // written nor counted: it never entered r_count.)
            case ({w_ins_v, w_apply_free})
                2'b10: r_count <= r_count + 1'b1;  // Allocate only
                2'b01: r_count <= r_count - 1'b1;  // Deallocate only
                default: r_count <= r_count;       // Both or neither
            endcase
        end
    )

    //==========================================================================
    // Free Port: combinational or registered (PIPELINE_FREE)
    //==========================================================================
    // What this cycle's deallocate frees, as vectors. Mode 1 frees one match;
    // Mode 2 frees the count-0 entry and steps the other matches down.
    //
    // Under PIPELINE_FREE two more cases ride the registered free, so no
    // storage write enable or count value depends on this cycle's lookup:
    //  - the eviction port takes the pending entry: it is written anyway
    //    (w_ins_v) and its slot is freed here;
    //  - a same-tag retire beside an insert: the newcomer is written with
    //    the pre-retire count and steps down with the other survivors.
    logic w_pend_take;
    assign w_pend_take = (PIPELINE_FREE == 1) && w_deallocate_active && w_pend_hit;
    always_comb begin
        w_free_oh  = '0;
        w_free_dec = '0;
        w_free_now = w_deallocate_active && w_cam_evict_found;
        if (w_free_now) begin
            if (ALLOW_DUPLICATES == 0) begin
                w_free_oh[w_evict_match_loc] = 1'b1;
            end else begin
                w_free_oh  = w_evict_count0_hits;
                w_free_dec = w_evict_matches_active & ~w_evict_count0_hits;
                if (PIPELINE_FREE == 1 && w_same_tag_retire && w_ins_v)
                    w_free_dec = w_free_dec | w_next_free_oh;
            end
        end
        if (w_pend_take) begin
            w_free_now = 1'b1;
            w_free_oh  = w_next_free_oh;
        end
    end

    generate
        if (PIPELINE_FREE == 1) begin : gen_free_pipe
            logic             r_pf_v;
            logic [DEPTH-1:0] r_pf_oh;
            logic [DEPTH-1:0] r_pf_dec;
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_pf_v   <= 1'b0;
                    r_pf_oh  <= '0;
                    r_pf_dec <= '0;
                end else begin
                    r_pf_v   <= w_free_now;
                    r_pf_oh  <= w_free_oh;
                    r_pf_dec <= w_free_dec;
                end
            )
            assign w_apply_free = r_pf_v;
            assign w_apply_oh   = r_pf_oh;
            assign w_apply_dec  = r_pf_dec;
            // Lookups this cycle see last cycle's free as done.
            always_comb begin
                for (int e = 0; e < DEPTH; e++) begin
                    w_valid_eff[e] = r_valid[e] && !(r_pf_v && r_pf_oh[e]);
                    w_count_eff[e] = r_count_array[e] - COUNT_WIDTH'(r_pf_v && r_pf_dec[e]);
                end
            end
        end else begin : gen_free_comb
            assign w_apply_free = w_free_now;
            assign w_apply_oh   = w_free_oh;
            assign w_apply_dec  = w_free_dec;
            always_comb begin
                for (int e = 0; e < DEPTH; e++) begin
                    w_valid_eff[e] = r_valid[e];
                    w_count_eff[e] = r_count_array[e];
                end
            end
        end
    endgenerate

    //==========================================================================
    // Status Outputs
    //==========================================================================

    // A pending insert holds a slot: it is counted here so an allocate can
    // never be accepted into a CAM whose last free entry it is about to take.
    logic [COUNT_WIDTH-1:0] w_occupied;
    assign w_occupied = r_count + COUNT_WIDTH'(w_pend_v);
    assign tags_empty = (w_occupied == '0);
    assign tags_full  = (w_occupied == COUNT_WIDTH'(DEPTH));  // Physical capacity only (both modes)
    assign tags_count = w_occupied;

endmodule : bridge_cam
