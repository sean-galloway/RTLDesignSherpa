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
//
// Mode 1 Usage (Simple - Block Duplicates):
//   External arbiter checks cam_hit and blocks allocation if tag exists.
//   CAM prevents same transaction ID from being allocated twice.
//
// Mode 2 Usage (Complex - Out-of-Order Slave Responses):
//   Allows duplicate transaction IDs with FIFO ordering via count field.
//   Handles out-of-order slave responses by always deallocating count=0 first.
//
// Version: 1.2
// Author: RTL Design Sherpa
// Date: 2025-10-26
//==============================================================================

module bridge_cam #(
    parameter int TAG_WIDTH = 8,           // Transaction ID width
    parameter int DATA_WIDTH = 8,          // Master index width
    parameter int DEPTH = 16,              // Number of CAM entries
    parameter int ALLOW_DUPLICATES = 0,    // 0=Mode 1, 1=Mode 2
    parameter int PIPELINE_EVICT = 0       // 0=Comb, 1=Pipelined (for timing)
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
    `elsif INTEL
        /* synthesis ramstyle = "MLAB" */
    `endif
    logic [TAG_WIDTH-1:0] r_tag_array [DEPTH];

    // Data array: Stores associated metadata (master_index)
    `ifdef XILINX
        (* ram_style = "distributed" *)
    `elsif INTEL
        /* synthesis ramstyle = "MLAB" */
    `endif
    logic [DATA_WIDTH-1:0] r_data_array [DEPTH];

    // Counter array: Stores ordering counter for duplicate tags (Mode 2 only)
    `ifdef XILINX
        (* ram_style = "distributed" *)
    `elsif INTEL
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

    // Mode 2 max count
    logic [COUNT_WIDTH-1:0] w_max_count_for_entry_tag;

    //==========================================================================
    // Single CAM Search Loop - TWO Lookup Ports
    //==========================================================================
    // ONE loop, TWO ports: Entry and Eviction

    always_comb begin
        for (i = 0; i < DEPTH; i++) begin
            w_entry_matches[i] = r_valid[i] && (allocate_tag == r_tag_array[i]);
            w_evict_matches[i] = r_valid[i] && (deallocate_tag == r_tag_array[i]);
        end
    end

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

    assign cam_hit = |w_entry_matches;

    //==========================================================================
    // Priority Encoder: Find Next Free Slot
    //==========================================================================
    // Scan from high to low, last match wins (returns lowest free index)

    always_comb begin
        w_next_free_loc = -1;
        w_has_free_slot = 1'b0;
        for (m = DEPTH-1; m >= 0; m--) begin
            if (r_valid[m] == 1'b0) begin
                w_next_free_loc = m;
                w_has_free_slot = 1'b1;
            end
        end
    end

    //==========================================================================
    // Entry Port: Max Count Search (Mode 2 only)
    //==========================================================================
    // Only search entries that matched allocate_tag

    always_comb begin
        w_max_count_for_entry_tag = 0;
        if (ALLOW_DUPLICATES == 1) begin
            for (n = 0; n < DEPTH; n++) begin
                if (w_entry_matches[n]) begin
                    if (r_count_array[n] > w_max_count_for_entry_tag) begin
                        w_max_count_for_entry_tag = r_count_array[n];
                    end
                end
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

    // Mode 2: Find entry with matching tag AND count=0 (oldest)
    always_comb begin
        w_evict_count0_loc = -1;
        w_evict_count0_found = 1'b0;
        if (ALLOW_DUPLICATES == 1) begin
            for (q = 0; q < DEPTH; q++) begin
                if (w_evict_matches_active[q] && (r_count_array[q] == 0)) begin
                    w_evict_count0_loc = q;
                    w_evict_count0_found = 1'b1;
                end
            end
        end
    end

    // Eviction port outputs
    assign deallocate_valid = (ALLOW_DUPLICATES == 0) ? w_evict_match_found : w_evict_count0_found;

    assign deallocate_data = (ALLOW_DUPLICATES == 0)
                           ? (w_evict_match_found ? r_data_array[w_evict_match_loc] : '0)
                           : (w_evict_count0_found ? r_data_array[w_evict_count0_loc] : '0);

    assign deallocate_count = (ALLOW_DUPLICATES == 1 && w_evict_count0_found)
                            ? r_count_array[w_evict_count0_loc] : '0;

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
            if (allocate && !tags_full) begin
                r_tag_array[w_next_free_loc] <= allocate_tag;
                r_data_array[w_next_free_loc] <= allocate_data;
                r_valid[w_next_free_loc] <= 1'b1;

                if (ALLOW_DUPLICATES == 1) begin
                    // Mode 2: Set count based on existing duplicates
                    r_count_array[w_next_free_loc] <= cam_hit
                        ? (w_max_count_for_entry_tag + 1'b1)  // Increment
                        : '0;                                   // First occurrence
                end
            end

            // Deallocate: Free entry (independent from allocate)
            if (w_deallocate_active) begin
                if (ALLOW_DUPLICATES == 0) begin
                    // Mode 1: Simple deallocation - free any matching entry
                    if (w_evict_match_found) begin
                        r_valid[w_evict_match_loc] <= 1'b0;
                        r_tag_array[w_evict_match_loc] <= '0;  // Optional: waveform clarity
                        r_data_array[w_evict_match_loc] <= '0;
                    end
                end else begin
                    // Mode 2: FIFO deallocation - free count=0, decrement others
                    if (w_evict_count0_found) begin
                        // Free the count=0 entry (oldest)
                        r_valid[w_evict_count0_loc] <= 1'b0;
                        r_tag_array[w_evict_count0_loc] <= '0;
                        r_data_array[w_evict_count0_loc] <= '0;
                        r_count_array[w_evict_count0_loc] <= '0;

                        // Decrement ONLY matching entries (use match vector)
                        for (j = 0; j < DEPTH; j++) begin
                            if (j != w_evict_count0_loc && w_evict_matches_active[j]) begin
                                r_count_array[j] <= r_count_array[j] - 1'b1;
                            end
                        end
                    end
                end
            end

            // Occupancy counter update
            case ({allocate && !tags_full,
                   w_deallocate_active && (ALLOW_DUPLICATES == 0 ? w_evict_match_found
                                                                  : w_evict_count0_found)})
                2'b10: r_count <= r_count + 1'b1;  // Allocate only
                2'b01: r_count <= r_count - 1'b1;  // Deallocate only
                default: r_count <= r_count;       // Both or neither
            endcase
        end
    )

    //==========================================================================
    // Status Outputs
    //==========================================================================

    assign tags_empty = (r_count == '0);
    assign tags_full = (r_count == COUNT_WIDTH'(DEPTH));  // Physical capacity only (both modes)
    assign tags_count = r_count;

endmodule : bridge_cam
