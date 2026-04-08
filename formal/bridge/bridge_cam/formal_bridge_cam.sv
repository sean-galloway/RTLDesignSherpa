// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for bridge_cam -- Content Addressable Memory for transaction tracking
// Verifies reset, allocate/deallocate correctness, count range, status flags
// All assertions use port-level signals only (no hierarchical DUT references)

`include "reset_defs.svh"

module formal_bridge_cam #(
    parameter int TAG_WIDTH        = 4,
    parameter int DATA_WIDTH       = 4,
    parameter int DEPTH            = 4,
    parameter int ALLOW_DUPLICATES = 0,
    parameter int PIPELINE_EVICT   = 0
) (
    input logic clk,
    input logic rst_n
);

    localparam int COUNT_WIDTH = $clog2(DEPTH) + 1;

    // =========================================================================
    // Free inputs for the solver
    // =========================================================================

    (* anyseq *) logic                   allocate;
    (* anyseq *) logic [TAG_WIDTH-1:0]   allocate_tag;
    (* anyseq *) logic [DATA_WIDTH-1:0]  allocate_data;
    (* anyseq *) logic                   deallocate;
    (* anyseq *) logic [TAG_WIDTH-1:0]   deallocate_tag;

    // =========================================================================
    // DUT outputs
    // =========================================================================

    logic                        deallocate_valid;
    logic [DATA_WIDTH-1:0]       deallocate_data;
    logic [COUNT_WIDTH-1:0]      deallocate_count;
    logic                        cam_hit;
    logic                        tags_empty;
    logic                        tags_full;
    logic [COUNT_WIDTH-1:0]      tags_count;

    // =========================================================================
    // DUT instantiation
    // =========================================================================

    bridge_cam #(
        .TAG_WIDTH        (TAG_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .DEPTH            (DEPTH),
        .ALLOW_DUPLICATES (ALLOW_DUPLICATES),
        .PIPELINE_EVICT   (PIPELINE_EVICT)
    ) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .allocate         (allocate),
        .allocate_tag     (allocate_tag),
        .allocate_data    (allocate_data),
        .deallocate       (deallocate),
        .deallocate_tag   (deallocate_tag),
        .deallocate_valid (deallocate_valid),
        .deallocate_data  (deallocate_data),
        .deallocate_count (deallocate_count),
        .cam_hit          (cam_hit),
        .tags_empty       (tags_empty),
        .tags_full        (tags_full),
        .tags_count       (tags_count)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Don't allocate when full (external arbiter responsibility)
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(allocate && tags_full));
        end
    end

    // =========================================================================
    // P1: Reset clears all entries -- tags_empty asserted after reset
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (tags_empty == 1'b1);
    end

    // =========================================================================
    // P2: Reset clears count to zero
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_count_zero: assert (tags_count == '0);
    end

    // =========================================================================
    // P3: Reset clears full flag
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_not_full: assert (tags_full == 1'b0);
    end

    // =========================================================================
    // P4: Mutual exclusion -- empty and full never both asserted
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_mutex_empty_full: assert (!(tags_empty && tags_full));
    end

    // =========================================================================
    // P5: Count range -- tags_count always in [0, DEPTH]
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_count_range: assert (tags_count <= COUNT_WIDTH'(DEPTH));
    end

    // =========================================================================
    // P6: Empty consistent with count
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_empty_iff_zero: assert (tags_empty == (tags_count == '0));
    end

    // =========================================================================
    // P7: Full consistent with count
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_full_iff_depth: assert (tags_full == (tags_count == COUNT_WIDTH'(DEPTH)));
    end

    // =========================================================================
    // P8: Allocate increases count (when no simultaneous deallocate)
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n && $past(rst_n) &&
            $past(allocate) && !$past(tags_full) && !$past(deallocate))
            ap_alloc_increments: assert (tags_count == $past(tags_count) + 1);
    end

    // =========================================================================
    // P9: Deallocate with valid match decreases count (no simultaneous alloc)
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n && $past(rst_n) &&
            $past(deallocate) && $past(deallocate_valid) && !$past(allocate))
            ap_dealloc_decrements: assert (tags_count == $past(tags_count) - 1);
    end

    // =========================================================================
    // P10: Simultaneous alloc+dealloc preserves count (when dealloc valid)
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n && $past(rst_n) &&
            $past(allocate) && !$past(tags_full) &&
            $past(deallocate) && $past(deallocate_valid))
            ap_alloc_dealloc_stable: assert (tags_count == $past(tags_count));
    end

    // =========================================================================
    // P11: cam_hit only when CAM is not empty
    //      (if nothing is stored, nothing can match)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && tags_empty)
            ap_no_hit_when_empty: assert (!cam_hit);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Allocate a tag
    always @(posedge clk) begin
        if (rst_n)
            cp_allocate: cover (allocate && !tags_full);
    end

    // Deallocate a tag successfully
    always @(posedge clk) begin
        if (rst_n)
            cp_deallocate_valid: cover (deallocate && deallocate_valid);
    end

    // CAM becomes full
    always @(posedge clk) begin
        if (rst_n)
            cp_full: cover (tags_full);
    end

    // CAM goes from non-empty back to empty
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && !$past(tags_empty))
            cp_back_to_empty: cover (tags_empty);
    end

    // cam_hit asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_cam_hit: cover (cam_hit);
    end

    // Simultaneous allocate and deallocate
    always @(posedge clk) begin
        if (rst_n)
            cp_simultaneous: cover (allocate && deallocate && deallocate_valid);
    end

endmodule
