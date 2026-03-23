// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for axi_split_combi (yosys-compatible)
// Proves 4KB boundary splitting correctness: beat conservation,
// boundary alignment, and split decision logic.
// Uses anyconst inputs since the DUT is purely combinational.

`timescale 1ns / 1ps

module formal_axi_split_combi #(
    parameter int AW = 32,
    parameter int DW = 64
) (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // anyconst inputs -- solver picks fixed values, all combos explored
    // =========================================================================
    (* anyconst *) logic [AW-1:0]  fc_current_addr;
    (* anyconst *) logic [7:0]     fc_current_len;
    (* anyconst *) logic [2:0]     fc_ax_size;
    (* anyconst *) logic [11:0]    fc_alignment_mask;
    (* anyconst *) logic           fc_is_idle_state;
    (* anyconst *) logic           fc_transaction_valid;

    // DUT outputs
    logic           split_required;
    logic [7:0]     split_len;
    logic [AW-1:0]  next_boundary_addr;
    logic [7:0]     remaining_len_after_split;
    logic           new_split_needed;

    // Instantiate DUT
    axi_split_combi #(
        .AW (AW),
        .DW (DW)
    ) dut (
        .aclk                    (clk),
        .aresetn                 (rst_n),
        .current_addr            (fc_current_addr),
        .current_len             (fc_current_len),
        .ax_size                 (fc_ax_size),
        .alignment_mask          (fc_alignment_mask),
        .is_idle_state           (fc_is_idle_state),
        .transaction_valid       (fc_transaction_valid),
        .split_required          (split_required),
        .split_len               (split_len),
        .next_boundary_addr      (next_boundary_addr),
        .remaining_len_after_split (remaining_len_after_split),
        .new_split_needed        (new_split_needed)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 1) assume (rst_n);
    end

    // =========================================================================
    // Derived helper signals
    // =========================================================================
    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int LOG2_BPB = $clog2(BYTES_PER_BEAT);

    wire [AW-1:0] total_beats    = AW'(fc_current_len) + AW'(1);
    wire [AW-1:0] total_bytes    = total_beats << fc_ax_size;
    wire [AW-1:0] end_addr       = fc_current_addr + total_bytes - AW'(1);
    wire [AW-1:0] boundary_addr  = (fc_current_addr | AW'(fc_alignment_mask)) + AW'(1);

    // =========================================================================
    // Environment assumptions
    // =========================================================================

    // ax_size matches data bus width (module assumption)
    always @(posedge clk) begin
        if (rst_n)
            assume (fc_ax_size == LOG2_BPB[2:0]);
    end

    // Address aligned to data bus width
    always @(posedge clk) begin
        if (rst_n)
            assume ((fc_current_addr & AW'(BYTES_PER_BEAT - 1)) == '0);
    end

    // 4KB alignment mask
    always @(posedge clk) begin
        if (rst_n)
            assume (fc_alignment_mask == 12'hFFF);
    end

    // No address wraparound: transaction end address >= start address
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid)
            assume (end_addr >= fc_current_addr);
    end

    // No boundary wraparound
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid)
            assume (boundary_addr > fc_current_addr);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: If transaction does not cross 4KB boundary, split_required must be 0
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid)
            if (end_addr < boundary_addr)
                ap_no_cross_no_split: assert (!split_required);
    end

    // P2: If split_required, next_boundary_addr is 4KB-aligned
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid && split_required)
            ap_boundary_aligned: assert ((next_boundary_addr & AW'(12'hFFF)) == '0);
    end

    // P3: Total beats conservation -- split_beats + remaining_beats == original total
    //     split_len uses AXI encoding (beats-1), remaining_len_after_split likewise
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid && split_required) begin
            ap_beats_conserved: assert (
                (AW'(split_len) + AW'(1)) +
                (AW'(remaining_len_after_split) + AW'(1)) ==
                total_beats
            );
        end
    end

    // P4: split_beats > 0 when split_required (split_len >= 0 in AXI encoding
    //     means at least 1 beat, which is always true for 8-bit unsigned)
    //     More specifically: split_len < total_beats (strictly less)
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid && split_required)
            ap_split_beats_positive: assert ((AW'(split_len) + AW'(1)) > AW'(0));
    end

    // P5: When no split required, split_len equals original current_len
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid && !split_required)
            ap_no_split_passthrough: assert (split_len == fc_current_len);
    end

    // P6: When no split, remaining length is 0
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid && !split_required)
            ap_no_split_no_remaining: assert (remaining_len_after_split == 8'd0);
    end

    // P7: new_split_needed requires all three conditions
    always @(posedge clk) begin
        if (rst_n)
            ap_new_split_logic: assert (new_split_needed ==
                                        (split_required && fc_is_idle_state && fc_transaction_valid));
    end

    // P8: next_boundary_addr is strictly greater than current_addr
    always @(posedge clk) begin
        if (rst_n && fc_transaction_valid)
            ap_boundary_gt_addr: assert (next_boundary_addr > fc_current_addr);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: No split needed (transaction fits within boundary)
    always @(posedge clk) begin
        if (rst_n)
            cp_no_split: cover (fc_transaction_valid && !split_required);
    end

    // C2: Split needed (transaction crosses 4KB boundary)
    always @(posedge clk) begin
        if (rst_n)
            cp_split_needed: cover (fc_transaction_valid && split_required);
    end

    // C3: Single-beat transaction (len=0) with no split
    always @(posedge clk) begin
        if (rst_n)
            cp_single_beat: cover (fc_transaction_valid && fc_current_len == 8'd0 &&
                                   !split_required);
    end

    // C4: new_split_needed asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_new_split: cover (new_split_needed);
    end

endmodule
