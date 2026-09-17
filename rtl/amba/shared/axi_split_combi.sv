// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_split_combi
// Purpose: Axi Split Combi module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/*
 * AXI Transaction Splitting Combinational Logic - SIMPLIFIED VERSION
 *
 * ASSUMPTIONS (ENFORCED BY ASSERTIONS):
 * - All AXI addresses are aligned to the data bus width
 * - All AXI transfers use maximum transfer size equal to bus width (AxSIZE matches data width)
 * - All bursts use incrementing address mode (AxBURST = 2'b01)
 * - NO ADDRESS WRAPAROUND: Transactions never wrap around the top of address space
 *   (0xFFFFFFFF -> 0x00000000). This is guaranteed by system software/hardware design.
 *
 * RATIONALE FOR NO WRAPAROUND ASSUMPTION:
 * - Top of address space typically reserved for device registers, special regions
 * - Memory allocators avoid allocating near address space boundaries
 * - Wraparound creates unnecessary complexity for a case that never occurs in practice
 * - Simplifies boundary crossing logic significantly
 *
 * TASK-095 (fixed): the BOUNDARY arithmetic is carried in AW+1 bits, so the
 * top alignment window -- where the next boundary is 2**AW and does not fit
 * in AW -- no longer produces a spurious split. The TRANSACTION still must
 * not wrap; that assumption is unchanged and still asserted.
 *
 * OPTIMIZATIONS:
 * - Replaced integer division with bit shifts (synthesis friendly)
 * - Leveraged fixed alignment assumptions for simpler logic
 * - Removed wraparound handling for cleaner, faster logic
 * - Added comprehensive assertions for assumption validation
 * - Fixed all Verilator warnings with proper width casting
 */

module axi_split_combi #(
    parameter int AW = 32,
    parameter int DW = 32  // Data width in bits
) (
    // Clock for assertions only
    input  logic            aclk,
    input  logic            aresetn,

    // Inputs
    input  logic [AW-1:0]   current_addr,           // Current transaction address
    input  logic [7:0]      current_len,            // Current transaction length (AXI encoding)
    input  logic [2:0]      ax_size,                // AXI size field
    input  logic [11:0]     alignment_mask,         // 12-bit alignment mask (e.g., 0xFFF for 4KB)
    input  logic            is_idle_state,          // Whether we're in IDLE state (first transaction)
    input  logic            transaction_valid,      // Whether there's a valid transaction

    // Essential outputs
    output logic            split_required,            // Transaction crosses boundary
    output logic [7:0]      split_len,                 // Length of current split (AXI encoding)
    output logic [AW-1:0]   next_boundary_addr,        // Address at next boundary
    output logic [7:0]      remaining_len_after_split, // Remaining length after this split (AXI encoding)

    // State machine helper
    output logic            new_split_needed           // New split transaction starting
);

    //===========================================================================
    // Parameter Validation and Constants
    //===========================================================================

    // Validate data width is power of 2 and reasonable
    initial begin
        assert (DW inside {32, 64, 128, 256, 512, 1024}) else
            $fatal(1, "DATA_WIDTH must be power of 2 between 32 and 1024 bits");
    end

    // Calculate constants based on data width
    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int LOG2_BYTES_PER_BEAT = $clog2(BYTES_PER_BEAT);
    localparam int EXPECTED_AX_SIZE = LOG2_BYTES_PER_BEAT;
    localparam logic [AW-1:0] ADDR_ALIGN_MASK = AW'(BYTES_PER_BEAT - 1);

    //===========================================================================
    // Core Split Logic
    //===========================================================================

    // Transaction parameters
    logic [AW-1:0] total_bytes;
    logic [AW-1:0] transaction_end_addr;
    logic [AW-1:0] bytes_to_boundary;
    logic [AW-1:0] beats_to_boundary;

    // Calculate total transaction parameters
    assign total_bytes = (AW'(current_len) + AW'(1)) << ax_size;
    assign transaction_end_addr = current_addr + total_bytes - AW'(1);

    // Boundary calculation - SIMPLIFIED (no wraparound)
    // TASK-095: carry the boundary in AW+1 bits. In the TOP alignment window
    // (current_addr | mask) is all ones, so +1 overflowed to 0 in AW bits and
    // crosses_boundary compared the end address against 0 -- always true, so a
    // transaction that crosses nothing was split anyway.
    logic [AW:0] w_next_boundary_ext;
    assign w_next_boundary_ext = {1'b0, (current_addr | AW'(alignment_mask))} + 1'b1;

    // The AW-wide port truncates a 2**AW boundary to 0. That is safe: both
    // splitters read it only on the split path (r_current_addr <= it), and
    // split_required is false in that window. bytes_to_boundary below stays
    // correct either way -- the modular subtraction gives the true byte count.
    assign next_boundary_addr = w_next_boundary_ext[AW-1:0];
    assign bytes_to_boundary = next_boundary_addr - current_addr;
    assign beats_to_boundary = bytes_to_boundary >> ax_size;

    //===========================================================================
    // Split Decision Logic - SIMPLIFIED (no wraparound handling)
    //===========================================================================

    // Transaction requires splitting if:
    // 1. It ends at or past the next boundary, AND
    // 2. We have space for at least one beat before the boundary, AND
    // 3. The beats to boundary is less than or equal to total transaction beats
    logic crosses_boundary;
    logic has_beats_before_boundary;
    logic beats_fit_before_boundary;

    // SIMPLIFIED: No wraparound means straightforward comparison
    assign crosses_boundary = ({1'b0, transaction_end_addr} >= w_next_boundary_ext);
    assign has_beats_before_boundary = (beats_to_boundary > 0);
    assign beats_fit_before_boundary = (beats_to_boundary <= (AW'(current_len) + AW'(1)));

    assign split_required = crosses_boundary && has_beats_before_boundary && beats_fit_before_boundary;

    //===========================================================================
    // Split Length Calculation
    //===========================================================================

    // If we have N beats before boundary, split_len = N - 1 (AXI encoding)
    assign split_len = split_required ?
                        8'(beats_to_boundary - AW'(1)) :
                        current_len;

    //===========================================================================
    // Remaining Length Calculation
    //===========================================================================

    logic [AW-1:0] split_beats_actual;     // Actual beats consumed by split
    logic [AW-1:0] original_beats_total;   // Original total beats
    logic [AW-1:0] remaining_beats_actual; // Remaining beats after split

    assign original_beats_total = AW'(current_len) + AW'(1);
    assign split_beats_actual = split_required ? beats_to_boundary : original_beats_total;
    assign remaining_beats_actual = split_required ? (original_beats_total - split_beats_actual) : AW'(0);

    // Convert remaining beats to AXI encoding (beats - 1)
    assign remaining_len_after_split = split_required ?
                                        ((remaining_beats_actual > 0) ? 8'(remaining_beats_actual - AW'(1)) : 8'(0)) :
                                        8'(0);

    //===========================================================================
    // State Machine Helper
    //===========================================================================

    assign new_split_needed = split_required && is_idle_state && transaction_valid;

    //===========================================================================
    // Input Validation Assertions
    //===========================================================================

    always_ff @(posedge aclk) begin
        if (aresetn && transaction_valid && is_idle_state) begin
            // Check address alignment to data width
            assert ((current_addr & AW'(ADDR_ALIGN_MASK)) == '0) else
                $error("Address 0x%08X is not aligned to %0d-byte data width boundary",
                        current_addr, BYTES_PER_BEAT);

            // Check ax_size matches data width expectation
            assert (ax_size == 3'(EXPECTED_AX_SIZE)) else
                $error("ax_size (%0d) doesn't match expected value (%0d) for %0d-bit data width",
                        ax_size, EXPECTED_AX_SIZE, DW);

            // NO WRAPAROUND ASSERTION: Verify transaction doesn't wrap around
            assert (transaction_end_addr >= current_addr) else
                $error("WRAPAROUND VIOLATION: Transaction wraps around address space! Start=0x%08X, End=0x%08X",
                        current_addr, transaction_end_addr);

            // NO WRAPAROUND ASSERTION: Verify boundary calculation doesn't wrap
            assert (w_next_boundary_ext > {1'b0, current_addr}) else
                $error("WRAPAROUND VIOLATION: Boundary calculation wrapped! Addr=0x%08X, NextBoundary=0x%08X",
                        current_addr, next_boundary_addr);
        end
    end

    //===========================================================================
    // Enhanced Validation Assertions
    //===========================================================================

    always_ff @(posedge aclk) begin
        if (aresetn && transaction_valid) begin

            // Validate beats_to_boundary calculation
            // Max is 4KB boundary / min beat size, e.g., 4096/4 = 1024 for DW=32
            assert (beats_to_boundary <= AW'(4096 / BYTES_PER_BEAT)) else
                $error("beats_to_boundary (%0d) exceeds max for DW=%0d", beats_to_boundary, DW);

            // Validate split length logic
            if (split_required) begin
                assert (split_len < current_len) else
                    $error("split_len (%0d) should be < current_len (%0d) when splitting",
                            split_len, current_len);

                // split_beats + remaining_beats should equal original_beats
                assert ((split_len + 1) + (remaining_len_after_split + 1) == (current_len + 1)) else
                    $error("Length conservation failed - split_beats(%0d) + remaining_beats(%0d) != original_beats(%0d)",
                            split_len + 1, remaining_len_after_split + 1, current_len + 1);

                /* verilator lint_off WIDTHEXPAND */
                assert (split_len == (beats_to_boundary - 1)) else
                    $error("split_len (%0d) should equal beats_to_boundary (%0d) - 1",
                            split_len, beats_to_boundary);
                /* verilator lint_on WIDTHEXPAND */

            end else begin
                // When no split required
                assert (split_len == current_len) else
                    $error("No split: split_len (%0d) should equal current_len (%0d)",
                            split_len, current_len);

                assert (remaining_len_after_split == 0) else
                    $error("No split: remaining_len should be 0, got %0d", remaining_len_after_split);
            end

            // Validate boundary calculations - SIMPLIFIED (no wraparound checks)
            assert (w_next_boundary_ext > {1'b0, current_addr}) else
                $error("next_boundary_addr (0x%08X) should be > current_addr (0x%08X)",
                        next_boundary_addr, current_addr);

            // Validate boundary alignment
            assert ((next_boundary_addr & AW'(alignment_mask)) == '0) else
                $error("next_boundary_addr (0x%08X) not aligned to boundary (mask=0x%03X)",
                        next_boundary_addr, alignment_mask);
        end
    end

    //===========================================================================
    // Debug Information (for verification)
    //===========================================================================

    `ifdef DEBUG_AXI_SPLIT
    // Repaired: this block was a dangling fragment of a deleted $display and
    // failed to compile whenever the documented macro was enabled.
    always_ff @(posedge aclk) begin
        if (aresetn && transaction_valid && is_idle_state) begin
            $display("=== AXI SPLIT DEBUG === addr=%h len=%0d split_required=%0d split_len=%0d remaining_after=%0d",
                     current_addr, current_len, split_required,
                     split_len, remaining_len_after_split);
        end
    end
    `endif

endmodule : axi_split_combi
