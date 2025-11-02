// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_split_combi
// Purpose: Axi Split Combi module
//
// Documentation: rtl/amba/PRD.md
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

    // synopsys translate_off
    // Validate data width is power of 2 and reasonable
    initial begin
        assert (DW inside {32, 64, 128, 256, 512, 1024}) else
            $fatal(1, "DATA_WIDTH must be power of 2 between 32 and 1024 bits");
    end
    // synopsys translate_on

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
    assign next_boundary_addr = (current_addr | AW'(alignment_mask)) + AW'(1);
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
    assign crosses_boundary = (transaction_end_addr >= next_boundary_addr);
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

    // synopsys translate_off
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
            assert (next_boundary_addr > current_addr) else
                $error("WRAPAROUND VIOLATION: Boundary calculation wrapped! Addr=0x%08X, NextBoundary=0x%08X",
                        current_addr, next_boundary_addr);
        end
    end
    // synopsys translate_on

    //===========================================================================
    // Enhanced Validation Assertions
    //===========================================================================

    // synopsys translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && transaction_valid) begin

            // Validate beats_to_boundary calculation
            assert (beats_to_boundary <= AW'(256)) else  // Reasonable upper bound
                $error("beats_to_boundary (%0d) seems too large", beats_to_boundary);

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
            assert (next_boundary_addr > current_addr) else
                $error("next_boundary_addr (0x%08X) should be > current_addr (0x%08X)",
                        next_boundary_addr, current_addr);

            // Validate boundary alignment
            assert ((next_boundary_addr & AW'(alignment_mask)) == '0) else
                $error("next_boundary_addr (0x%08X) not aligned to boundary (mask=0x%03X)",
                        next_boundary_addr, alignment_mask);
        end
    end
    // synopsys translate_on

    //===========================================================================
    // Debug Information (for verification)
    //===========================================================================

    `ifdef DEBUG_AXI_SPLIT
    always_ff @(posedge aclk) begin
        if (aresetn && transaction_valid && is_idle_state) begin
            $display("=== AXI SPLIT DEBUG (NO WRAPAROUND) ===");
            $display("current_addr = 0x%08X", current_addr);
            $display("current_len = %0d (total beats = %0d)", current_len, current_len + 1);
            $display("ax_size = %0d (bytes_per_beat = %0d)", ax_size, 1 << ax_size);
            $display("alignment_mask = 0x%03X", alignment_mask);
            $display("transaction_end_addr = 0x%08X", transaction_end_addr);
            $display("next_boundary_addr = 0x%08X", next_boundary_addr);
            $display("bytes_to_boundary = %0d", bytes_to_boundary);
            $display("beats_to_boundary = %0d", beats_to_boundary);
            $display("crosses_boundary = %0d", crosses_boundary);
            $display("split_required = %0d", split_required);
            $display("split_len = %0d (split beats = %0d)", split_len, split_len + 1);
            $display("remaining_len_after_split = %0d (remaining beats = %0d)",
                        remaining_len_after_split, remaining_len_after_split + 1);
            $display("=======================================");
        end
    end
    `endif

endmodule : axi_split_combi
