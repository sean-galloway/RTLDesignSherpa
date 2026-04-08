// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dma_address_gen
// Purpose:
//   Two-dimensional strided address generator with wrap and signed stride
//   support. 2-stage pipeline for timing closure at high frequencies.
//
// Documentation: projects/components/misc/README.md
// Subsystem: misc
// Registers: projects/components/misc/rdl/dma_address_gen.rdl
//
// Author: sean galloway
// Created: 2025-04-08

`timescale 1ns / 1ps

//==============================================================================
// Module: dma_address_gen
//==============================================================================
// Description:
//   Generates addresses using a base address plus two independently strided
//   index dimensions with optional per-dimension wrap (circular buffer).
//   Suitable for DMA engines, scatter/gather, 2D block transfers, ring
//   buffers, and any descriptor-driven memory access pattern.
//
//   Address formula:
//     offset_0    = (index_0 * stride_0) & wrap_mask_0   (if wrap enabled)
//     offset_0    = (index_0 * stride_0)                 (if wrap disabled)
//     offset_1    = (index_1 * stride_1) & wrap_mask_1   (if wrap enabled)
//     offset_1    = (index_1 * stride_1)                 (if wrap disabled)
//     result_addr = base + offset_0 + offset_1
//
//   Wrap behavior:
//     - wrap_mask = 0 means no wrap (full address range)
//     - wrap_mask != 0 constrains offset to power-of-2 region via bitwise AND
//     - Each dimension wraps independently
//     - Example: wrap_mask = 24'hFFF wraps offset within a 4KB region
//
//   Signed strides:
//     - Strides are signed, enabling reverse traversal (negative stride)
//     - Example: stride = -4 walks backwards through a buffer
//     - Useful for image vertical flip, reverse playback, bottom-up formats
//
//   Addressing modes via descriptor programming:
//     - Linear/incremental: stride_1=0, stride_0=element_size
//     - Row-major 2D:       stride_0=element_size, stride_1=row_pitch
//     - Column-major 2D:    stride_0=col_pitch, stride_1=element_size
//     - Fixed (FIFO):       stride_0=0, stride_1=0
//     - Circular buffer:    stride_0=element_size, wrap_mask_0=buf_size-1
//     - Reverse traversal:  stride_0=-element_size (signed negative)
//
// Features:
//   - Parameterizable address width (up to 64 bits)
//   - Parameterizable index and stride widths
//   - Signed strides for forward and reverse traversal
//   - Per-dimension power-of-2 wrap masks (circular buffer support)
//   - Parameterizable pass-through tag for downstream routing
//   - Valid/ready handshaking on both request and result interfaces
//   - Pipeline stall support (backpressure propagation)
//   - 2-stage pipeline for timing closure at high frequencies
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH:
//     Description: Width of generated addresses in bits
//     Type: int
//     Range: 8 to 64
//     Default: 40
//
//   INDEX_WIDTH:
//     Description: Width of dimension index inputs in bits
//     Type: int
//     Range: 1 to 32
//     Default: 16
//
//   STRIDE_WIDTH:
//     Description: Width of stride configuration inputs in bits (signed)
//     Type: int
//     Range: 2 to 32
//     Default: 24
//     Note: Signed, so effective range is -(2^(N-1)) to +(2^(N-1)-1)
//
//   TAG_WIDTH:
//     Description: Width of pass-through tag (set to 1 if unused)
//     Type: int
//     Range: 1 to 64
//     Default: 8
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_clk:               Clock input (rising edge active)
//     i_rst_n:             Asynchronous active-low reset
//
//   Configuration (static during a transfer/descriptor):
//     i_cfg_base_addr:     Base address for this transfer
//     i_cfg_stride_0:      Signed byte stride for dimension 0 (inner)
//     i_cfg_stride_1:      Signed byte stride for dimension 1 (outer)
//     i_cfg_wrap_mask_0:   Wrap mask for dim 0 (0 = no wrap, else power-of-2 mask)
//     i_cfg_wrap_mask_1:   Wrap mask for dim 1 (0 = no wrap, else power-of-2 mask)
//
//   Request Interface:
//     i_req_valid:         Request valid
//     o_req_ready:         Ready to accept request
//     i_req_index_0:       Dimension 0 index (inner)
//     i_req_index_1:       Dimension 1 index (outer)
//     i_req_tag:           Pass-through tag (routing ID, channel, etc.)
//
//   Result Interface:
//     o_result_valid:      Result valid
//     i_result_ready:      Downstream ready
//     o_result_addr:       Calculated address
//     o_result_tag:        Pass-through tag from request
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:     2 cycles
//   Throughput:  1 address/cycle (when pipeline is full)
//   Clock-to-Q:  Single flip-flop delay on all outputs
//
//------------------------------------------------------------------------------
// Pipeline Structure:
//------------------------------------------------------------------------------
//   Stage 1: Multiply and wrap
//     - raw_offset_0 = index_0 * stride_0  (signed multiply)
//     - raw_offset_1 = index_1 * stride_1  (signed multiply)
//     - offset_0 = (wrap_mask_0 != 0) ? raw_offset_0 & wrap_mask_0 : raw_offset_0
//     - offset_1 = (wrap_mask_1 != 0) ? raw_offset_1 & wrap_mask_1 : raw_offset_1
//     - Register offsets, base address, and tag
//
//   Stage 2: Final address addition
//     - result_addr = base + offset_0 + offset_1
//     - Register final address and tag
//
//   Both stages support backpressure: if downstream stalls, upstream
//   stalls as well with no data loss.
//
//------------------------------------------------------------------------------
// Usage Examples:
//------------------------------------------------------------------------------
//
//   // Example 1: Linear 2D block transfer (64 rows x 128 elements, 4B each)
//   dma_address_gen #(.ADDR_WIDTH(40), .INDEX_WIDTH(16),
//                     .STRIDE_WIDTH(24), .TAG_WIDTH(8)
//   ) u_2d_xfer (
//       .i_clk(clk), .i_rst_n(rst_n),
//       .i_cfg_base_addr  (desc.base_addr),
//       .i_cfg_stride_0   (24'sd4),          // +4 bytes per element
//       .i_cfg_stride_1   (24'sd512),        // +512 bytes per row
//       .i_cfg_wrap_mask_0(24'd0),           // no wrap
//       .i_cfg_wrap_mask_1(24'd0),           // no wrap
//       // ... handshake signals ...
//   );
//
//   // Example 2: Circular audio ring buffer (4KB, 2B samples)
//   dma_address_gen #(.ADDR_WIDTH(40), .INDEX_WIDTH(16),
//                     .STRIDE_WIDTH(24), .TAG_WIDTH(8)
//   ) u_ring_buf (
//       .i_cfg_base_addr  (ring_base),
//       .i_cfg_stride_0   (24'sd2),          // +2 bytes per sample
//       .i_cfg_stride_1   (24'sd0),          // unused dimension
//       .i_cfg_wrap_mask_0(24'h0FFF),        // wrap at 4KB boundary
//       .i_cfg_wrap_mask_1(24'd0),           // no wrap
//       // ...
//   );
//
//   // Example 3: Reverse image scanline (walk backwards)
//   dma_address_gen #(.ADDR_WIDTH(40), .INDEX_WIDTH(16),
//                     .STRIDE_WIDTH(24), .TAG_WIDTH(8)
//   ) u_reverse (
//       .i_cfg_base_addr  (img_end_addr),
//       .i_cfg_stride_0   (-24'sd4),         // -4 bytes per pixel (reverse)
//       .i_cfg_stride_1   (-24'sd1920),      // -1920 bytes per row (bottom-up)
//       .i_cfg_wrap_mask_0(24'd0),
//       .i_cfg_wrap_mask_1(24'd0),
//       // ...
//   );
//
//==============================================================================

module dma_address_gen #(
    parameter int ADDR_WIDTH   = 40,
    parameter int INDEX_WIDTH  = 16,
    parameter int STRIDE_WIDTH = 24,
    parameter int TAG_WIDTH    = 8
) (
    input  logic                        i_clk,
    input  logic                        i_rst_n,

    // =========================================================================
    // Configuration (static during transfer, loaded from descriptor)
    //
    // IEEE 1800-2017 References:
    //   - Section 6.11, Table 6-8: Integer data types and signing
    //   - Section 6.11.1: Integral types (logic is 4-state integral)
    //   - Section 7.4.1: Packed arrays (packed dimension for vector width)
    //   - Section 23.2.2.1: ANSI-style port declarations
    //     Syntax: direction data_type [signing] {packed_dimension} identifier
    //
    // Signed stride ports use the canonical IEEE form:
    //   input logic signed [N-1:0] name
    //         ^     ^       ^
    //         |     |       packed_dimension (Section 7.4.1)
    //         |     signing (Section 6.11, Table 6-8)
    //         integer_vector_type (Section 6.11.1)
    //
    // PeakRDL / SystemRDL (IEEE 1800.2-2017) Integration:
    //   These configuration ports map directly to descriptor register fields.
    //   A SystemRDL register block can drive them via peakrdl-regblock output.
    //   See ../rdl/dma_address_gen.rdl for the register definition.
    //   Generated register block goes in ../rtl/generated/.
    // =========================================================================
    input  logic [ADDR_WIDTH-1:0]       i_cfg_base_addr,      // Descriptor field: base address
    input  logic signed [STRIDE_WIDTH-1:0] i_cfg_stride_0,    // Descriptor field: signed stride dim 0
    input  logic signed [STRIDE_WIDTH-1:0] i_cfg_stride_1,    // Descriptor field: signed stride dim 1
    input  logic [ADDR_WIDTH-1:0]       i_cfg_wrap_mask_0,    // Descriptor field: wrap mask dim 0 (0=no wrap)
    input  logic [ADDR_WIDTH-1:0]       i_cfg_wrap_mask_1,    // Descriptor field: wrap mask dim 1 (0=no wrap)

    // =========================================================================
    // Request Interface
    // =========================================================================
    input  logic                        i_req_valid,
    output logic                        o_req_ready,
    input  logic [INDEX_WIDTH-1:0]      i_req_index_0,        // Dimension 0 index
    input  logic [INDEX_WIDTH-1:0]      i_req_index_1,        // Dimension 1 index
    input  logic [TAG_WIDTH-1:0]        i_req_tag,            // Pass-through tag

    // =========================================================================
    // Result Interface
    // =========================================================================
    output logic                        o_result_valid,
    input  logic                        i_result_ready,
    output logic [ADDR_WIDTH-1:0]       o_result_addr,
    output logic [TAG_WIDTH-1:0]        o_result_tag
);

    // =========================================================================
    // Internal width for signed multiplication products
    // =========================================================================
    // index is unsigned, stride is signed, so the product is signed and
    // requires INDEX_WIDTH + STRIDE_WIDTH bits (index zero-extended to
    // INDEX_WIDTH+1 signed bits, then multiplied by STRIDE_WIDTH signed bits).
    localparam int PRODUCT_WIDTH = INDEX_WIDTH + STRIDE_WIDTH;

    // =========================================================================
    // Stage 1: Compute stride offsets (signed multiply + optional wrap)
    // =========================================================================
    //
    // Breaking the multiply + add into two stages allows meeting aggressive
    // timing targets. Stage 1 computes the two products and applies wrap
    // masks; Stage 2 does the final 3-input addition.
    // =========================================================================

    // Signed products: unsigned index sign-extended to signed, then multiplied
    logic signed [PRODUCT_WIDTH:0] w_s1_raw_offset_0;
    logic signed [PRODUCT_WIDTH:0] w_s1_raw_offset_1;

    assign w_s1_raw_offset_0 = $signed({1'b0, i_req_index_0}) * i_cfg_stride_0;
    assign w_s1_raw_offset_1 = $signed({1'b0, i_req_index_1}) * i_cfg_stride_1;

    // Apply wrap masks (power-of-2 wrap via bitwise AND on the offset)
    // Wrap constrains the offset magnitude, then the sign is preserved for
    // the final addition to base. When wrap_mask is 0, no wrapping occurs.
    logic [ADDR_WIDTH-1:0] w_s1_offset_0;
    logic [ADDR_WIDTH-1:0] w_s1_offset_1;

    always_comb begin
        if (i_cfg_wrap_mask_0 != '0)
            w_s1_offset_0 = ADDR_WIDTH'(w_s1_raw_offset_0) & i_cfg_wrap_mask_0;
        else
            w_s1_offset_0 = ADDR_WIDTH'(w_s1_raw_offset_0);
    end

    always_comb begin
        if (i_cfg_wrap_mask_1 != '0)
            w_s1_offset_1 = ADDR_WIDTH'(w_s1_raw_offset_1) & i_cfg_wrap_mask_1;
        else
            w_s1_offset_1 = ADDR_WIDTH'(w_s1_raw_offset_1);
    end

    // =========================================================================
    // Stage 1: Registered outputs
    // =========================================================================

    logic                        r_s1_valid;
    logic [ADDR_WIDTH-1:0]       r_s1_offset_0;
    logic [ADDR_WIDTH-1:0]       r_s1_offset_1;
    logic [ADDR_WIDTH-1:0]       r_s1_base_addr;
    logic [TAG_WIDTH-1:0]        r_s1_tag;

    // S1 ready when S1 is empty or S2 can accept
    logic w_s1_ready;
    logic w_s2_ready;

    assign w_s1_ready  = !r_s1_valid || w_s2_ready;
    assign o_req_ready = w_s1_ready;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_s1_valid     <= 1'b0;
            r_s1_offset_0  <= '0;
            r_s1_offset_1  <= '0;
            r_s1_base_addr <= '0;
            r_s1_tag       <= '0;
        end else begin
            if (i_req_valid && w_s1_ready) begin
                r_s1_valid     <= 1'b1;
                r_s1_offset_0  <= w_s1_offset_0;
                r_s1_offset_1  <= w_s1_offset_1;
                r_s1_base_addr <= i_cfg_base_addr;
                r_s1_tag       <= i_req_tag;
            end else if (w_s2_ready) begin
                r_s1_valid <= 1'b0;
            end
        end
    end

    // =========================================================================
    // Stage 2: Final address addition
    // =========================================================================
    // addr = base + offset_0 + offset_1
    // Offsets are already truncated/wrapped to ADDR_WIDTH in Stage 1, so
    // this is a simple unsigned addition (two's complement arithmetic handles
    // negative offsets correctly).
    // =========================================================================

    logic [ADDR_WIDTH-1:0] w_s2_addr;
    assign w_s2_addr = r_s1_base_addr + r_s1_offset_0 + r_s1_offset_1;

    // =========================================================================
    // Stage 2: Registered outputs (final output stage)
    // =========================================================================

    logic                        r_s2_valid;
    logic [ADDR_WIDTH-1:0]       r_s2_addr;
    logic [TAG_WIDTH-1:0]        r_s2_tag;

    assign w_s2_ready = !r_s2_valid || i_result_ready;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_s2_valid <= 1'b0;
            r_s2_addr  <= '0;
            r_s2_tag   <= '0;
        end else begin
            if (r_s1_valid && w_s2_ready) begin
                r_s2_valid <= 1'b1;
                r_s2_addr  <= w_s2_addr;
                r_s2_tag   <= r_s1_tag;
            end else if (i_result_ready) begin
                r_s2_valid <= 1'b0;
            end
        end
    end

    // =========================================================================
    // Output assignments
    // =========================================================================

    assign o_result_valid = r_s2_valid;
    assign o_result_addr  = r_s2_addr;
    assign o_result_tag   = r_s2_tag;

endmodule : dma_address_gen
