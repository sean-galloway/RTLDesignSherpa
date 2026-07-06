// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_pkg
// Purpose: Stream Pkg module
//
// Documentation: projects/components/includes/PRD.md
// Subsystem: includes
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

package stream_pkg;

    //=========================================================================
    // STREAM Constants
    //=========================================================================

    // Maximum channels
    parameter int STREAM_MAX_CHANNELS = 8;

    // Data width defaults (parameterizable at instantiation)
    parameter int STREAM_ADDR_WIDTH = 64;
    parameter int STREAM_DATA_WIDTH = 512;
    parameter int STREAM_STRB_WIDTH = STREAM_DATA_WIDTH / 8;

    // AXI configuration
    parameter int STREAM_MAX_BURST_LEN = 256;    // AXI4 max burst length
    parameter int STREAM_DEFAULT_BURST = 16;     // Default burst for streaming

    // Descriptor configuration
    parameter int STREAM_MAX_DESCRIPTORS = 16;   // Max descriptors per channel

    //=========================================================================
    // Descriptor Structure
    //=========================================================================
    // Format: 256-bit descriptor (4 x 64-bit words)
    //   [63:0]    - src_addr: Source address (64-bit, must be aligned to data width)
    //   [127:64]  - dst_addr: Destination address (64-bit, must be aligned to data width)
    //   [159:128] - length: Transfer length in BEATS (not bytes)
    //   [191:160] - next_descriptor_ptr: Address of next descriptor (0 = last)
    //   [255:192] - control: Control bits
    //       [192]     - valid: Descriptor is valid
    //       [193]     - gen_irq: Generate interrupt on completion
    //       [194]     - last: Last descriptor in chain
    //       [195]     - error: Error flag (used for status)
    //       [199:196] - channel_id: Channel ID (INFORMATIONAL ONLY - for MonBus/debug)
    //       [207:200] - desc_priority: Transfer priority
    //       [210:208] - desc_type: Descriptor type (0 = legacy 256b; 1 = extended 512b) [TASK-101]
    //       [255:211] - reserved: Reserved for future use
    //
    // NOTE: Channel selection is determined by APB register address, NOT by channel_id field.
    //       Writing to CHx_CTRL APB register implicitly selects that channel.
    //       The channel_id field is for monitoring/logging purposes only.

    //=========================================================================
    // Descriptor Type (TASK-101, STREAM Extended)
    //=========================================================================
    // Selects legacy linear addressing vs dma_address_gen-driven addressing,
    // and (equivalently) the physical descriptor length. Lives in bits [210:208]
    // of chunk 0 (carved from the former reserved field). DESC_TYPE_LEGACY = 0
    // so legacy descriptors (reserved = 0) decode to today's behavior verbatim.
    //   LEGACY: 256-bit descriptor, 1 chunk,  linear address accumulation
    //   EXT:    512-bit descriptor, 2 chunks, per-direction dma_address_gen cfg
    // Only meaningful when the scheduler is built with
    // USE_ROW_COL_MAJOR_ADDRESSING = 1; with the param = 0 the hardware is
    // legacy-only and this field is ignored.
    typedef enum logic [2:0] {
        DESC_TYPE_LEGACY = 3'd0,  // 256-bit, 1 chunk, linear addressing
        DESC_TYPE_EXT    = 3'd1   // 512-bit, 2 chunks, dma_address_gen addressing
        // 3'd2 .. 3'd7 reserved for future descriptor formats
    } desc_type_e;

    // Chunk 0 (bits [255:0]) - legacy layout, byte-identical to the original
    // 256-bit descriptor except that reserved[2:0] is now named desc_type.
    typedef struct packed {
        logic [60:0]  reserved;              // [271:211] Reserved (top 16 = struct pad)
        desc_type_e   desc_type;             // [210:208] Descriptor type (0 = legacy)
        logic [7:0]   desc_priority;         // [207:200] Transfer priority
        logic [3:0]   channel_id;            // [199:196] Channel ID (informational only)
        logic         error;                 // [195] Error flag
        logic         last;                  // [194] Last in chain
        logic         gen_irq;               // [193] Generate interrupt
        logic         valid;                 // [192] Valid descriptor
        logic [31:0]  next_descriptor_ptr;   // [191:160] Next descriptor address
        logic [31:0]  length;                // [159:128] Length in BEATS
        logic [63:0]  dst_addr;              // [127:64] Destination address
        logic [63:0]  src_addr;              // [63:0] Source address
    } descriptor_t;

    // Chunk 1 (bits [511:256]) - extended addr-gen cfg, present only when
    // desc_type == DESC_TYPE_EXT. Independent read/write cfg is what enables
    // transpose (row-major read <-> col-major write) and independent
    // gather/scatter. Strides are signed byte strides; wrap fields are log2 of
    // the circular window (0 = no wrap) which the scheduler expands to a
    // (2^n - 1) mask before driving dma_address_gen.
    typedef struct packed {
        logic [63:0]        reserved_hi;     // [511:448] future: 3rd dim / elem-size
        logic [3:0]         wr_reserved;     // [447:444]
        logic [5:0]         wr_wrap1_log2;   // [443:438]
        logic [5:0]         wr_wrap0_log2;   // [437:432]
        logic [15:0]        wr_inner_count;  // [431:416] index_0 extent (beats/row)
        logic signed [31:0] wr_stride_1;     // [415:384] signed byte stride (outer)
        logic signed [31:0] wr_stride_0;     // [383:352] signed byte stride (inner)
        logic [3:0]         rd_reserved;     // [351:348]
        logic [5:0]         rd_wrap1_log2;   // [347:342]
        logic [5:0]         rd_wrap0_log2;   // [341:336]
        logic [15:0]        rd_inner_count;  // [335:320] index_0 extent (beats/row)
        logic signed [31:0] rd_stride_1;     // [319:288] signed byte stride (outer)
        logic signed [31:0] rd_stride_0;     // [287:256] signed byte stride (inner)
    } descriptor_ext_t;

    // Descriptor sizes in bits
    parameter int STREAM_DESCRIPTOR_WIDTH     = 256;  // chunk 0 (legacy)
    parameter int STREAM_DESCRIPTOR_EXT_WIDTH = 512;  // chunk 0 + chunk 1 (extended)

    // dma_address_gen instantiation widths used by the STREAM scheduler
    // (match the extended descriptor's stride / index field widths).
    parameter int STREAM_ADDRGEN_STRIDE_WIDTH = 32;   // signed byte stride
    parameter int STREAM_ADDRGEN_INDEX_WIDTH  = 16;   // inner_count extent

    //=========================================================================
    // Channel State Enumeration (ONE-HOT ENCODED)
    //=========================================================================
    // CRITICAL: CH_XFER_DATA runs read and write engines CONCURRENTLY
    //           to prevent deadlock when transfer size > SRAM buffer size
    typedef enum logic [6:0] {
        CH_IDLE         = 7'b0000001,  // [0] Channel idle, waiting for descriptor
        CH_FETCH_DESC   = 7'b0000010,  // [1] Fetching descriptor from memory
        CH_XFER_DATA    = 7'b0000100,  // [2] Concurrent read AND write transfer
        CH_COMPLETE     = 7'b0001000,  // [3] Transfer complete
        CH_NEXT_DESC    = 7'b0010000,  // [4] Fetching next chained descriptor
        CH_ERROR        = 7'b0100000,  // [5] Error state
        CH_RESERVED     = 7'b1000000   // [6] Reserved for future use
    } channel_state_t;

    //=========================================================================
    // Descriptor Engine State Enumeration (Control Path FSM)
    //=========================================================================
    // Descriptor engine FSM for fetching descriptors via AXI
    // This is a CONTROL PATH module (not data path), so FSM is appropriate
    typedef enum logic [2:0] {
        RD_IDLE         = 3'b000,  // Waiting for descriptor address
        RD_ISSUE_ADDR   = 3'b001,  // Issue AXI AR for descriptor fetch
        RD_WAIT_DATA    = 3'b010,  // Wait for AXI R response
        RD_COMPLETE     = 3'b011,  // Descriptor fetched successfully
        RD_ERROR        = 3'b100   // AXI error response
    } read_engine_state_t;

    //=========================================================================
    // MonBus Event Types (STREAM-specific)
    //=========================================================================
    // Uses standard 128-bit MonBus format from monitor_common_pkg
    // (event_code field is 8 bits at [104:97]).
    parameter logic [7:0] STREAM_EVENT_DESC_START     = 8'h00;  // Descriptor started
    parameter logic [7:0] STREAM_EVENT_DESC_COMPLETE  = 8'h01;  // Descriptor completed
    parameter logic [7:0] STREAM_EVENT_READ_START     = 8'h02;  // Read phase started
    parameter logic [7:0] STREAM_EVENT_READ_COMPLETE  = 8'h03;  // Read phase completed
    parameter logic [7:0] STREAM_EVENT_WRITE_START    = 8'h04;  // Write phase started
    parameter logic [7:0] STREAM_EVENT_WRITE_COMPLETE = 8'h05;  // Write phase completed
    parameter logic [7:0] STREAM_EVENT_CHAIN_FETCH    = 8'h06;  // Chained descriptor fetch
    parameter logic [7:0] STREAM_EVENT_IRQ            = 8'h07;  // Interrupt request generated
    parameter logic [7:0] STREAM_EVENT_ERROR          = 8'h0F;  // Error occurred

    //=========================================================================
    // Descriptor Helper Functions
    //=========================================================================

    // Extract source address from descriptor
    function automatic logic [63:0] get_src_addr(input descriptor_t desc);
        return desc.src_addr;
    endfunction

    // Extract destination address from descriptor
    function automatic logic [63:0] get_dst_addr(input descriptor_t desc);
        return desc.dst_addr;
    endfunction

    // Extract transfer length (in beats) from descriptor
    function automatic logic [31:0] get_length(input descriptor_t desc);
        return desc.length;
    endfunction

    // Extract next descriptor pointer
    function automatic logic [31:0] get_next_desc_ptr(input descriptor_t desc);
        return desc.next_descriptor_ptr;
    endfunction

    // Check if descriptor is last in chain
    function automatic logic is_last_desc(input descriptor_t desc);
        return desc.last || (desc.next_descriptor_ptr == 32'h0);
    endfunction

    // Check if descriptor requests interrupt
    function automatic logic needs_interrupt(input descriptor_t desc);
        return desc.gen_irq;
    endfunction

    // Validate descriptor
    function automatic logic is_valid_desc(input descriptor_t desc);
        return desc.valid;
    endfunction

    //=========================================================================
    // Extended Descriptor Helper Functions (TASK-101)
    //=========================================================================

    // Extract descriptor type from chunk 0
    function automatic desc_type_e get_desc_type(input descriptor_t desc);
        return desc.desc_type;
    endfunction

    // Is this an extended (512-bit, 2-chunk) descriptor?
    function automatic logic is_extended_desc(input descriptor_t desc);
        return (desc.desc_type == DESC_TYPE_EXT);
    endfunction

    // Expand a log2-encoded circular-window size into a dma_address_gen wrap
    // mask. wrap_log2 == 0 means "no wrap" (full range) -> mask 0. Otherwise
    // the mask is (2^wrap_log2 - 1), constraining the offset to a power-of-2
    // region via bitwise AND inside dma_address_gen.
    function automatic logic [STREAM_ADDRGEN_STRIDE_WIDTH-1:0]
            wrap_log2_to_mask(input logic [5:0] wrap_log2);
        return (wrap_log2 == 6'd0) ? '0
            : (STREAM_ADDRGEN_STRIDE_WIDTH'((1 << wrap_log2) - 1));
    endfunction

endpackage : stream_pkg
