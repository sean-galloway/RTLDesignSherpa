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
    //       [255:208] - reserved: Reserved for future use
    //
    // NOTE: Channel selection is determined by APB register address, NOT by channel_id field.
    //       Writing to CHx_CTRL APB register implicitly selects that channel.
    //       The channel_id field is for monitoring/logging purposes only.

    typedef struct packed {
        logic [63:0]  reserved;              // [255:192] Reserved
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

    // Descriptor size in bits
    parameter int STREAM_DESCRIPTOR_WIDTH = 256;

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
    // Uses standard 64-bit MonBus format from monitor_pkg
    // Event codes for STREAM operations:
    parameter logic [3:0] STREAM_EVENT_DESC_START     = 4'h0;  // Descriptor started
    parameter logic [3:0] STREAM_EVENT_DESC_COMPLETE  = 4'h1;  // Descriptor completed
    parameter logic [3:0] STREAM_EVENT_READ_START     = 4'h2;  // Read phase started
    parameter logic [3:0] STREAM_EVENT_READ_COMPLETE  = 4'h3;  // Read phase completed
    parameter logic [3:0] STREAM_EVENT_WRITE_START    = 4'h4;  // Write phase started
    parameter logic [3:0] STREAM_EVENT_WRITE_COMPLETE = 4'h5;  // Write phase completed
    parameter logic [3:0] STREAM_EVENT_CHAIN_FETCH    = 4'h6;  // Chained descriptor fetch
    parameter logic [3:0] STREAM_EVENT_IRQ            = 4'h7;  // Interrupt request generated
    parameter logic [3:0] STREAM_EVENT_ERROR          = 4'hF;  // Error occurred

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

endpackage : stream_pkg
