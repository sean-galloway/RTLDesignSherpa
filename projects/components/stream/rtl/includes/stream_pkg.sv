//////////////////////////////////////////////////////////////////////////////////
// Company:  Cornami, Inc.
//           Copyright (c) 2025 by Cornami, Inc. All rights reserved.
//
// Engineer: STREAM RTL v1.0
//
// Package Name  : stream_pkg
// Project Name  : STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
// Target Devices: ASIC/FPGA
// Tool versions : Verilator compatible
// Description   : STREAM Common Types Package
//                 - Simplified memory-to-memory DMA with scatter-gather support
//                 - Descriptor-based operation with chaining (no circular buffers)
//                 - Aligned addresses only (tutorial-friendly)
//                 - 8 independent channels maximum
//
//////////////////////////////////////////////////////////////////////////////////

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
    //       [193]     - interrupt: Generate interrupt on completion
    //       [194]     - last: Last descriptor in chain
    //       [195]     - error: Error flag (used for status)
    //       [199:196] - channel_id: Channel ID (INFORMATIONAL ONLY - for MonBus/debug)
    //       [207:200] - priority: Transfer priority
    //       [255:208] - reserved: Reserved for future use
    //
    // NOTE: Channel selection is determined by APB register address, NOT by channel_id field.
    //       Writing to CHx_CTRL APB register implicitly selects that channel.
    //       The channel_id field is for monitoring/logging purposes only.

    typedef struct packed {
        logic [63:0]  reserved;              // [255:192] Reserved
        logic [7:0]   priority;              // [207:200] Priority
        logic [3:0]   channel_id;            // [199:196] Channel ID (informational only)
        logic         error;                 // [195] Error flag
        logic         last;                  // [194] Last in chain
        logic         interrupt;             // [193] Generate interrupt
        logic         valid;                 // [192] Valid descriptor
        logic [31:0]  next_descriptor_ptr;   // [191:160] Next descriptor address
        logic [31:0]  length;                // [159:128] Length in BEATS
        logic [63:0]  dst_addr;              // [127:64] Destination address
        logic [63:0]  src_addr;              // [63:0] Source address
    } descriptor_t;

    // Descriptor size in bits
    parameter int STREAM_DESCRIPTOR_WIDTH = 256;

    //=========================================================================
    // Channel State Enumeration
    //=========================================================================
    typedef enum logic [3:0] {
        CH_IDLE         = 4'h0,  // Channel idle, waiting for descriptor
        CH_FETCH_DESC   = 4'h1,  // Fetching descriptor from memory
        CH_READ_DATA    = 4'h2,  // Reading source data
        CH_WRITE_DATA   = 4'h3,  // Writing destination data
        CH_COMPLETE     = 4'h4,  // Transfer complete
        CH_NEXT_DESC    = 4'h5,  // Fetching next chained descriptor
        CH_ERROR        = 4'hF   // Error state
    } channel_state_t;

    //=========================================================================
    // Scheduler State Enumeration (Simplified from RAPIDS)
    //=========================================================================
    typedef enum logic [7:0] {
        SCHED_IDLE              = 8'b00000001,  // Idle, waiting for channel activation
        SCHED_FETCH_DESCRIPTOR  = 8'b00000010,  // Fetch descriptor via AXI master
        SCHED_PARSE_DESCRIPTOR  = 8'b00000100,  // Parse descriptor fields
        SCHED_READ_PHASE        = 8'b00001000,  // Coordinate read engine
        SCHED_WRITE_PHASE       = 8'b00010000,  // Coordinate write engine
        SCHED_CHAIN_CHECK       = 8'b00100000,  // Check for next descriptor
        SCHED_COMPLETE          = 8'b01000000,  // Transfer complete, report status
        SCHED_ERROR             = 8'b10000000   // Error state
    } scheduler_state_t;

    //=========================================================================
    // AXI Read Engine State (Simplified)
    //=========================================================================
    typedef enum logic [2:0] {
        RD_IDLE       = 3'b000,  // Idle, waiting for request
        RD_ISSUE_ADDR = 3'b001,  // Issue read address on AR channel
        RD_WAIT_DATA  = 3'b010,  // Wait for data on R channel
        RD_WRITE_SRAM = 3'b011,  // Write data to SRAM buffer
        RD_COMPLETE   = 3'b100,  // Read complete
        RD_ERROR      = 3'b111   // Error state
    } read_engine_state_t;

    //=========================================================================
    // AXI Write Engine State (Simplified)
    //=========================================================================
    typedef enum logic [2:0] {
        WR_IDLE       = 3'b000,  // Idle, waiting for request
        WR_READ_SRAM  = 3'b001,  // Read data from SRAM buffer
        WR_ISSUE_ADDR = 3'b010,  // Issue write address on AW channel
        WR_ISSUE_DATA = 3'b011,  // Issue write data on W channel
        WR_WAIT_RESP  = 3'b100,  // Wait for response on B channel
        WR_COMPLETE   = 3'b101,  // Write complete
        WR_ERROR      = 3'b111   // Error state
    } write_engine_state_t;

    //=========================================================================
    // Channel Status Structure
    //=========================================================================
    typedef struct packed {
        logic                    active;               // Channel is active
        logic                    ready;                // Channel ready for transfers
        logic                    error;                // Channel in error state
        logic [7:0]              used_count;           // SRAM buffer used count
        logic [7:0]              available_count;      // SRAM buffer available count
        logic [31:0]             bytes_transferred;    // Total bytes transferred
        logic [15:0]             transfers_completed;  // Number of descriptors completed
        channel_state_t          state;                // Current channel state
    } channel_status_t;

    //=========================================================================
    // MonBus Event Types (STREAM-specific)
    //=========================================================================
    // Uses standard 64-bit MonBus format from monitor_pkg
    // Event codes for STREAM operations:
    parameter logic [3:0] STREAM_EVENT_DESC_START    = 4'h0;  // Descriptor started
    parameter logic [3:0] STREAM_EVENT_DESC_COMPLETE = 4'h1;  // Descriptor completed
    parameter logic [3:0] STREAM_EVENT_READ_START    = 4'h2;  // Read phase started
    parameter logic [3:0] STREAM_EVENT_READ_COMPLETE = 4'h3;  // Read phase completed
    parameter logic [3:0] STREAM_EVENT_WRITE_START   = 4'h4;  // Write phase started
    parameter logic [3:0] STREAM_EVENT_WRITE_COMPLETE = 4'h5; // Write phase completed
    parameter logic [3:0] STREAM_EVENT_CHAIN_FETCH   = 4'h6;  // Chained descriptor fetch
    parameter logic [3:0] STREAM_EVENT_ERROR         = 4'hF;  // Error occurred

    //=========================================================================
    // Utility Functions (Simplified from RAPIDS)
    //=========================================================================

    // Calculate number of AXI bursts needed for given beat count
    function automatic logic [15:0] beats_to_bursts(
        input logic [31:0] beats,
        input logic [7:0]  burst_len
    );
        if (burst_len == 0) return 16'h0;
        return 16'((beats + {24'h0, burst_len} - 32'd1) / {24'h0, burst_len});
    endfunction

    // Calculate bytes for given number of beats
    function automatic logic [31:0] beats_to_bytes(
        input logic [31:0] beats,
        input logic [15:0] data_width_bytes
    );
        return beats * {16'h0, data_width_bytes};
    endfunction

    // Check if address is aligned to data width
    function automatic logic is_address_aligned(
        input logic [63:0] address,
        input logic [5:0]  align_bits
    );
        return (address[align_bits-1:0] == '0);
    endfunction

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
        return desc.interrupt;
    endfunction

    // Validate descriptor
    function automatic logic is_valid_desc(input descriptor_t desc);
        return desc.valid;
    endfunction

endpackage : stream_pkg
