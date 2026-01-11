// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_pkg
// Purpose: Rapids Pkg module
//
// Documentation: projects/components/includes/PRD.md
// Subsystem: includes
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

package rapids_pkg;

    //=========================================================================
    // Common RAPIDS Constants
    //=========================================================================

    // Standard data widths
    parameter int RAPIDS_DATA_WIDTH = 512;
    parameter int RAPIDS_NUM_CHUNKS = 16;            // 512 bits ÷ 32 bits = 16 chunks
    parameter int RAPIDS_CHUNK_SIZE = 32;            // bits per chunk (4 bytes)
    parameter int RAPIDS_BYTES_PER_BEAT = 64;        // 512 bits ÷ 8 = 64 bytes
    parameter int RAPIDS_CHUNKS_PER_BEAT = 16;       // 64 bytes ÷ 4 bytes = 16 chunks

    // Address alignment
    parameter int RAPIDS_ALIGNMENT_BOUNDARY = 64;    // bytes - optimal alignment boundary
    parameter int RAPIDS_ADDR_OFFSET_BITS = 6;       // log2(64) - for 64B boundary checks

    // Transfer limits
    parameter int RAPIDS_MAX_BURST_LEN = 64;
    parameter int RAPIDS_MAX_CHANNELS = 32;
    parameter int RAPIDS_MAX_TRANSFER_BYTES = 32'hFFFF_FFFF;

    //=========================================================================
    // Descriptor Structure (256-bit - same as STREAM for Phase 1)
    //=========================================================================
    // Format: 256-bit descriptor (4 x 64-bit words)
    //   [63:0]    - src_addr: Source address (64-bit, must be aligned to data width)
    //   [127:64]  - dst_addr: Destination address (64-bit, must be aligned to data width)
    //   [159:128] - length: Transfer length in BEATS (not bytes)
    //   [191:160] - next_descriptor_ptr: Address of next descriptor (0 = last)
    //   [255:192] - control: Control bits

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

    //=========================================================================
    // Channel State Enumeration (ONE-HOT ENCODED - for Phase 1 scheduler)
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
    // Descriptor Fetch FSM States (for descriptor_engine)
    //=========================================================================
    // Used by descriptor_engine to fetch descriptors via AXI read
    typedef enum logic [2:0] {
        RD_IDLE       = 3'b000,  // Waiting for descriptor address in FIFO
        RD_ISSUE_ADDR = 3'b001,  // Issue AXI AR transaction
        RD_WAIT_DATA  = 3'b010,  // Wait for AXI R response
        RD_COMPLETE   = 3'b011,  // Descriptor fetched successfully
        RD_ERROR      = 3'b100   // AXI response error
    } desc_fetch_state_t;

    //=========================================================================
    // MonBus Event Types (RAPIDS-specific)
    //=========================================================================
    // NOTE: PktType* and PROTOCOL_* constants are imported from monitor_common_pkg
    // via rapids_imports.svh. Do NOT redefine them here to avoid conflicts.
    // Uses standard 64-bit MonBus format from monitor_pkg
    parameter logic [3:0] RAPIDS_EVENT_DESC_START     = 4'h0;  // Descriptor started
    parameter logic [3:0] RAPIDS_EVENT_DESC_COMPLETE  = 4'h1;  // Descriptor completed
    parameter logic [3:0] RAPIDS_EVENT_READ_START     = 4'h2;  // Read phase started
    parameter logic [3:0] RAPIDS_EVENT_READ_COMPLETE  = 4'h3;  // Read phase completed
    parameter logic [3:0] RAPIDS_EVENT_WRITE_START    = 4'h4;  // Write phase started
    parameter logic [3:0] RAPIDS_EVENT_WRITE_COMPLETE = 4'h5;  // Write phase completed
    parameter logic [3:0] RAPIDS_EVENT_CHAIN_FETCH    = 4'h6;  // Chained descriptor fetch
    parameter logic [3:0] RAPIDS_EVENT_IRQ            = 4'h7;  // Interrupt request generated
    parameter logic [3:0] RAPIDS_EVENT_ERROR          = 4'hF;  // Error occurred

    //=========================================================================
    // Transfer Phase Enumeration
    //=========================================================================

    typedef enum logic [2:0] {
        PHASE_IDLE      = 3'h0,  // No active transfer
        PHASE_ALIGNMENT = 3'h1,  // Initial alignment transfer (to reach 64B boundary)
        PHASE_STREAMING = 3'h2,  // Optimal aligned streaming transfers (64B each)
        PHASE_FINAL     = 3'h3,  // Final partial transfer (remaining < 64B)
        PHASE_SINGLE    = 3'h4,  // Single transfer (fits entirely in one or few beats)
        PHASE_ERROR     = 3'h7   // Error state
    } transfer_phase_t;

    //=========================================================================
    // Alignment Strategy Enumeration
    //=========================================================================

    typedef enum logic [2:0] {
        ALIGN_STRAT_SINGLE    = 3'h0,  // Single transfer, no alignment needed
        ALIGN_STRAT_ALIGNED   = 3'h1,  // Already aligned, optimal transfers
        ALIGN_STRAT_PRECISION = 3'h2,  // Precise alignment with all phases
        ALIGN_STRAT_FORCED    = 3'h3,  // Force single beat transfers
        ALIGN_STRAT_STREAM    = 3'h4,  // Streaming optimized
        ALIGN_STRAT_ERROR     = 3'h7   // Invalid strategy
    } alignment_strategy_t;

    //=========================================================================
    // Address Alignment Information Structure - FIXED: Added missing members
    //=========================================================================

    typedef struct packed {
        // Basic Alignment Information
        logic                    is_aligned;           // Address is already 64-byte aligned
        logic [5:0]              addr_offset;          // Offset within 64-byte boundary (BYTES)
        alignment_strategy_t     alignment_strategy;   // Strategy code

        // First Transfer (Alignment Phase) - BYTE VALUES for AXI calculations
        logic                    requires_alignment;   // Needs initial alignment transfer
        logic [31:0]             first_transfer_bytes; // Bytes in alignment transfer (BYTES not chunks)
        logic [RAPIDS_NUM_CHUNKS-1:0] first_chunk_enables;  // Chunk pattern for alignment (16-bit mask)
        logic [3:0]              first_start_chunk;    // Starting chunk index (0-15)
        logic [3:0]              first_valid_chunks;   // Number of valid chunks (count)

        // Streaming Phase (Post-Alignment) - BYTE VALUES for AXI calculations
        logic                    has_streaming_phase;  // Has optimal streaming transfers
        logic [7:0]              optimal_burst_len;    // Optimal burst length (AXI beats)
        logic [31:0]             streaming_bytes;      // Total bytes in streaming (BYTES)
        logic [RAPIDS_NUM_CHUNKS-1:0] streaming_chunk_enables; // Always all 1's for streaming

        // Final Transfer (Remainder Phase) - BYTE VALUES for AXI calculations
        logic                    has_final_partial;    // Has final partial transfer
        logic [31:0]             final_transfer_bytes; // Bytes in final transfer (BYTES not chunks)
        logic [RAPIDS_NUM_CHUNKS-1:0] final_chunk_enables;  // Chunk pattern for final (16-bit mask)
        logic [3:0]              final_start_chunk;    // FIXED: Added missing member
        logic [3:0]              final_valid_chunks;   // Number of valid chunks in final (count)

        // Transfer Sequence Planning
        logic [3:0]              total_transfers;      // Total AXI transfers needed (count)
        logic [1:0]              sequence_type;        // Transfer sequence type

        // Performance Optimization - BYTE VALUES for efficiency calculations
        logic [7:0]              max_burst_efficiency; // Efficiency percentage (0-100)
        logic [31:0]             total_axi_bytes;      // Total bytes across AXI transfers (BYTES)
        logic [31:0]             payload_bytes;        // Actual payload bytes (BYTES, from chunks×4)

        // Stream Boundary Integration
        logic                    eos_in_alignment;     // EOS in alignment phase
        logic                    eos_in_streaming;     // EOS in streaming phase
        logic                    eos_in_final;         // EOS in final phase
        logic [1:0]              eos_phase;            // Which phase contains EOS
    } alignment_info_t;

    //=========================================================================
    // Common Utility Functions - FIXED: Proper Width Handling
    //=========================================================================

    // Calculate number of 4-byte chunks needed for given byte count
    function automatic logic [3:0] bytes_to_chunks(input logic [31:0] bytes);
        /* verilator lint_off WIDTHTRUNC */
        return 4'((bytes + 32'd3) >> 2);  // FIXED: Explicit 4-bit cast
        /* verilator lint_on WIDTHTRUNC */
    endfunction

    // Calculate number of 64-byte beats needed for given byte count
    function automatic logic [7:0] bytes_to_beats(input logic [31:0] bytes);
        /* verilator lint_off WIDTHTRUNC */
        return 8'((bytes + 32'd63) >> 6);  // FIXED: Explicit 8-bit cast
        /* verilator lint_on WIDTHTRUNC */
    endfunction

    // Convert 4-byte chunks to bytes
    function automatic logic [31:0] chunks_to_bytes(input logic [31:0] chunks);
        return chunks << 2;  // Multiply by 4
    endfunction

    // Calculate AXI beats for HBM3e optimized transfer sizes
    // cfg_transfer_size: 0=256B, 1=512B, 2=1K, 3=2K, 4=4K
    function automatic logic [7:0] calc_transfer_size_beats(input logic [2:0] cfg_transfer_size);
        case (cfg_transfer_size)
            3'h0: return 8'd4;   // 256B = 4 beats of 64B
            3'h1: return 8'd8;   // 512B = 8 beats of 64B
            3'h2: return 8'd16;  // 1KB = 16 beats of 64B
            3'h3: return 8'd32;  // 2KB = 32 beats of 64B
            3'h4: return 8'd64;  // 4KB = 64 beats of 64B
            default: return 8'd8; // Default to 512B
        endcase
    endfunction

    // Convert 4-byte chunks to 64-byte beats (for optimal transfers)
    function automatic logic [7:0] chunks_to_beats(input logic [31:0] chunks);
        /* verilator lint_off WIDTHTRUNC */
        return 8'((chunks + 32'd15) >> 4);  // FIXED: Explicit 8-bit cast
        /* verilator lint_on WIDTHTRUNC */
    endfunction

    // Check if address is aligned to 64-byte boundary
    function automatic logic is_address_aligned(input logic [63:0] address);
        return (address[5:0] == 6'h0);
    endfunction

    // Get address offset within 64-byte boundary
    function automatic logic [5:0] get_address_offset(input logic [63:0] address);
        return address[5:0];
    endfunction

    // Calculate bytes to next 64-byte boundary - FIXED: Width issues
    function automatic logic [5:0] bytes_to_boundary(input logic [63:0] address);
        logic [5:0] offset = get_address_offset(address);
        /* verilator lint_off WIDTHTRUNC */
        return (offset == 6'h0) ? 6'h0 : 6'(7'd64 - {1'b0, offset});  // FIXED: Use 7-bit intermediate
        /* verilator lint_on WIDTHTRUNC */
    endfunction

    // Calculate 4-byte chunks to next 64-byte boundary - FIXED: Width handling
    function automatic logic [3:0] chunks_to_boundary(input logic [63:0] address);
        logic [5:0] byte_offset = get_address_offset(address);
        logic [5:0] bytes_to_align;
        /* verilator lint_off WIDTHTRUNC */
        bytes_to_align = (byte_offset == 6'h0) ? 6'h0 : 6'(7'd64 - {1'b0, byte_offset});  // FIXED: Use 7-bit intermediate
        /* verilator lint_on WIDTHTRUNC */
        /* verilator lint_off WIDTHEXPAND */
        return bytes_to_chunks({26'h0, bytes_to_align});  // FIXED: Expand to 32 bits
        /* verilator lint_on WIDTHEXPAND */
    endfunction

    // Generate chunk enable mask for partial transfers - FIXED: Width expansion
    function automatic logic [RAPIDS_NUM_CHUNKS-1:0] generate_chunk_enables(
        input logic [3:0] start_chunk,
        input logic [3:0] num_chunks
    );
        logic [RAPIDS_NUM_CHUNKS-1:0] mask = '0;
        for (int i = 0; i < RAPIDS_NUM_CHUNKS; i++) begin
            /* verilator lint_off WIDTHEXPAND */
            if ((i >= {28'h0, start_chunk}) && (i < ({28'h0, start_chunk} + {28'h0, num_chunks}))) begin
            /* verilator lint_on WIDTHEXPAND */
                mask[i] = 1'b1;
            end
        end
        return mask;
    endfunction

    // Calculate transfer efficiency percentage - FIXED: Width truncation
    function automatic logic [7:0] calculate_efficiency(
        input logic [31:0] payload_bytes,
        input logic [31:0] total_axi_bytes
    );
        if (total_axi_bytes == 0) return 8'h0;
        /* verilator lint_off WIDTHTRUNC */
        return 8'((payload_bytes * 32'd100) / total_axi_bytes);  // FIXED: Explicit 8-bit cast
        /* verilator lint_on WIDTHTRUNC */
    endfunction

    //=========================================================================
    // Alignment Strategy Selection Function - FIXED: Width expansion
    //=========================================================================

    function automatic alignment_strategy_t select_alignment_strategy(
        input logic [63:0] address,
        input logic [31:0] length,         // 4-BYTE CHUNKS
        input logic force_single_beat,
        input logic enable_streaming
    );
        logic is_aligned = is_address_aligned(address);
        logic [5:0] offset = get_address_offset(address);
        logic [5:0] bytes_to_align = bytes_to_boundary(address);
        logic [31:0] length_in_bytes = chunks_to_bytes(length);  // Convert chunks to bytes

        if (force_single_beat) begin
            return ALIGN_STRAT_FORCED;
        end else if (length_in_bytes <= 32'd64) begin  // ≤ 64 bytes (16 chunks)
            return ALIGN_STRAT_SINGLE;
        end else if (is_aligned) begin
            return enable_streaming ? ALIGN_STRAT_STREAM : ALIGN_STRAT_ALIGNED;
        end else begin
            return ALIGN_STRAT_PRECISION;
        end
    endfunction

    //=========================================================================
    // Enhanced Alignment Calculation Function - FIXED: All width issues
    //=========================================================================

    function automatic alignment_info_t calculate_alignment_info(
        input logic [63:0] address,
        input logic [31:0] length,         // 4-BYTE CHUNKS
        input logic enable_streaming
    );
        alignment_info_t info;
        logic [31:0] length_in_bytes;
        logic [5:0] addr_offset;
        logic [5:0] bytes_to_align;
        logic [31:0] first_transfer_bytes;
        logic [31:0] remaining_bytes;
        logic [31:0] streaming_bytes;
        logic [31:0] final_bytes;

        // Initialize structure
        info = '0;

        // Convert length from chunks to bytes for calculations
        length_in_bytes = chunks_to_bytes(length);

        // Basic alignment analysis
        info.is_aligned = is_address_aligned(address);
        info.addr_offset = get_address_offset(address);
        addr_offset = info.addr_offset;
        bytes_to_align = bytes_to_boundary(address);

        // Select strategy
        info.alignment_strategy = select_alignment_strategy(address, length, 1'b0, enable_streaming);

        // Calculate transfer phases
        case (info.alignment_strategy)
            ALIGN_STRAT_SINGLE: begin
                // Single transfer handles everything
                info.requires_alignment = 1'b0;
                info.has_streaming_phase = 1'b0;
                info.has_final_partial = 1'b1;
                info.final_transfer_bytes = length_in_bytes;
                info.final_start_chunk = addr_offset[5:2];  // Starting chunk
                info.final_valid_chunks = bytes_to_chunks(length_in_bytes);
                /* verilator lint_off WIDTHEXPAND */
                info.final_chunk_enables = generate_chunk_enables(
                    4'(addr_offset[5:2]), info.final_valid_chunks);  // FIXED: Explicit 4-bit cast
                /* verilator lint_on WIDTHEXPAND */
            end

            ALIGN_STRAT_ALIGNED, ALIGN_STRAT_STREAM: begin
                // Already aligned - streaming optimization
                info.requires_alignment = 1'b0;
                if (length_in_bytes > 32'd64) begin
                    info.has_streaming_phase = 1'b1;
                    streaming_bytes = (length_in_bytes >> 6) << 6;  // Round down to 64B multiple
                    info.streaming_bytes = streaming_bytes;
                    info.optimal_burst_len = chunks_to_beats(length);
                    info.streaming_chunk_enables = {RAPIDS_NUM_CHUNKS{1'b1}};

                    final_bytes = length_in_bytes - streaming_bytes;
                    if (final_bytes > 0) begin
                        info.has_final_partial = 1'b1;
                        info.final_transfer_bytes = final_bytes;
                        info.final_start_chunk = 4'h0;  // FIXED: Set start chunk for final
                        info.final_valid_chunks = bytes_to_chunks(final_bytes);
                        /* verilator lint_off WIDTHEXPAND */
                        info.final_chunk_enables = generate_chunk_enables(4'h0, info.final_valid_chunks);
                        /* verilator lint_on WIDTHEXPAND */
                    end
                end else begin
                    // ≤ 64 bytes - single optimal transfer
                    info.has_final_partial = 1'b1;
                    info.final_transfer_bytes = length_in_bytes;
                    info.final_start_chunk = 4'h0;  // FIXED: Set start chunk
                    info.final_valid_chunks = bytes_to_chunks(length_in_bytes);
                    info.final_chunk_enables = {RAPIDS_NUM_CHUNKS{1'b1}};
                end
            end

            ALIGN_STRAT_PRECISION: begin
                // Multi-phase precision alignment
                info.requires_alignment = 1'b1;

                // First transfer: align to 64B boundary - FIXED: Width expansion
                /* verilator lint_off WIDTHEXPAND */
                first_transfer_bytes = ({26'h0, bytes_to_align} <= length_in_bytes) ?
                                     {26'h0, bytes_to_align} : length_in_bytes;
                /* verilator lint_on WIDTHEXPAND */
                info.first_transfer_bytes = first_transfer_bytes;
                info.first_start_chunk = addr_offset[5:2];
                info.first_valid_chunks = bytes_to_chunks(first_transfer_bytes);
                /* verilator lint_off WIDTHEXPAND */
                info.first_chunk_enables = generate_chunk_enables(
                    4'(addr_offset[5:2]), info.first_valid_chunks);  // FIXED: Explicit cast
                /* verilator lint_on WIDTHEXPAND */

                remaining_bytes = length_in_bytes - first_transfer_bytes;

                if (remaining_bytes > 32'd64) begin
                    // Streaming phase for bulk data
                    info.has_streaming_phase = 1'b1;
                    streaming_bytes = (remaining_bytes >> 6) << 6;  // Round down to 64B multiple
                    info.streaming_bytes = streaming_bytes;
                    /* verilator lint_off WIDTHTRUNC */
                    info.optimal_burst_len = 8'(streaming_bytes >> 6);  // FIXED: Explicit 8-bit cast
                    /* verilator lint_on WIDTHTRUNC */
                    info.streaming_chunk_enables = {RAPIDS_NUM_CHUNKS{1'b1}};

                    final_bytes = remaining_bytes - streaming_bytes;
                    if (final_bytes > 0) begin
                        info.has_final_partial = 1'b1;
                        info.final_transfer_bytes = final_bytes;
                        info.final_start_chunk = 4'h0;  // FIXED: Set start chunk
                        info.final_valid_chunks = bytes_to_chunks(final_bytes);
                        /* verilator lint_off WIDTHEXPAND */
                        info.final_chunk_enables = generate_chunk_enables(4'h0, info.final_valid_chunks);
                        /* verilator lint_on WIDTHEXPAND */
                    end
                end else if (remaining_bytes > 0) begin
                    // Only final transfer needed
                    info.has_final_partial = 1'b1;
                    info.final_transfer_bytes = remaining_bytes;
                    info.final_start_chunk = 4'h0;  // FIXED: Set start chunk
                    info.final_valid_chunks = bytes_to_chunks(remaining_bytes);
                    /* verilator lint_off WIDTHEXPAND */
                    info.final_chunk_enables = generate_chunk_enables(4'h0, info.final_valid_chunks);
                    /* verilator lint_on WIDTHEXPAND */
                end
            end

            default: begin
                // Error case - treat as single transfer
                info.alignment_strategy = ALIGN_STRAT_ERROR;
            end
        endcase

        // Calculate totals and efficiency
        info.total_axi_bytes = info.first_transfer_bytes + info.streaming_bytes + info.final_transfer_bytes;
        info.payload_bytes = length_in_bytes;
        info.max_burst_efficiency = calculate_efficiency(info.payload_bytes, info.total_axi_bytes);

        // Calculate total transfer count - FIXED: Width expansion and truncation
        /* verilator lint_off WIDTHEXPAND */
        /* verilator lint_off WIDTHTRUNC */
        info.total_transfers = 4'((info.requires_alignment ? 32'd1 : 32'd0) +
                                (info.has_streaming_phase ? {24'h0, info.optimal_burst_len} : 32'd0) +
                                (info.has_final_partial ? 32'd1 : 32'd0));
        /* verilator lint_on WIDTHTRUNC */
        /* verilator lint_on WIDTHEXPAND */

        return info;
    endfunction

    //=========================================================================
    // Rest of the package structures (unchanged)
    //=========================================================================

    // Transfer Sequence Type Enumeration
    typedef enum logic [1:0] {
        SEQ_SINGLE     = 2'h0,  // Single transfer only
        SEQ_ALIGN_ONLY = 2'h1,  // Alignment + final only
        SEQ_STREAM_ONLY = 2'h2, // Streaming only (already aligned)
        SEQ_FULL       = 2'h3   // All phases: alignment + streaming + final
    } sequence_type_t;

    // AXI Transfer Configuration Structure
    typedef struct packed {
        logic [7:0]              max_burst_length;     // Maximum burst length to use
        logic                    enable_variable_beats; // Allow variable beat sizing
        logic                    force_single_beat;    // Force single beat transfers
        logic                    enable_streaming;     // Enable streaming optimization
        logic [31:0]             timeout_cycles;       // Transaction timeout
        logic [3:0]              cache_policy;         // AXI cache policy
        logic [2:0]              protection_level;     // AXI protection level
    } axi_config_t;

    // Channel Status Structure
    typedef struct packed {
        logic                    active;               // Channel is active
        logic                    ready;                // Channel ready for transfers
        logic                    error;                // Channel in error state
        logic                    overflow;             // Buffer overflow detected
        logic                    underflow;            // Buffer underflow detected
        logic                    eos_pending;          // EOS completion pending
        logic [7:0]              used_count;           // Buffer used count
        logic [7:0]              available_count;      // Buffer available count
        logic [31:0]             bytes_transferred;    // Total bytes transferred
        logic [15:0]             transfers_completed;  // Number of transfers completed
    } channel_status_t;

    // Scheduler State Enumeration
    typedef enum logic [7:0] {
        SCHED_IDLE              = 8'b00000001,
        SCHED_WAIT_FOR_CONTROL  = 8'b00000010,
        SCHED_ISSUE_CTRLRD      = 8'b00000100,
        SCHED_DESCRIPTOR_ACTIVE = 8'b00001000,
        SCHED_ISSUE_CTRLWR0     = 8'b00010000,
        SCHED_ISSUE_CTRLWR1     = 8'b00100000,
        SCHED_ERROR             = 8'b01000000
    } scheduler_state_t;

    // Address Alignment FSM State Enumeration
    typedef enum logic [2:0] {
        ALIGN_IDLE          = 3'b000,  // Wait for descriptor with data address
        ANALYZE_ADDRESS     = 3'b001,  // Analyze address alignment requirements
        CALC_FIRST_TRANSFER = 3'b010,  // Calculate alignment transfer parameters
        CALC_STREAMING      = 3'b011,  // Calculate optimal streaming parameters
        CALC_FINAL_TRANSFER = 3'b100,  // Calculate final partial transfer
        ALIGNMENT_COMPLETE  = 3'b101,  // Provide alignment info to engines
        ALIGNMENT_ERROR     = 3'b110   // Handle alignment calculation errors
    } alignment_fsm_state_t;

    // AXI Engine State Enumerations
    typedef enum logic [2:0] {
        read_IDLE        = 3'b000,
        read_ARBITRATE   = 3'b001,
        READ_PREALLOC    = 3'b010,
        read_ISSUE_ADDR  = 3'b011,
        read_WAIT_DATA   = 3'b100,
        read_COMPLETE    = 3'b101,
        read_ERROR       = 3'b110
    } read_engine_state_t;

    typedef enum logic [2:0] {
        WRITE_IDLE       = 3'b000,
        WRITE_ARBITRATE  = 3'b001,
        WRITE_ISSUE_ADDR = 3'b010,
        WRITE_ISSUE_DATA = 3'b011,
        WRITE_WAIT_RESP  = 3'b100,
        WRITE_COMPLETE   = 3'b101,
        WRITE_ERROR      = 3'b110
    } write_engine_state_t;

endpackage : rapids_pkg
