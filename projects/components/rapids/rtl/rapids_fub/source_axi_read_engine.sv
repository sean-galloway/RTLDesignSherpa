// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: source_axi_read_engine
// Purpose: Source Axi Read Engine module
//
// Documentation: projects/components/rapids_fub/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"

module source_axi_read_engine #(
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int NUM_CHUNKS = 16,
    parameter int AXI_ID_WIDTH = 8,
    parameter int MAX_BURST_LEN = 64,
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int TRACKING_FIFO_DEPTH = 32,
    parameter int COUNT_BITS = 8,
    // Monitor Bus Parameters
    /* verilator lint_off WIDTHTRUNC */
    parameter logic [7:0] MON_AGENT_ID = 8'h40,
    parameter logic [3:0] MON_UNIT_ID = 4'h1,
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0
    /* verilator lint_on WIDTHTRUNC */
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Configuration
    input  logic [2:0]                  cfg_transfer_size,         // 0=256B, 1=512B, 2=1K, 3=2K, 4=4K
    input  logic                        cfg_streaming_enable,

    // Multi-Channel Scheduler Data Interface
    // NOTE: ALL LENGTH VALUES ARE IN 4-BYTE CHUNKS (NOT BYTES)
    input  logic [NUM_CHANNELS-1:0]     data_valid,
    output logic [NUM_CHANNELS-1:0]     data_ready,
    input  logic [ADDR_WIDTH-1:0]       data_address [NUM_CHANNELS],
    input  logic [31:0]                 data_length [NUM_CHANNELS],    // 4-BYTE CHUNKS
    input  logic [1:0]                  data_type [NUM_CHANNELS],
    input  logic [NUM_CHANNELS-1:0]     data_eos,
    output logic [31:0]                 data_transfer_length [NUM_CHANNELS], // 4-BYTE CHUNKS
    output logic [NUM_CHANNELS-1:0]     data_error,
    output logic [NUM_CHANNELS-1:0]     data_done_strobe,

    // Multi-Channel Scheduler Alignment Bus Interface
    input  alignment_info_t             data_alignment_info [NUM_CHANNELS],
    input  logic [NUM_CHANNELS-1:0]     data_alignment_valid,
    output logic [NUM_CHANNELS-1:0]     data_alignment_ready,
    output logic [NUM_CHANNELS-1:0]     data_alignment_next,
    input  transfer_phase_t             data_transfer_phase [NUM_CHANNELS],
    input  logic [NUM_CHANNELS-1:0]     data_sequence_complete,

    // Channel Availability Interface
    input  logic [COUNT_BITS-1:0]       available_lines [NUM_CHANNELS],
    input  logic [NUM_CHANNELS-1:0]     channel_ready_for_prealloc,

    // SRAM Preallocation Interface
    output logic                        prealloc_valid,
    input  logic                        prealloc_ready,
    output logic [7:0]                  prealloc_beats,
    output logic [1:0]                  prealloc_type,
    output logic [CHAN_WIDTH-1:0]       prealloc_channel,

    // Enhanced SRAM Write Interface
    output logic                        wr_valid,
    input  logic                        wr_ready,
    output logic [DATA_WIDTH-1:0]       wr_data,
    output logic [1:0]                  wr_type,
    output logic                        wr_eos,
    output logic [NUM_CHUNKS-1:0]       wr_chunk_valid,
    output logic [CHAN_WIDTH-1:0]       wr_channel,

    // AXI4 Master Read Interface
    output logic                        ar_valid,
    input  logic                        ar_ready,
    output logic [ADDR_WIDTH-1:0]       ar_addr,
    output logic [7:0]                  ar_len,
    output logic [2:0]                  ar_size,
    output logic [1:0]                  ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     ar_id,
    output logic                        ar_lock,
    output logic [3:0]                  ar_cache,
    output logic [2:0]                  ar_prot,
    output logic [3:0]                  ar_qos,
    output logic [3:0]                  ar_region,

    // AXI4 Master Read Data
    input  logic                        r_valid,
    output logic                        r_ready,
    input  logic [DATA_WIDTH-1:0]       r_data,
    input  logic [1:0]                  r_resp,
    input  logic                        r_last,
    input  logic [AXI_ID_WIDTH-1:0]     r_id,

    // Status Interface
    output logic                        engine_idle,
    output logic                        engine_busy,

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    //=========================================================================
    // Pure Pipeline Architecture - No FSM!
    //=========================================================================

    //=========================================================================
    // Channel Arbitration (Pure Combinational)
    //=========================================================================

    logic [NUM_CHANNELS-1:0] w_channel_request_mask;
    logic [NUM_CHANNELS-1:0] w_grant;
    logic [NUM_CHANNELS-1:0] w_grant_ack;
    logic w_grant_valid;
    logic [CHAN_WIDTH-1:0] w_grant_id;

    // Request mask: channels with data, alignment, and SRAM space available
    assign w_channel_request_mask = data_valid & data_alignment_valid & channel_ready_for_prealloc;

    // Round-robin arbiter in grant-ack mode
    arbiter_round_robin #(
        .CLIENTS(NUM_CHANNELS),
        .WAIT_GNT_ACK(1)  // Hold grant until sequence complete
    ) u_channel_arbiter (
        .clk(clk),
        .rst_n(rst_n),
        .block_arb(1'b0),
        .request(w_channel_request_mask),
        .grant_ack(w_grant_ack),
        .grant_valid(w_grant_valid),
        .grant(w_grant),
        .grant_id(w_grant_id),
        .last_grant()
    );

    // Release grant when sequence completes
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_grant_ack
            assign w_grant_ack[i] = w_grant[i] && data_sequence_complete[i] &&
                                w_address_accepted && w_prealloc_accepted;
        end
    endgenerate

    //=========================================================================
    // FIXED: Address Progression Logic Between Transfer Phases
    //=========================================================================

    // Track address progression through phases for each channel
    logic [ADDR_WIDTH-1:0] r_current_phase_addr [NUM_CHANNELS];
    logic [31:0] r_remaining_chunks [NUM_CHANNELS];  // 4-byte chunks remaining

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_current_phase_addr[i] <= '0;
                r_remaining_chunks[i] <= '0;
            end
        end else begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                // Initialize at start of new sequence
                if (data_alignment_next[i] && data_transfer_phase[i] == PHASE_ALIGNMENT) begin
                    r_current_phase_addr[i] <= data_address[i];
                    r_remaining_chunks[i] <= data_length[i];  // Total 4B chunks
                end
                // Progress address and decrement chunks after each completed transfer
                else if (w_response_complete && (w_response_channel == CHAN_WIDTH'(i))) begin
                    case (data_transfer_phase[i])
                        PHASE_ALIGNMENT: begin
                            // Alignment transfers us to next 64B boundary
                            r_current_phase_addr[i] <= (data_address[i] + 64) & ~64'h3F;  // Round up to 64B
                            // Subtract chunks transferred in alignment phase
                            /* verilator lint_off WIDTHEXPAND */
                            r_remaining_chunks[i] <= r_remaining_chunks[i] -
                                32'(data_alignment_info[i].first_transfer_bytes >> 2);  // FIXED: 32-bit cast
                            /* verilator lint_on WIDTHEXPAND */
                        end
                        PHASE_STREAMING: begin
                            // Streaming transfers are always 64B (16 chunks)
                            r_current_phase_addr[i] <= r_current_phase_addr[i] + 64;
                            r_remaining_chunks[i] <= r_remaining_chunks[i] - 32'd16;  // 64 bytes = 16 chunks
                        end
                        PHASE_FINAL: begin
                            // Final transfer completes the remaining chunks
                            /* verilator lint_off WIDTHEXPAND */
                            r_current_phase_addr[i] <= r_current_phase_addr[i] +
                                ADDR_WIDTH'(data_alignment_info[i].final_transfer_bytes);  // FIXED: Explicit cast
                            /* verilator lint_on WIDTHEXPAND */
                            r_remaining_chunks[i] <= '0;  // Should be zero after final
                        end
                        default: begin
                            // Single phase transfer
                            /* verilator lint_off WIDTHEXPAND */
                            r_current_phase_addr[i] <= r_current_phase_addr[i] +
                                ADDR_WIDTH'(data_length[i] << 2);  // FIXED: Explicit cast for chunks to bytes
                            /* verilator lint_on WIDTHEXPAND */
                            r_remaining_chunks[i] <= '0;
                        end
                    endcase
                end
            end
        end
    end

    //=========================================================================
    // FIXED: Preallocation Pipeline with Dynamic Parameters
    //=========================================================================

    // Current transfer parameters (pure combinational from scheduler alignment)
    logic [ADDR_WIDTH-1:0] w_current_addr;
    logic [7:0] w_current_burst_len;
    logic [2:0] w_current_axi_size;
    logic [NUM_CHUNKS-1:0] w_current_chunk_enables;
    logic [1:0] w_current_type;
    logic w_eos_in_current_transfer;

    // FIXED: Extract current transfer parameters with proper width handling
    always_comb begin
        w_current_addr = '0;
        w_current_burst_len = 8'h1;
        w_current_axi_size = 3'b110;  // Default 64-byte
        w_current_chunk_enables = {NUM_CHUNKS{1'b0}};
        w_current_type = 2'b00;
        w_eos_in_current_transfer = 1'b0;

        if (w_grant_valid) begin
            w_current_type = data_type[w_grant_id];
            w_eos_in_current_transfer = data_eos[w_grant_id];

            // Use progressed address for current phase
            w_current_addr = r_current_phase_addr[w_grant_id];

            // FIXED: Use scheduler's pre-calculated alignment with proper width casting
            case (data_transfer_phase[w_grant_id])
                PHASE_ALIGNMENT: begin
                    // Alignment phase: Use 4-byte transfers for granular control
                    w_current_axi_size = 3'b010;  // 4 bytes per beat
                    // Calculate beats needed: alignment bytes ÷ 4 bytes per beat
                    /* verilator lint_off WIDTHTRUNC */
                    w_current_burst_len = 8'((data_alignment_info[w_grant_id].first_transfer_bytes + 32'd3) >> 2);
                    /* verilator lint_on WIDTHTRUNC */
                    w_current_chunk_enables = data_alignment_info[w_grant_id].first_chunk_enables;
                end
                PHASE_STREAMING: begin
                    // Streaming phase: Use configured transfer size for HBM3e optimization
                    w_current_axi_size = 3'b110;  // 64 bytes per beat
                    w_current_burst_len = calc_transfer_size_beats(cfg_transfer_size);
                    w_current_chunk_enables = data_alignment_info[w_grant_id].streaming_chunk_enables;
                end
                PHASE_FINAL: begin
                    // Final phase: Use 4-byte transfers for precise partial data
                    w_current_axi_size = 3'b010;  // 4 bytes per beat
                    // Calculate beats needed: final bytes ÷ 4 bytes per beat
                    /* verilator lint_off WIDTHTRUNC */
                    w_current_burst_len = 8'((data_alignment_info[w_grant_id].final_transfer_bytes + 32'd3) >> 2);
                    /* verilator lint_on WIDTHTRUNC */
                    w_current_chunk_enables = data_alignment_info[w_grant_id].final_chunk_enables;
                end
                PHASE_SINGLE: begin
                    // Single transfer: Determine size based on alignment
                    if (w_current_addr[5:0] == 6'h0 && (data_length[w_grant_id] >= 32'd16)) begin
                        // 64B aligned and ≥64 bytes: use 64-byte transfers
                        w_current_axi_size = 3'b110;  // 64 bytes per beat
                        /* verilator lint_off WIDTHTRUNC */
                        w_current_burst_len = 8'((data_length[w_grant_id] + 32'd15) >> 4);  // FIXED: Explicit cast
                        /* verilator lint_on WIDTHTRUNC */
                    end else begin
                        // Misaligned or <64 bytes: use 4-byte transfers
                        w_current_axi_size = 3'b010;  // 4 bytes per beat
                        w_current_burst_len = data_length[w_grant_id][7:0];  // Direct 4B chunk count
                    end
                    w_current_chunk_enables = {NUM_CHUNKS{1'b1}};  // Enable all needed chunks
                end
                default: begin
                    // Default case: Use 4-byte transfers for safety
                    w_current_axi_size = 3'b010;  // 4 bytes per beat
                    w_current_burst_len = data_length[w_grant_id][7:0];  // 4B chunks
                    w_current_chunk_enables = {NUM_CHUNKS{1'b1}};
                end
            endcase

            // Clamp burst length to AXI limits - FIXED: Width expansion
            /* verilator lint_off WIDTHEXPAND */
            if ({24'h0, w_current_burst_len} > 32'(MAX_BURST_LEN)) begin
                w_current_burst_len = 8'(MAX_BURST_LEN);  // FIXED: Explicit cast
            end else if (w_current_burst_len == 8'h0) begin
            /* verilator lint_on WIDTHEXPAND */
                w_current_burst_len = 8'h1;  // Minimum 1 beat
            end
        end
    end

    // IMMEDIATE Preallocation (same cycle as arbitration!)
    logic w_prealloc_accepted;
    assign prealloc_valid = w_grant_valid;  // Preallocate immediately when granted
    assign prealloc_beats = w_current_burst_len;
    assign prealloc_type = w_current_type;
    assign prealloc_channel = w_grant_id;

    assign w_prealloc_accepted = prealloc_valid && prealloc_ready;

    //=========================================================================
    // FIXED: Address Phase Pipeline with Dynamic AXI Sizing
    //=========================================================================

    // Preallocation pipeline register
    logic [CHAN_WIDTH-1:0] r_prealloc_channel;
    logic r_prealloc_valid;
    logic [ADDR_WIDTH-1:0] r_prealloc_addr;
    logic [7:0] r_prealloc_burst_len;
    logic [2:0] r_prealloc_axi_size;
    logic [NUM_CHUNKS-1:0] r_prealloc_chunk_enables;
    logic [1:0] r_prealloc_type;
    logic r_prealloc_eos;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_prealloc_channel <= '0;
            r_prealloc_valid <= 1'b0;
            r_prealloc_addr <= '0;
            r_prealloc_burst_len <= 8'h0;
            r_prealloc_axi_size <= 3'b110;
            r_prealloc_chunk_enables <= '0;
            r_prealloc_type <= 2'b00;
            r_prealloc_eos <= 1'b0;
        end else begin
            if (w_prealloc_accepted) begin
                r_prealloc_channel <= w_grant_id;
                r_prealloc_valid <= 1'b1;
                r_prealloc_addr <= w_current_addr;
                r_prealloc_burst_len <= w_current_burst_len;
                r_prealloc_axi_size <= w_current_axi_size;  // Store calculated size
                r_prealloc_chunk_enables <= w_current_chunk_enables;
                r_prealloc_type <= w_current_type;
                r_prealloc_eos <= w_eos_in_current_transfer;
            end else if (w_address_accepted) begin
                r_prealloc_valid <= 1'b0;
            end
        end
    end

    // AXI ID encoding (channel ID in lower bits)
    logic [AXI_ID_WIDTH-1:0] w_axi_id;
    assign w_axi_id = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, r_prealloc_channel};

    // FIXED: AXI Address Issue with Dynamic Sizing
    logic w_address_accepted;
    assign ar_valid = r_prealloc_valid;  // Issue address when prealloc complete
    assign ar_addr = r_prealloc_addr;
    assign ar_len = r_prealloc_burst_len - 8'h1;  // AXI length encoding
    assign ar_size = r_prealloc_axi_size;  // Use calculated size (4B or 64B)
    assign ar_burst = 2'b01;  // INCR
    assign ar_id = w_axi_id;
    assign ar_lock = 1'b0;
    assign ar_cache = 4'b0010;  // Normal non-cacheable
    assign ar_prot = 3'b000;
    assign ar_qos = 4'b0000;
    assign ar_region = 4'b0000;

    assign w_address_accepted = ar_valid && ar_ready;

    //=========================================================================
    // Response Pipeline (Direct AXI → SRAM Write)
    //=========================================================================

    // Address pipeline register to track transaction details
    logic [CHAN_WIDTH-1:0] r_addr_issued_channel;
    logic r_addr_issued_valid;
    logic [NUM_CHUNKS-1:0] r_addr_issued_chunk_enables;
    logic [1:0] r_addr_issued_type;
    logic r_addr_issued_eos;
    logic [7:0] r_addr_issued_burst_len;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_addr_issued_channel <= '0;
            r_addr_issued_valid <= 1'b0;
            r_addr_issued_chunk_enables <= '0;
            r_addr_issued_type <= 2'b00;
            r_addr_issued_eos <= 1'b0;
            r_addr_issued_burst_len <= 8'h0;
        end else begin
            if (w_address_accepted) begin
                r_addr_issued_channel <= r_prealloc_channel;
                r_addr_issued_valid <= 1'b1;
                r_addr_issued_chunk_enables <= r_prealloc_chunk_enables;
                r_addr_issued_type <= r_prealloc_type;
                r_addr_issued_eos <= r_prealloc_eos;
                r_addr_issued_burst_len <= r_prealloc_burst_len;
            end else if (w_response_complete) begin
                r_addr_issued_valid <= 1'b0;
            end
        end
    end

    // Beat counter for burst tracking
    logic [7:0] r_response_beat_count;
    logic w_response_complete;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_response_beat_count <= 8'h0;
        end else begin
            if (w_address_accepted) begin
                r_response_beat_count <= r_prealloc_burst_len;
            end else if (r_valid && r_ready && r_addr_issued_valid) begin
                r_response_beat_count <= r_response_beat_count - 8'h1;
            end
        end
    end

    assign w_response_complete = r_valid && r_ready && r_last;

    // Response channel extraction
    logic [CHAN_WIDTH-1:0] w_response_channel;
    logic w_our_response;
    logic w_axi_error;

    assign w_response_channel = r_id[CHAN_WIDTH-1:0];
    assign w_our_response = r_valid;  // All responses should be ours
    assign w_axi_error = w_our_response && (r_resp != 2'b00);

    // DIRECT SRAM Write (pure pipeline!)
    assign wr_valid = w_our_response && r_addr_issued_valid;
    assign wr_data = r_data;
    assign wr_type = r_addr_issued_type;
    assign wr_eos = wr_valid && r_last && r_addr_issued_eos;
    assign wr_chunk_valid = r_addr_issued_chunk_enables;
    assign wr_channel = w_response_channel;

    // Always ready for responses (pure pipeline)
    assign r_ready = wr_ready;

    //=========================================================================
    // Outstanding Transaction Tracking
    //=========================================================================

    logic [15:0] r_outstanding_count;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_outstanding_count <= 16'h0;
        end else begin
            case ({w_address_accepted, w_response_complete})
                2'b10: r_outstanding_count <= r_outstanding_count + 16'h1;  // Address only
                2'b01: r_outstanding_count <= r_outstanding_count - 16'h1;  // Response only
                2'b11: r_outstanding_count <= r_outstanding_count;          // Both (no change)
                default: r_outstanding_count <= r_outstanding_count;        // Neither
            endcase
        end
    end

    //=========================================================================
    // Scheduler Interface (Pure Combinational)
    //=========================================================================

    // Always ready for alignment info (no buffering needed)
    assign data_alignment_ready = {NUM_CHANNELS{1'b1}};

    // Request next alignment when current transfer completes and more in sequence
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_alignment_next
            assign data_alignment_next[i] = w_response_complete &&
                                        (w_response_channel == i) &&
                                        !data_sequence_complete[i];
        end
    endgenerate

    // Data ready when not actively transferring or when sequence completes
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_data_ready
            assign data_ready[i] = !w_grant[i] ||
                                (w_response_complete && (w_response_channel == i) &&
                                data_sequence_complete[i]);
        end
    endgenerate

    //=========================================================================
    // FIXED: Completion Tracking with 4-Byte Chunk Accounting
    //=========================================================================

    logic [31:0] r_channel_chunks_transferred [NUM_CHANNELS];  // Track in 4B chunks

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_channel_chunks_transferred[i] <= 32'h0;
            end
        end else begin
            // Increment chunks when data written to SRAM
            if (wr_valid && wr_ready) begin
                // Count actual chunks transferred based on chunk enables
                logic [4:0] chunks_this_beat;
                chunks_this_beat = 5'h0;
                for (int j = 0; j < NUM_CHUNKS; j++) begin
                    if (wr_chunk_valid[j]) begin
                        chunks_this_beat = chunks_this_beat + 5'h1;
                    end
                end
                /* verilator lint_off WIDTHEXPAND */
                r_channel_chunks_transferred[wr_channel] <=
                    r_channel_chunks_transferred[wr_channel] + 32'(chunks_this_beat);  // FIXED: 32-bit cast
                /* verilator lint_on WIDTHEXPAND */
            end

            // Reset when sequence completes
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                /* verilator lint_off WIDTHEXPAND */
                if (data_sequence_complete[i] && w_response_complete && (w_response_channel == CHAN_WIDTH'(i))) begin
                /* verilator lint_on WIDTHEXPAND */
                    r_channel_chunks_transferred[i] <= 32'h0;
                end
            end
        end
    end

    // Completion signals - Report in 4-byte chunks
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_completion
            assign data_transfer_length[i] = r_channel_chunks_transferred[i];  // 4B chunks transferred
            assign data_done_strobe[i] = w_response_complete && (w_response_channel == i) &&
                                    data_sequence_complete[i];
            assign data_error[i] = w_our_response && (w_response_channel == i) && w_axi_error;
        end
    endgenerate

    //=========================================================================
    // Status and Monitor Outputs
    //=========================================================================

    assign engine_idle = !w_grant_valid && !r_prealloc_valid && !r_addr_issued_valid &&
                        (r_outstanding_count == 16'h0);
    assign engine_busy = w_grant_valid || r_prealloc_valid || r_addr_issued_valid ||
                        (r_outstanding_count > 16'h0);

    // Simple monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            r_mon_valid <= 1'b0;  // Default

            // Monitor address acceptance with transfer type info
            if (w_address_accepted) begin
                r_mon_valid <= 1'b1;
                r_mon_packet <= create_monitor_packet(
                    PktTypePerf,
                    PROTOCOL_AXI,
                    AXI_PERF_ADDR_LATENCY,
                    MON_CHANNEL_ID,
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    35'({3'h0, r_prealloc_axi_size, 8'h0, r_prealloc_burst_len, 12'h0, r_prealloc_channel})
                );
            end
            // Monitor completion
            else if (|data_done_strobe) begin
                r_mon_valid <= 1'b1;
                r_mon_packet <= create_monitor_packet(
                    PktTypeCompletion,
                    PROTOCOL_AXI,
                    AXI_COMPL_READ_COMPLETE,
                    MON_CHANNEL_ID,
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    35'h0
                );
            end
        end
    end

    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Verification Assertions for Alignment Requirements
    //=========================================================================

    `ifdef FORMAL
    // Verify 4-byte alignment support in alignment/final phases
    property alignment_4byte_transfers;
        @(posedge clk) disable iff (!rst_n)
        $forall(i = 0; i < NUM_CHANNELS; i++)
        (data_transfer_phase[i] inside {PHASE_ALIGNMENT, PHASE_FINAL} &&
        ar_valid && ar_id[CHAN_WIDTH-1:0] == i)
        |-> (ar_size == 3'b010);  // Must use 4-byte transfers
    endproperty
    assert property (alignment_4byte_transfers);

    // Verify 64-byte optimal transfers in streaming phase
    property streaming_64byte_transfers;
        @(posedge clk) disable iff (!rst_n)
        $forall(i = 0; i < NUM_CHANNELS; i++)
        (data_transfer_phase[i] == PHASE_STREAMING &&
        ar_valid && ar_id[CHAN_WIDTH-1:0] == i)
        |-> (ar_size == 3'b110);  // Must use 64-byte transfers
    endproperty
    assert property (streaming_64byte_transfers);

    // Verify address progression maintains 64B alignment in streaming
    property streaming_address_aligned;
        @(posedge clk) disable iff (!rst_n)
        $forall(i = 0; i < NUM_CHANNELS; i++)
        (data_transfer_phase[i] == PHASE_STREAMING &&
        ar_valid && ar_id[CHAN_WIDTH-1:0] == i)
        |-> (ar_addr[5:0] == 6'h0);  // Must be 64-byte aligned
    endproperty
    assert property (streaming_address_aligned);

    // Verify length accounting in 4B chunks
    property chunk_accounting_consistency;
        @(posedge clk) disable iff (!rst_n)
        $forall(i = 0; i < NUM_CHANNELS; i++)
        data_sequence_complete[i] |->
        (r_channel_chunks_transferred[i] <= data_length[i]);
    endproperty
    assert property (chunk_accounting_consistency);
    `endif

endmodule : source_axi_read_engine
