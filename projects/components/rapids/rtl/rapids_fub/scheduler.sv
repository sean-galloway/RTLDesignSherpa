// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler
// Purpose: Scheduler module
//
// Documentation: projects/components/rapids_fub/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"

module scheduler #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 32,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int NUM_CHUNKS = 16,
    parameter int CREDIT_WIDTH = 8,
    parameter int TIMEOUT_CYCLES = 1000,
    parameter int EARLY_WARNING_THRESHOLD = 4,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h30,
    parameter logic [3:0] MON_UNIT_ID = 4'h1,
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Configuration
    input  logic                        cfg_idle_mode,
    input  logic                        cfg_channel_wait,
    input  logic                        cfg_channel_enable,
    input  logic                        cfg_use_credit,
    input  logic [3:0]                  cfg_initial_credit,
    input  logic                        credit_increment,
    input  logic                        cfg_channel_reset,
    output logic [31:0]                 descriptor_credit_counter,
    output logic [7:0]                  fsm_state,

    // Status Interface
    output logic                        scheduler_idle,

    // Enhanced Descriptor Engine Interface
    input  logic                        descriptor_valid,
    output logic                        descriptor_ready,
    input  logic [DATA_WIDTH-1:0]       descriptor_packet,
    input  logic                        descriptor_same,
    input  logic                        descriptor_error,
    input  logic                        descriptor_is_cda,
    input  logic [CHAN_WIDTH-1:0]       descriptor_cda_channel,
    input  logic                        descriptor_eos,
    input  logic                        descriptor_eol,
    input  logic                        descriptor_eod,
    input  logic [1:0]                  descriptor_type,

    // EOS Completion Interface (from SRAM Control)
    input  logic                        eos_completion_valid,
    output logic                        eos_completion_ready,
    input  logic [CHAN_WIDTH-1:0]       eos_completion_channel,

    // Ctrlrd Engine Interface (Control Read - Pre-Descriptor)
    output logic                        ctrlrd_valid,
    input  logic                        ctrlrd_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlrd_addr,
    output logic [31:0]                 ctrlrd_data,
    output logic [31:0]                 ctrlrd_mask,
    input  logic                        ctrlrd_error,
    input  logic [31:0]                 ctrlrd_result,

    // Ctrlwr Engine Interface (Control Write - Post-Descriptor)
    output logic                        ctrlwr_valid,
    input  logic                        ctrlwr_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlwr_addr,
    output logic [31:0]                 ctrlwr_data,
    input  logic                        ctrlwr_error,

    // EXISTING Data Engine Interface (unchanged for compatibility)
    output logic                        data_valid,
    input  logic                        data_ready,
    output logic [ADDR_WIDTH-1:0]       data_address,
    output logic [31:0]                 data_length,
    output logic [1:0]                  data_type,
    output logic                        data_eos,
    input  logic [31:0]                 data_transfer_length,
    input  logic                        data_error,
    input  logic                        data_done_strobe,

    // NEW: Address Alignment Bus (using RAPIDS package types)
    output alignment_info_t             data_alignment_info,
    output logic                        data_alignment_valid,
    input  logic                        data_alignment_ready,
    input  logic                        data_alignment_next,
    output transfer_phase_t             data_transfer_phase,
    output logic                        data_sequence_complete,

    // CDA Completion Interface
    output logic                        cda_complete_valid,
    input  logic                        cda_complete_ready,
    output logic [CHAN_WIDTH-1:0]       cda_complete_channel,

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet,

    // Status outputs
    output logic                        scheduler_error,
    output logic                        backpressure_warning
);

    //=========================================================================
    // Internal Signals (using RAPIDS package types)
    //=========================================================================

    // Main FSM state (using RAPIDS package enum)
    scheduler_state_t r_current_state, w_next_state;

    // Address Alignment FSM state (using RAPIDS package enum)
    alignment_fsm_state_t r_alignment_state, w_alignment_next_state;

    // Channel reset management
    logic r_channel_reset_active;
    logic w_safe_to_reset;
    logic w_no_pending_operations;

    // Descriptor processing registers
    logic [ADDR_WIDTH-1:0] r_next_descriptor_addr;
    logic [ADDR_WIDTH-1:0] r_data_addr;
    logic [31:0] r_data_length;
    logic [ADDR_WIDTH-1:0] r_ctrlrd_addr;
    logic [31:0] r_ctrlrd_data;
    logic [31:0] r_ctrlrd_mask;
    logic [ADDR_WIDTH-1:0] r_ctrlwr0_addr;
    logic [31:0] r_ctrlwr0_data;
    logic [ADDR_WIDTH-1:0] r_ctrlwr1_addr;
    logic [31:0] r_ctrlwr1_data;
    logic [1:0] r_data_type;
    logic r_packet_eos_received;
    logic r_stream_boundary_pending;

    // Address Alignment Registers (using RAPIDS package structure)
    alignment_info_t r_alignment_info;
    logic r_alignment_valid;
    transfer_phase_t r_transfer_phase;
    logic r_sequence_complete;
    logic [3:0] r_current_transfer_index;

    // Credit management
    logic [31:0] r_descriptor_credit_counter;
    logic w_credit_available;
    logic [31:0] r_timeout_counter;
    logic w_timeout_expired;
    logic r_data_error_sticky;
    logic r_ctrlrd_error_sticky;
    logic r_ctrlwr_error_sticky;

    // Descriptor completion logic
    logic w_descriptor_complete_by_length;
    logic w_descriptor_complete_by_eos;
    logic w_descriptor_complete;
    logic w_ctrlrd_needed;
    logic w_ctrlwr0_needed;
    logic w_ctrlwr1_needed;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // Address Alignment Calculation Logic (using RAPIDS package functions)
    //=========================================================================

    // Address analysis signals (using RAPIDS package functions)
    logic [5:0] w_addr_offset;
    logic w_is_aligned;
    logic [31:0] w_bytes_to_boundary;
    logic [3:0] w_start_chunk;
    logic [3:0] w_chunks_in_first;
    logic [31:0] w_remaining_after_first;
    logic [31:0] w_streaming_transfers;
    logic [31:0] w_final_bytes;

    // Use RAPIDS package functions for address analysis
    assign w_addr_offset = get_address_offset(r_data_addr);
    assign w_is_aligned = is_address_aligned(r_data_addr);
    assign w_bytes_to_boundary = w_is_aligned ? 32'h0 : {26'h0, bytes_to_boundary(r_data_addr)};
    assign w_start_chunk = w_addr_offset[5:2];  // Which 32-bit chunk to start

    // FIXED: Calculate chunk enables using RAPIDS package function with proper width handling
    always_comb begin
        w_chunks_in_first = 4'h0;

        if (!w_is_aligned && (w_bytes_to_boundary <= r_data_length)) begin
            w_chunks_in_first = bytes_to_chunks(w_bytes_to_boundary);
        end else if (w_is_aligned) begin
            /* verilator lint_off WIDTHTRUNC */
            w_chunks_in_first = (r_data_length >= 64) ? 4'd16 : bytes_to_chunks(r_data_length);  // Explicit 4-bit literal
            /* verilator lint_on WIDTHTRUNC */
        end else begin
            w_chunks_in_first = bytes_to_chunks(r_data_length);  // All remaining data
        end
    end

    // Calculate remaining data after first transfer
    assign w_remaining_after_first = w_is_aligned ?
                                ((r_data_length >= 64) ? (r_data_length - 64) : 32'h0) :
                                ((r_data_length >= w_bytes_to_boundary) ?
                                    (r_data_length - w_bytes_to_boundary) : 32'h0);

    // Calculate streaming phase parameters
    assign w_streaming_transfers = w_remaining_after_first >> 6;  // Number of 64-byte transfers
    assign w_final_bytes = w_remaining_after_first & 32'h3F;     // Remaining bytes after streaming

    //=========================================================================
    // FIXED: Address Alignment FSM Logic - Complete Case Coverage
    //=========================================================================

    // Alignment FSM state register
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_alignment_state <= ALIGN_IDLE;
        end else begin
            r_alignment_state <= w_alignment_next_state;
        end
    end

    // FIXED: Alignment FSM next state logic with complete case coverage
    always_comb begin
        // Default assignment
        w_alignment_next_state = r_alignment_state;

        if (r_channel_reset_active) begin
            w_alignment_next_state = ALIGN_IDLE;
        end else begin
            case (r_alignment_state)
                ALIGN_IDLE: begin
                    if ((r_current_state == SCHED_DESCRIPTOR_ACTIVE) && (r_data_length > 32'h0)) begin
                        w_alignment_next_state = ANALYZE_ADDRESS;
                    end
                end

                ANALYZE_ADDRESS: begin
                    // Analysis completes in one cycle
                    if (!w_is_aligned && (w_bytes_to_boundary <= r_data_length)) begin
                        w_alignment_next_state = CALC_FIRST_TRANSFER;
                    end else if (w_remaining_after_first > 64) begin
                        w_alignment_next_state = CALC_STREAMING;
                    end else if (w_remaining_after_first > 0) begin
                        w_alignment_next_state = CALC_FINAL_TRANSFER;
                    end else begin
                        w_alignment_next_state = ALIGNMENT_COMPLETE;
                    end
                end

                CALC_FIRST_TRANSFER: begin
                    if (w_remaining_after_first > 64) begin
                        w_alignment_next_state = CALC_STREAMING;
                    end else if (w_remaining_after_first > 0) begin
                        w_alignment_next_state = CALC_FINAL_TRANSFER;
                    end else begin
                        w_alignment_next_state = ALIGNMENT_COMPLETE;
                    end
                end

                CALC_STREAMING: begin
                    if (w_final_bytes > 0) begin
                        w_alignment_next_state = CALC_FINAL_TRANSFER;
                    end else begin
                        w_alignment_next_state = ALIGNMENT_COMPLETE;
                    end
                end

                CALC_FINAL_TRANSFER: begin
                    w_alignment_next_state = ALIGNMENT_COMPLETE;
                end

                ALIGNMENT_COMPLETE: begin
                    if (r_sequence_complete || (r_current_state != SCHED_DESCRIPTOR_ACTIVE)) begin
                        w_alignment_next_state = ALIGN_IDLE;
                    end
                end

                ALIGNMENT_ERROR: begin
                    w_alignment_next_state = ALIGN_IDLE;  // Reset on error
                end

                // FIXED: Added default case to ensure complete coverage
                default: begin
                    w_alignment_next_state = ALIGNMENT_ERROR;
                end
            endcase
        end
    end

    //=========================================================================
    // Alignment Information Register Updates (using RAPIDS package functions)
    //=========================================================================

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_alignment_info <= '0;
            r_alignment_valid <= 1'b0;
            r_transfer_phase <= PHASE_IDLE;
            r_sequence_complete <= 1'b0;
            r_current_transfer_index <= 4'h0;
        end else begin
            case (r_alignment_state)
                ANALYZE_ADDRESS: begin
                    // Basic alignment information using RAPIDS package functions
                    r_alignment_info.is_aligned <= w_is_aligned;
                    r_alignment_info.addr_offset <= w_addr_offset;
                    r_alignment_info.requires_alignment <= !w_is_aligned && (w_bytes_to_boundary <= r_data_length);
                    r_alignment_info.payload_bytes <= r_data_length;
                    r_alignment_info.alignment_strategy <= select_alignment_strategy(
                        r_data_addr, r_data_length, 1'b0, 1'b1);
                end

                CALC_FIRST_TRANSFER: begin
                    // First transfer parameters using RAPIDS package functions
                    r_alignment_info.first_transfer_bytes <= w_is_aligned ?
                                                        ((r_data_length >= 64) ? 32'd64 : r_data_length) :
                                                        w_bytes_to_boundary;
                    r_alignment_info.first_start_chunk <= w_start_chunk;
                    r_alignment_info.first_valid_chunks <= w_chunks_in_first;

                    // Generate first transfer chunk enables using RAPIDS package function
                    r_alignment_info.first_chunk_enables <= generate_chunk_enables(w_start_chunk, w_chunks_in_first);
                end

                CALC_STREAMING: begin
                    // Streaming phase parameters
                    r_alignment_info.has_streaming_phase <= (w_streaming_transfers > 0);
                    r_alignment_info.optimal_burst_len <= (w_streaming_transfers > 64) ? 8'd64 : w_streaming_transfers[7:0];
                    r_alignment_info.streaming_bytes <= w_streaming_transfers << 6;  // × 64
                    r_alignment_info.streaming_chunk_enables <= {NUM_CHUNKS{1'b1}};  // All chunks valid
                end

                CALC_FINAL_TRANSFER: begin
                    // Final transfer parameters using RAPIDS package functions
                    r_alignment_info.has_final_partial <= (w_final_bytes > 0);
                    r_alignment_info.final_transfer_bytes <= w_final_bytes;
                    r_alignment_info.final_valid_chunks <= bytes_to_chunks(w_final_bytes);

                    // Generate final transfer chunk enables using RAPIDS package function
                    r_alignment_info.final_chunk_enables <= generate_chunk_enables(4'h0, bytes_to_chunks(w_final_bytes));
                end

                ALIGNMENT_COMPLETE: begin
                    r_alignment_valid <= 1'b1;

                    // Calculate total transfers and efficiency using RAPIDS package functions
                    r_alignment_info.total_transfers <= (r_alignment_info.requires_alignment ? 4'h1 : 4'h0) +
                                                    (r_alignment_info.has_streaming_phase ? w_streaming_transfers[3:0] : 4'h0) +
                                                    (r_alignment_info.has_final_partial ? 4'h1 : 4'h0);

                    // Calculate total AXI bytes
                    r_alignment_info.total_axi_bytes <= r_alignment_info.first_transfer_bytes +
                                                    r_alignment_info.streaming_bytes +
                                                    r_alignment_info.final_transfer_bytes;

                    // Calculate efficiency using RAPIDS package function
                    if (r_alignment_info.total_axi_bytes > 0) begin
                        r_alignment_info.max_burst_efficiency <=
                            calculate_efficiency(r_alignment_info.payload_bytes, r_alignment_info.total_axi_bytes);
                    end

                    // Stream boundary integration
                    r_alignment_info.eos_in_alignment <= descriptor_eos && r_alignment_info.requires_alignment;
                    r_alignment_info.eos_in_streaming <= descriptor_eos && r_alignment_info.has_streaming_phase;
                    r_alignment_info.eos_in_final <= descriptor_eos && r_alignment_info.has_final_partial;
                end

                // FIXED: Handle all other cases explicitly
                default: begin
                    // Maintain current values for unhandled states
                end
            endcase

            // Handle transfer phase progression using RAPIDS package enum
            if (data_alignment_next) begin
                r_current_transfer_index <= r_current_transfer_index + 1;

                // Update transfer phase using RAPIDS package enum
                if (r_current_transfer_index == 0 && r_alignment_info.requires_alignment) begin
                    r_transfer_phase <= PHASE_ALIGNMENT;
                end else if (r_alignment_info.has_streaming_phase) begin
                    r_transfer_phase <= PHASE_STREAMING;
                end else begin
                    r_transfer_phase <= PHASE_FINAL;
                end

                // Check for sequence completion
                if (r_current_transfer_index >= (r_alignment_info.total_transfers - 1)) begin
                    r_sequence_complete <= 1'b1;
                end
            end

            // Reset sequence tracking when starting new descriptor
            if (r_alignment_state == ALIGN_IDLE) begin
                r_current_transfer_index <= 4'h0;
                r_sequence_complete <= 1'b0;
                r_alignment_valid <= 1'b0;
                r_transfer_phase <= PHASE_IDLE;
            end
        end
    end

    //=========================================================================
    // Main Scheduler FSM Logic (using RAPIDS package types)
    //=========================================================================

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_current_state <= SCHED_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    end

    // Main FSM logic using RAPIDS package enum values
    always_comb begin
        w_next_state = r_current_state;

        if (r_channel_reset_active) begin
            case (r_current_state)
                SCHED_ISSUE_CTRLRD, SCHED_ISSUE_CTRLWR0, SCHED_ISSUE_CTRLWR1: begin
                    // Allow control operations to complete during reset
                    if ((r_current_state == SCHED_ISSUE_CTRLRD && ctrlrd_ready) ||
                        (r_current_state == SCHED_ISSUE_CTRLWR0 && ctrlwr_ready) ||
                        (r_current_state == SCHED_ISSUE_CTRLWR1 && ctrlwr_ready)) begin
                        w_next_state = SCHED_IDLE;
                    end
                end
                default: w_next_state = SCHED_IDLE;
            endcase
        end else begin
            if (data_error || ctrlrd_error || ctrlwr_error || descriptor_error ||
                w_timeout_expired || r_data_error_sticky || r_ctrlrd_error_sticky || r_ctrlwr_error_sticky) begin
                w_next_state = SCHED_ERROR;
            end else begin
                case (r_current_state)
                    SCHED_IDLE: begin
                        if (cfg_idle_mode) begin
                            w_next_state = SCHED_IDLE;
                        end else if (descriptor_valid && w_credit_available) begin
                            w_next_state = SCHED_WAIT_FOR_CONTROL;
                        end else if (descriptor_valid && !w_credit_available && cfg_use_credit) begin
                            w_next_state = SCHED_ERROR;
                        end
                    end

                    SCHED_WAIT_FOR_CONTROL: begin
                        if (!cfg_channel_wait && cfg_channel_enable) begin
                            if (w_ctrlrd_needed) begin
                                w_next_state = SCHED_ISSUE_CTRLRD;  // Control read first
                            end else begin
                                w_next_state = SCHED_DESCRIPTOR_ACTIVE;  // Skip to data ops
                            end
                        end
                    end

                    SCHED_ISSUE_CTRLRD: begin
                        if (ctrlrd_ready && !ctrlrd_error) begin
                            // Read matched expected value - proceed to data operations
                            w_next_state = SCHED_DESCRIPTOR_ACTIVE;
                        end else if (ctrlrd_ready && ctrlrd_error) begin
                            // Max retries exceeded or AXI error - enter error state
                            w_next_state = SCHED_ERROR;
                        end
                        // Else: Stay in SCHED_ISSUE_CTRLRD while ctrlrd engine retries
                    end

                    SCHED_DESCRIPTOR_ACTIVE: begin
                        if (w_descriptor_complete) begin
                            if (w_ctrlwr0_needed) begin
                                w_next_state = SCHED_ISSUE_CTRLWR0;
                            end else if (w_ctrlwr1_needed) begin
                                w_next_state = SCHED_ISSUE_CTRLWR1;
                            end else begin
                                w_next_state = SCHED_IDLE;
                            end
                        end
                    end

                    SCHED_ISSUE_CTRLWR0: begin
                        if (ctrlwr_ready) begin
                            if (w_ctrlwr1_needed) begin
                                w_next_state = SCHED_ISSUE_CTRLWR1;
                            end else begin
                                w_next_state = SCHED_IDLE;
                            end
                        end
                    end

                    SCHED_ISSUE_CTRLWR1: begin
                        if (ctrlwr_ready) begin
                            w_next_state = SCHED_IDLE;
                        end
                    end

                    SCHED_ERROR: begin
                        if (!data_error && !ctrlrd_error && !ctrlwr_error && !descriptor_error &&
                            !w_timeout_expired && !r_data_error_sticky && !r_ctrlrd_error_sticky &&
                            !r_ctrlwr_error_sticky && w_credit_available) begin
                            w_next_state = SCHED_IDLE;
                        end
                    end

                    default: begin
                        w_next_state = SCHED_ERROR;
                    end
                endcase
            end
        end
    end

    //=========================================================================
    // Output Assignments (using RAPIDS package types)
    //=========================================================================

    // Existing data interface (unchanged for compatibility)
    assign data_valid = (r_current_state == SCHED_DESCRIPTOR_ACTIVE) && (r_data_length > 32'h0);
    assign data_address = r_data_addr;
    assign data_length = r_data_length;
    assign data_type = r_data_type;
    assign data_eos = descriptor_eos;

    // Address alignment bus outputs (using RAPIDS package types)
    assign data_alignment_info = r_alignment_info;
    assign data_alignment_valid = r_alignment_valid;
    assign data_transfer_phase = r_transfer_phase;
    assign data_sequence_complete = r_sequence_complete;

    // Status outputs using RAPIDS package enum
    assign scheduler_idle = (r_current_state == SCHED_IDLE) &&
                        (r_alignment_state == ALIGN_IDLE) &&
                        w_no_pending_operations &&
                        !r_channel_reset_active;

    assign fsm_state = r_current_state;

    // Control operation assignments
    assign descriptor_ready = (r_current_state == SCHED_IDLE) && !r_channel_reset_active;

    // Ctrlrd Engine Interface outputs
    assign ctrlrd_valid = (r_current_state == SCHED_ISSUE_CTRLRD);
    assign ctrlrd_addr = r_ctrlrd_addr;
    assign ctrlrd_data = r_ctrlrd_data;
    assign ctrlrd_mask = r_ctrlrd_mask;

    // Ctrlwr Engine Interface outputs
    assign ctrlwr_valid = (r_current_state == SCHED_ISSUE_CTRLWR0) || (r_current_state == SCHED_ISSUE_CTRLWR1);
    assign ctrlwr_addr = (r_current_state == SCHED_ISSUE_CTRLWR0) ? r_ctrlwr0_addr : r_ctrlwr1_addr;
    assign ctrlwr_data = (r_current_state == SCHED_ISSUE_CTRLWR0) ? r_ctrlwr0_data : r_ctrlwr1_data;

    // Credit management
    assign w_credit_available = !cfg_use_credit || (r_descriptor_credit_counter > 0);
    assign descriptor_credit_counter = r_descriptor_credit_counter;

    // Completion logic
    assign w_descriptor_complete_by_length = (r_data_length == 32'h0) ||
                                        (data_done_strobe && (r_data_length <= data_transfer_length));
    assign w_descriptor_complete_by_eos = r_packet_eos_received || r_stream_boundary_pending;
    assign w_descriptor_complete = w_descriptor_complete_by_length || w_descriptor_complete_by_eos;

    // Control operation needed checks
    assign w_ctrlrd_needed = (r_ctrlrd_addr != 64'h0);
    assign w_ctrlwr0_needed = (r_ctrlwr0_addr != 64'h0);
    assign w_ctrlwr1_needed = (r_ctrlwr1_addr != 64'h0);

    // Monitor outputs
    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    // Error outputs
    assign scheduler_error = (r_current_state == SCHED_ERROR);
    assign backpressure_warning = !w_credit_available || w_timeout_expired;

    //=========================================================================
    // Register Updates (same logic, using RAPIDS package functions where applicable)
    //=========================================================================

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_next_descriptor_addr <= 64'h0;
            r_data_addr <= 64'h0;
            r_data_length <= 32'h0;
            r_ctrlrd_addr <= 64'h0;
            r_ctrlrd_data <= 32'h0;
            r_ctrlrd_mask <= 32'h0;
            r_ctrlwr0_addr <= 64'h0;
            r_ctrlwr0_data <= 32'h0;
            r_ctrlwr1_addr <= 64'h0;
            r_ctrlwr1_data <= 32'h0;
            r_data_type <= 2'b00;
            r_packet_eos_received <= 1'b0;
            r_stream_boundary_pending <= 1'b0;
            // FIXED: Exponential credit encoding:
            //   0→1, 1→2, 2→4, 3→8, ..., 14→16384 (exponential: 2^n)
            //   15→0 (special case: DISABLED - no credits, blocks all operations)
            r_descriptor_credit_counter <= (cfg_initial_credit == 4'hF) ? 32'h00000000 :
                                          (cfg_initial_credit == 4'h0) ? 32'h00000001 :
                                          (32'h1 << cfg_initial_credit);
            r_timeout_counter <= 32'h0;
            r_data_error_sticky <= 1'b0;
            r_ctrlrd_error_sticky <= 1'b0;
            r_ctrlwr_error_sticky <= 1'b0;
            r_channel_reset_active <= 1'b0;
        end else begin
            // Channel reset handling
            r_channel_reset_active <= cfg_channel_reset;

            // Descriptor unpacking and credit decrement
            if ((r_current_state == SCHED_IDLE) && descriptor_valid && descriptor_ready) begin
                // Unpack descriptor fields with new layout

                // Data operation fields (bits 0-95)
                r_data_length <= descriptor_packet[31:0];
                r_data_addr <= {descriptor_packet[95:64], descriptor_packet[63:32]};

                // Next descriptor pointer (bits 96-159)
                r_next_descriptor_addr <= {descriptor_packet[159:128], descriptor_packet[127:96]};

                // Control Read fields (bits 160-287)
                r_ctrlrd_addr <= {descriptor_packet[223:192], descriptor_packet[191:160]};
                r_ctrlrd_data <= descriptor_packet[255:224];
                r_ctrlrd_mask <= descriptor_packet[287:256];

                // Control Write 0 fields (bits 288-383)
                r_ctrlwr0_addr <= {descriptor_packet[351:320], descriptor_packet[319:288]};
                r_ctrlwr0_data <= descriptor_packet[383:352];

                // Control Write 1 fields (bits 384-479)
                r_ctrlwr1_addr <= {descriptor_packet[447:416], descriptor_packet[415:384]};
                r_ctrlwr1_data <= descriptor_packet[479:448];

                // Companion signals
                r_data_type <= descriptor_type;
                r_packet_eos_received <= descriptor_eos;

                // FIXED: Decrement credit on descriptor acceptance (not on data_done_strobe)
                if (cfg_use_credit && (r_descriptor_credit_counter > 0)) begin
                    r_descriptor_credit_counter <= r_descriptor_credit_counter - 1;
                end
            end

            // Data length updates
            if (data_done_strobe && (r_current_state == SCHED_DESCRIPTOR_ACTIVE)) begin
                if (r_data_length >= data_transfer_length) begin
                    r_data_length <= r_data_length - data_transfer_length;
                end else begin
                    r_data_length <= 32'h0;
                end
            end

            // Credit management - increment only (decrement happens on descriptor acceptance above)
            if (cfg_use_credit && credit_increment) begin
                r_descriptor_credit_counter <= r_descriptor_credit_counter + 1;
            end

            // Timeout management
            if (data_valid && !data_ready) begin
                r_timeout_counter <= r_timeout_counter + 1;
            end else begin
                r_timeout_counter <= 32'h0;
            end

            // Error tracking - capture errors when they occur
            if (data_error) r_data_error_sticky <= 1'b1;
            if (ctrlrd_error) r_ctrlrd_error_sticky <= 1'b1;
            if (ctrlwr_error) r_ctrlwr_error_sticky <= 1'b1;

            // Clear sticky errors only when transitioning FROM error state TO idle
            // This ensures errors are held long enough to trigger ERROR state
            if (r_current_state == SCHED_ERROR && w_next_state == SCHED_IDLE) begin
                r_data_error_sticky <= 1'b0;
                r_ctrlrd_error_sticky <= 1'b0;
                r_ctrlwr_error_sticky <= 1'b0;
            end
        end
    end

    // Timeout detection
    assign w_timeout_expired = (r_timeout_counter >= TIMEOUT_CYCLES);

    // Safety checks
    assign w_no_pending_operations = !data_valid && !ctrlrd_valid && !ctrlwr_valid;

endmodule : scheduler
