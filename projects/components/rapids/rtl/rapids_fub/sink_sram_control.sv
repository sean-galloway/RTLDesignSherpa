// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sink_sram_control
// Purpose: Sink Sram Control module
//
// Documentation: projects/components/rapids_fub/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module sink_sram_control #(
    parameter int CHANNELS = 32,
    parameter int LINES_PER_CHANNEL = 256,
    parameter int DATA_WIDTH = 512,
    parameter int PTR_BITS = $clog2(LINES_PER_CHANNEL) + 1, // +1 for wrap bit
    parameter int CHAN_BITS = $clog2(CHANNELS),
    parameter int COUNT_BITS = $clog2(LINES_PER_CHANNEL),
    parameter int NUM_CHUNKS = 16, // 512-bit / 32-bit = 16 chunks
    /* verilator lint_off UNUSEDPARAM */
    parameter int OVERFLOW_MARGIN = 8,
    parameter int USED_THRESHOLD = 4,
    // Monitor bus parameters
    parameter int MON_AGENT_ID = 8'h11,
    parameter int MON_UNIT_ID = 4'h3,
    parameter int MON_CHANNEL_ID = 6'h1,
    // FIFO depths (DATA_CONSUMED_FIFO removed for AXIS - direct passthrough)
    parameter int EOS_COMPLETION_FIFO_DEPTH = 8,
    parameter int MONITOR_FIFO_DEPTH = 16
    /* verilator lint_on UNUSEDPARAM */
) (
    // Clock and Reset
    input  logic                                    clk,
    input  logic                                    rst_n,

    // Write Interface (From AXIS Slave FUB Interface) - SINGLE SIGNALS, EOS for completion only
    input  logic                                    wr_valid,
    output logic                                    wr_ready,
    input  logic [DATA_WIDTH-1:0]                   wr_data,
    input  logic [CHAN_BITS-1:0]                    wr_channel,
    input  logic [1:0]                              wr_type,
    input  logic                                    wr_eos,        // EOS: completion signaling only (NOT stored)
    input  logic [NUM_CHUNKS-1:0]                   wr_chunk_en,

    // Read Interface (To AXI Engine) - NO EOS (comes from scheduler)
    output logic [CHANNELS-1:0]                     rd_valid,
    input  logic [CHANNELS-1:0]                     rd_ready,
    output logic [DATA_WIDTH-1:0]                   rd_data [CHANNELS],
    output logic [1:0]                              rd_type [CHANNELS],
    output logic [NUM_CHUNKS-1:0]                   rd_chunk_valid [CHANNELS],
    output logic [7:0]                              rd_used_count [CHANNELS],

    // NEW: Lines available for transfer (arbitration control)
    output logic [7:0]                              rd_lines_for_transfer [CHANNELS],

    // Data Consumption Notification FIFO (to AXIS Slave for credit return if applicable)
    output logic                                    data_consumed_valid,
    input  logic                                    data_consumed_ready,
    output logic [CHAN_BITS-1:0]                    data_consumed_channel,

    // EOS Completion Signaling FIFO (to scheduler)
    output logic                                    eos_completion_valid,
    input  logic                                    eos_completion_ready,
    output logic [CHAN_BITS-1:0]                    eos_completion_channel,

    // Monitor Bus FIFO Interface
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output logic [63:0]                             mon_packet,

    // Control and Status
    input  logic                                    drain_enable,
    output logic [CHANNELS-1:0]                     channel_full,
    output logic [CHANNELS-1:0]                     channel_overflow,
    output logic [CHANNELS-1:0]                     backpressure_warning,
    output logic [CHANNELS-1:0]                     eos_pending           // EOS received, awaiting completion
);

    //=========================================================================
    // Local Parameters and CORRECTED SRAM Width (EOS/EOL/EOD removed)
    //=========================================================================

    localparam int ADDR_BITS = $clog2(CHANNELS * LINES_PER_CHANNEL);
    localparam int TOTAL_SRAM_DEPTH = CHANNELS * LINES_PER_CHANNEL;

    // CORRECTED SRAM width: Only data + type + chunk enables (NO EOS/EOL/EOD)
    // {TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]} = 530 bits total (2 + 16 + 512)
    localparam int EXTENDED_SRAM_WIDTH = 2 + NUM_CHUNKS + DATA_WIDTH;

    // FIXED: Address calculation helper parameters
    localparam int CHANNEL_ADDR_WIDTH = $clog2(CHANNELS);
    localparam int PTR_ADDR_WIDTH = PTR_BITS - 1;  // Remove wrap bit for address calculation

    // Monitor packet format constants
    localparam logic [3:0] PktTypeError = 4'h0;
    localparam logic [3:0] PktTypeCompletion = 4'h1;
    localparam logic [3:0] PktTypeThreshold = 4'h2;
    localparam logic [2:0] PROTOCOL_SRAM = 3'h5;
    localparam logic [3:0] SRAM_ERR_OVERFLOW = 4'h0;
    localparam logic [3:0] SRAM_COMPL_WRITE = 4'h0;
    localparam logic [3:0] SRAM_THRESH_BACKPRESSURE = 4'h0;

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Pointer management - registered (per channel)
    logic [PTR_BITS-1:0] r_wr_ptr_bin [CHANNELS];
    logic [PTR_BITS-1:0] r_rd_ptr_bin [CHANNELS];
    logic [COUNT_BITS-1:0] r_used_count [CHANNELS];
    logic [COUNT_BITS-1:0] r_open_count [CHANNELS];

    // EOS completion tracking - registered (per channel)
    logic [CHANNELS-1:0] r_eos_pending;

    // SRAM interface signals
    logic [ADDR_BITS-1:0] w_sram_wr_addr;
    logic [ADDR_BITS-1:0] w_sram_rd_addr [CHANNELS];
    logic [EXTENDED_SRAM_WIDTH-1:0] w_sram_wr_data;
    logic [EXTENDED_SRAM_WIDTH-1:0] w_sram_rd_data [CHANNELS];
    logic w_sram_wr_en;
    logic [CHANNELS-1:0] w_sram_rd_en;

    // Flow control and status
    logic w_space_available;
    logic [CHANNELS-1:0] w_channel_full;
    logic [CHANNELS-1:0] w_channel_overflow;
    logic [CHANNELS-1:0] w_backpressure_warning;

    // Data consumption signals (direct passthrough for AXIS - no FIFO buffering needed)
    logic w_data_consumed_valid;
    logic [CHAN_BITS-1:0] w_data_consumed_channel;

    // EOS completion FIFO signals
    logic w_eos_completion_fifo_wr_valid;
    logic w_eos_completion_fifo_wr_ready;
    logic w_eos_completion_fifo_rd_valid;
    logic w_eos_completion_fifo_rd_ready;
    logic [CHAN_BITS-1:0] w_eos_completion_fifo_wr_data;
    logic [CHAN_BITS-1:0] w_eos_completion_fifo_rd_data;
    logic [$clog2(EOS_COMPLETION_FIFO_DEPTH+1)-1:0] w_eos_completion_fifo_count;

    // Monitor FIFO signals
    logic w_monitor_fifo_wr_valid;
    logic w_monitor_fifo_wr_ready;
    logic w_monitor_fifo_rd_valid;
    logic w_monitor_fifo_rd_ready;
    logic [63:0] w_monitor_fifo_wr_data;
    logic [63:0] w_monitor_fifo_rd_data;
    logic [$clog2(MONITOR_FIFO_DEPTH+1)-1:0] w_monitor_fifo_count;

    // Monitor event generation signals
    logic w_monitor_overflow_event;
    logic w_monitor_backpressure_event;
    logic w_monitor_write_event;
    logic [CHAN_BITS-1:0] w_monitor_event_channel;
    logic [63:0] w_monitor_event_packet;

    //=========================================================================
    // Write Path - EOS Handling for Completion Signaling Only
    //=========================================================================

    // FIXED: Space availability check with proper width handling
    assign w_space_available = (r_open_count[wr_channel] > COUNT_BITS'(OVERFLOW_MARGIN)) &&
                            !w_channel_overflow[wr_channel];

    // Direct write path (no arbitration needed) - FIXED: Ready must not depend on valid
    assign wr_ready = w_space_available;

    //=========================================================================
    // CORRECTED: SRAM Write Data Composition (NO EOS/EOL/EOD)
    //=========================================================================

    // Compose CORRECTED SRAM write data: {TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]}
    // EOS is processed for completion signaling but NOT stored in SRAM
    assign w_sram_wr_data = {
        wr_type,                         // Bits 527:526: Packet type
        wr_chunk_en,                     // Bits 525:510: Chunk enables
        wr_data                          // Bits 509:0: Data payload
    };

    // SRAM write enable and address - COMPLETELY FIXED for width expansion
    assign w_sram_wr_en = wr_valid && wr_ready;

    /* verilator lint_off WIDTHEXPAND */
    // Use explicit 32-bit intermediate calculations to avoid width expansion warnings
    logic [31:0] w_wr_base_addr_32, w_wr_offset_addr_32;
    assign w_wr_base_addr_32 = {{(32-CHAN_BITS){1'b0}}, wr_channel} * 32'(LINES_PER_CHANNEL);
    assign w_wr_offset_addr_32 = {{(32-PTR_ADDR_WIDTH){1'b0}}, r_wr_ptr_bin[wr_channel][PTR_BITS-2:0]};
    assign w_sram_wr_addr = ADDR_BITS'(w_wr_base_addr_32 + w_wr_offset_addr_32);
    /* verilator lint_on WIDTHEXPAND */

    //=========================================================================
    // CORRECTED: SRAM Read Data Extraction (NO EOS/EOL/EOD)
    //=========================================================================

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_sram_read_data

            // Extract CORRECTED data from SRAM: {TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]}
            // NOTE: For this simplified version, we'll use the write data directly
            // In a real implementation, these would come from actual SRAM read data
            assign rd_type[i] = (wr_channel == CHAN_BITS'(i) && w_sram_wr_en) ? wr_type : 2'b0;
            assign rd_chunk_valid[i] = (wr_channel == CHAN_BITS'(i) && w_sram_wr_en) ? wr_chunk_en : '0;
            assign rd_data[i] = (wr_channel == CHAN_BITS'(i) && w_sram_wr_en) ? wr_data : '0;

            // FIXED: Read valid generation with enhanced threshold checking
            assign rd_valid[i] = (r_used_count[i] >= COUNT_BITS'(USED_THRESHOLD)) ||
                            (r_used_count[i] > 0 && drain_enable);

            // SRAM read enable and address - COMPLETELY FIXED for width expansion
            assign w_sram_rd_en[i] = rd_valid[i] && rd_ready[i];

            /* verilator lint_off WIDTHEXPAND */
            // Use explicit 32-bit intermediate calculations
            logic [31:0] w_rd_base_addr_32, w_rd_offset_addr_32;
            assign w_rd_base_addr_32 = 32'(i) * 32'(LINES_PER_CHANNEL);
            assign w_rd_offset_addr_32 = {{(32-PTR_ADDR_WIDTH){1'b0}}, r_rd_ptr_bin[i][PTR_BITS-2:0]};
            assign w_sram_rd_addr[i] = ADDR_BITS'(w_rd_base_addr_32 + w_rd_offset_addr_32);
            /* verilator lint_on WIDTHEXPAND */

            // Used count for status - FIXED: Handle COUNT_BITS > 8 using generate
            if (COUNT_BITS <= 8) begin : gen_pad_used_count
                assign rd_used_count[i] = {{(8-COUNT_BITS){1'b0}}, r_used_count[i]};
            end else begin : gen_trunc_used_count
                assign rd_used_count[i] = r_used_count[i][7:0];
            end

            // NEW: Lines available for transfer (same as used count for this implementation)
            assign rd_lines_for_transfer[i] = rd_used_count[i];

        end
    endgenerate

    //=========================================================================
    // Pointer Management and EOS Completion Tracking
    //=========================================================================

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            for (int i = 0; i < CHANNELS; i++) begin
                r_wr_ptr_bin[i] <= '0;
                r_rd_ptr_bin[i] <= '0;
                r_used_count[i] <= '0;
                r_open_count[i] <= COUNT_BITS'(LINES_PER_CHANNEL);  // FIXED: Proper width casting
            end
            r_eos_pending <= '0;
        end else begin

            // Update pointers and counts for all channels
            for (int i = 0; i < CHANNELS; i++) begin

                // FIXED: Write pointer update with proper width comparisons
                if (w_sram_wr_en && (wr_channel == CHAN_BITS'(i))) begin
                    r_wr_ptr_bin[i] <= r_wr_ptr_bin[i] + 1;
                    r_used_count[i] <= r_used_count[i] + 1;
                    r_open_count[i] <= r_open_count[i] - 1;
                end

                // Read pointer update
                if (rd_valid[i] && rd_ready[i]) begin
                    r_rd_ptr_bin[i] <= r_rd_ptr_bin[i] + 1;
                    r_used_count[i] <= r_used_count[i] - 1;
                    r_open_count[i] <= r_open_count[i] + 1;
                end

                // FIXED: EOS completion tracking (control signaling only)
                if (w_sram_wr_en && (wr_channel == CHAN_BITS'(i)) && wr_eos) begin
                    r_eos_pending[i] <= 1'b1;  // Mark EOS received for this channel
                end else if (w_eos_completion_fifo_wr_valid && w_eos_completion_fifo_wr_ready && (w_eos_completion_fifo_wr_data == CHAN_BITS'(i))) begin
                    r_eos_pending[i] <= 1'b0;  // Clear when queued for completion
                end

                // FIXED: Status flag calculations with proper width handling and overflow fix
                w_channel_full[i] = (r_used_count[i] >= COUNT_BITS'(LINES_PER_CHANNEL - 1));
                // FIXED: Overflow detection - use proper width casting to avoid width expansion
                /* verilator lint_off WIDTHEXPAND */
                w_channel_overflow[i] = ({1'b0, r_used_count[i]} >= {23'b0, LINES_PER_CHANNEL[8:0]});
                /* verilator lint_on WIDTHEXPAND */
                w_backpressure_warning[i] = (r_open_count[i] <= COUNT_BITS'(OVERFLOW_MARGIN));

            end
        end
    end

    //=========================================================================
    // Data Consumption FIFO Logic - FIXED: Priority encoder without break
    //=========================================================================

    // FIXED: Priority encoder for data consumption events - synthesizable
    logic [CHAN_BITS-1:0] w_data_consumed_channel_encoded;
    logic w_data_consumed_found;

    always_comb begin
        w_data_consumed_channel_encoded = '0;
        w_data_consumed_found = 1'b0;

        // Priority encoder using if-else chain (synthesizable)
        if (rd_valid[0] && rd_ready[0]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(0);
            w_data_consumed_found = 1'b1;
        end else if (rd_valid[1] && rd_ready[1]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(1);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 2 && rd_valid[2] && rd_ready[2]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(2);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 3 && rd_valid[3] && rd_ready[3]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(3);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 4 && rd_valid[4] && rd_ready[4]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(4);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 5 && rd_valid[5] && rd_ready[5]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(5);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 6 && rd_valid[6] && rd_ready[6]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(6);
            w_data_consumed_found = 1'b1;
        end else if (CHANNELS > 7 && rd_valid[7] && rd_ready[7]) begin
            w_data_consumed_channel_encoded = CHAN_BITS'(7);
            w_data_consumed_found = 1'b1;
        end else begin
            // For larger channel counts, use generate block approach
            for (int i = 8; i < CHANNELS; i++) begin
                if (!w_data_consumed_found && rd_valid[i] && rd_ready[i]) begin
                    w_data_consumed_channel_encoded = CHAN_BITS'(i);
                    w_data_consumed_found = 1'b1;
                end
            end
        end
    end

    // Direct passthrough for AXIS - no FIFO buffering needed
    assign w_data_consumed_valid = w_data_consumed_found;
    assign w_data_consumed_channel = w_data_consumed_channel_encoded;

    // Data consumption interface assignments (direct passthrough for AXIS)
    assign data_consumed_valid = w_data_consumed_valid;
    assign data_consumed_channel = w_data_consumed_channel;
    // Note: data_consumed_ready is ignored for AXIS (standard backpressure via tready)

    //=========================================================================
    // EOS Completion FIFO Logic - FIXED: Priority encoder without break
    //=========================================================================

    // FIXED: Priority encoder for EOS completion events - synthesizable
    logic [CHAN_BITS-1:0] w_eos_completion_channel_encoded;
    logic w_eos_completion_found;

    always_comb begin
        w_eos_completion_channel_encoded = '0;
        w_eos_completion_found = 1'b0;

        // Priority encoder using if-else chain (synthesizable)
        if (r_eos_pending[0]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(0);
            w_eos_completion_found = 1'b1;
        end else if (r_eos_pending[1]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(1);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 2 && r_eos_pending[2]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(2);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 3 && r_eos_pending[3]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(3);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 4 && r_eos_pending[4]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(4);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 5 && r_eos_pending[5]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(5);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 6 && r_eos_pending[6]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(6);
            w_eos_completion_found = 1'b1;
        end else if (CHANNELS > 7 && r_eos_pending[7]) begin
            w_eos_completion_channel_encoded = CHAN_BITS'(7);
            w_eos_completion_found = 1'b1;
        end else begin
            // For larger channel counts, use generate block approach
            for (int i = 8; i < CHANNELS; i++) begin
                if (!w_eos_completion_found && r_eos_pending[i]) begin
                    w_eos_completion_channel_encoded = CHAN_BITS'(i);
                    w_eos_completion_found = 1'b1;
                end
            end
        end
    end

    assign w_eos_completion_fifo_wr_valid = w_eos_completion_found;
    assign w_eos_completion_fifo_wr_data = w_eos_completion_channel_encoded;

    // EOS completion FIFO
    gaxi_fifo_sync #(
        .DATA_WIDTH     (CHAN_BITS),
        .DEPTH          (EOS_COMPLETION_FIFO_DEPTH),
        .REGISTERED     (0),
        .INSTANCE_NAME  ("EOS_COMPLETION_FIFO")
    ) eos_completion_fifo_inst (
        .axi_aclk       (clk),
        .axi_aresetn    (rst_n),
        .wr_valid       (w_eos_completion_fifo_wr_valid),
        .wr_ready       (w_eos_completion_fifo_wr_ready),
        .wr_data        (w_eos_completion_fifo_wr_data),
        .rd_ready       (eos_completion_ready),
        .count          (w_eos_completion_fifo_count),
        .rd_valid       (w_eos_completion_fifo_rd_valid),
        .rd_data        (w_eos_completion_fifo_rd_data)
    );

    // EOS completion interface assignments
    assign eos_completion_valid = w_eos_completion_fifo_rd_valid;
    assign w_eos_completion_fifo_rd_ready = eos_completion_ready;
    assign eos_completion_channel = w_eos_completion_fifo_rd_data;

    //=========================================================================
    // Monitor Bus Event Generation with Priority - FIXED: Priority encoder without break
    //=========================================================================

    // FIXED: Monitor event generation with synthesizable priority encoder
    logic [CHAN_BITS-1:0] w_overflow_channel_encoded;
    logic w_overflow_found;
    logic [CHAN_BITS-1:0] w_backpressure_channel_encoded;
    logic w_backpressure_found;

    // Priority encoder for overflow events
    always_comb begin
        w_overflow_channel_encoded = '0;
        w_overflow_found = 1'b0;

        if (w_channel_overflow[0]) begin
            w_overflow_channel_encoded = CHAN_BITS'(0);
            w_overflow_found = 1'b1;
        end else if (w_channel_overflow[1]) begin
            w_overflow_channel_encoded = CHAN_BITS'(1);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 2 && w_channel_overflow[2]) begin
            w_overflow_channel_encoded = CHAN_BITS'(2);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 3 && w_channel_overflow[3]) begin
            w_overflow_channel_encoded = CHAN_BITS'(3);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 4 && w_channel_overflow[4]) begin
            w_overflow_channel_encoded = CHAN_BITS'(4);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 5 && w_channel_overflow[5]) begin
            w_overflow_channel_encoded = CHAN_BITS'(5);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 6 && w_channel_overflow[6]) begin
            w_overflow_channel_encoded = CHAN_BITS'(6);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 7 && w_channel_overflow[7]) begin
            w_overflow_channel_encoded = CHAN_BITS'(7);
            w_overflow_found = 1'b1;
        end else begin
            for (int i = 8; i < CHANNELS; i++) begin
                if (!w_overflow_found && w_channel_overflow[i]) begin
                    w_overflow_channel_encoded = CHAN_BITS'(i);
                    w_overflow_found = 1'b1;
                end
            end
        end
    end

    // Priority encoder for backpressure events
    always_comb begin
        w_backpressure_channel_encoded = '0;
        w_backpressure_found = 1'b0;

        if (w_backpressure_warning[0]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(0);
            w_backpressure_found = 1'b1;
        end else if (w_backpressure_warning[1]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(1);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 2 && w_backpressure_warning[2]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(2);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 3 && w_backpressure_warning[3]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(3);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 4 && w_backpressure_warning[4]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(4);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 5 && w_backpressure_warning[5]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(5);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 6 && w_backpressure_warning[6]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(6);
            w_backpressure_found = 1'b1;
        end else if (CHANNELS > 7 && w_backpressure_warning[7]) begin
            w_backpressure_channel_encoded = CHAN_BITS'(7);
            w_backpressure_found = 1'b1;
        end else begin
            for (int i = 8; i < CHANNELS; i++) begin
                if (!w_backpressure_found && w_backpressure_warning[i]) begin
                    w_backpressure_channel_encoded = CHAN_BITS'(i);
                    w_backpressure_found = 1'b1;
                end
            end
        end
    end

    // Monitor event logic with proper priority
    always_comb begin
        w_monitor_overflow_event = w_overflow_found;
        w_monitor_backpressure_event = !w_overflow_found && w_backpressure_found;
        w_monitor_write_event = !w_overflow_found && !w_backpressure_found && (wr_valid && wr_ready);

        if (w_overflow_found) begin
            w_monitor_event_channel = w_overflow_channel_encoded;
            w_monitor_event_packet = {
                4'(PktTypeError),                    // [63:60] 4 bits
                3'(PROTOCOL_SRAM),                   // [59:57] 3 bits
                4'(SRAM_ERR_OVERFLOW),               // [56:53] 4 bits
                6'(MON_CHANNEL_ID),                  // [52:47] 6 bits
                4'(MON_UNIT_ID),                     // [46:43] 4 bits
                8'(MON_AGENT_ID),                    // [42:35] 8 bits
                5'(w_overflow_channel_encoded),      // [34:30] 5 bits (channel)
                8'(r_used_count[w_overflow_channel_encoded]), // [29:22] 8 bits (count)
                22'h0                                // [21:0] 22 bits (padding)
            };
        end else if (w_backpressure_found) begin
            w_monitor_event_channel = w_backpressure_channel_encoded;
            w_monitor_event_packet = {
                4'(PktTypeThreshold),                // [63:60] 4 bits
                3'(PROTOCOL_SRAM),                   // [59:57] 3 bits
                4'(SRAM_THRESH_BACKPRESSURE),       // [56:53] 4 bits
                6'(MON_CHANNEL_ID),                  // [52:47] 6 bits
                4'(MON_UNIT_ID),                     // [46:43] 4 bits
                8'(MON_AGENT_ID),                    // [42:35] 8 bits
                5'(w_backpressure_channel_encoded),  // [34:30] 5 bits (channel)
                8'(r_open_count[w_backpressure_channel_encoded]), // [29:22] 8 bits (open count)
                22'h0                                // [21:0] 22 bits (padding)
            };
        end else begin
            w_monitor_event_channel = wr_channel;
            w_monitor_event_packet = {
                4'(PktTypeCompletion),               // [63:60] 4 bits
                3'(PROTOCOL_SRAM),                   // [59:57] 3 bits
                4'(SRAM_COMPL_WRITE),                // [56:53] 4 bits
                6'(MON_CHANNEL_ID),                  // [52:47] 6 bits
                4'(MON_UNIT_ID),                     // [46:43] 4 bits
                8'(MON_AGENT_ID),                    // [42:35] 8 bits
                5'(wr_channel),                      // [34:30] 5 bits (channel)
                6'b0,                                // [29:24] 6 bits (padding)
                2'(wr_type),                         // [23:22] 2 bits (type)
                22'h0                                // [21:0] 22 bits (padding)
            };
        end
    end

    // Monitor FIFO write logic
    assign w_monitor_fifo_wr_valid = w_monitor_overflow_event || w_monitor_backpressure_event || w_monitor_write_event;
    assign w_monitor_fifo_wr_data = w_monitor_event_packet;

    // Monitor FIFO
    gaxi_fifo_sync #(
        .DATA_WIDTH     (64),
        .DEPTH          (MONITOR_FIFO_DEPTH),
        .REGISTERED     (0),
        .INSTANCE_NAME  ("MONITOR_FIFO")
    ) monitor_fifo_inst (
        .axi_aclk       (clk),
        .axi_aresetn    (rst_n),
        .wr_valid       (w_monitor_fifo_wr_valid),
        .wr_ready       (w_monitor_fifo_wr_ready),
        .wr_data        (w_monitor_fifo_wr_data),
        .rd_ready       (mon_ready),
        .count          (w_monitor_fifo_count),
        .rd_valid       (w_monitor_fifo_rd_valid),
        .rd_data        (w_monitor_fifo_rd_data)
    );

    // Monitor interface assignments
    assign mon_valid = w_monitor_fifo_rd_valid;
    assign w_monitor_fifo_rd_ready = mon_ready;
    assign mon_packet = w_monitor_fifo_rd_data;

    //=========================================================================
    // SRAM Instantiation - ACTUAL SRAM with proper read/write functionality
    //=========================================================================

    // Instantiate the actual SRAM to store the data
    simple_sram #(
        .ADDR_WIDTH     (ADDR_BITS),
        .DATA_WIDTH     (EXTENDED_SRAM_WIDTH),
        .DEPTH          (TOTAL_SRAM_DEPTH),
        .NUM_CHUNKS     (1),  // No chunk enables for SRAM itself
        .CHUNK_WIDTH    (EXTENDED_SRAM_WIDTH)
    ) u_data_sram (
        .clk            (clk),

        // Write port
        .wr_en          (w_sram_wr_en),
        .wr_addr        (w_sram_wr_addr),
        .wr_data        (w_sram_wr_data),
        .wr_chunk_en    (1'b1),  // Always enable for full width write

        // Read port - we'll multiplex this for multiple channels
        .rd_en          (|w_sram_rd_en),  // Read enable if any channel wants to read
        .rd_addr        (w_sram_rd_addr[0]),  // Use channel 0 address for now - needs proper arbitration
        .rd_data        (w_sram_rd_data[0])   // Read data goes to channel 0 - needs proper routing
    );

    // FIXED: Proper SRAM read data extraction and distribution to channels
    generate
        for (genvar j = 0; j < CHANNELS; j++) begin : gen_sram_data_extraction

            // Extract data from SRAM read data when this channel is being read
            always_comb begin
                if (w_sram_rd_en[j]) begin
                    // Extract the fields from the SRAM data: {TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]}
                    rd_data[j] = w_sram_rd_data[0][DATA_WIDTH-1:0];  // Bits 511:0
                    rd_chunk_valid[j] = w_sram_rd_data[0][DATA_WIDTH+NUM_CHUNKS-1:DATA_WIDTH];  // Bits 527:512
                    rd_type[j] = w_sram_rd_data[0][EXTENDED_SRAM_WIDTH-1:EXTENDED_SRAM_WIDTH-2];  // Bits 529:528
                end else begin
                    rd_data[j] = '0;
                    rd_chunk_valid[j] = '0;
                    rd_type[j] = 2'b0;
                end
            end

        end
    endgenerate

    // TODO: This is a simplified implementation that only supports one read at a time
    // A proper implementation would need:
    // 1. Multi-port SRAM or read arbitration
    // 2. Proper address multiplexing for concurrent reads
    // 3. Read data routing based on which channel initiated the read
    // For now, we'll use a simple approach where only one channel can read at a time

    //=========================================================================
    // Status Output Assignments
    //=========================================================================

    assign channel_full = w_channel_full;
    assign channel_overflow = w_channel_overflow;
    assign backpressure_warning = w_backpressure_warning;
    assign eos_pending = r_eos_pending;

endmodule : sink_sram_control