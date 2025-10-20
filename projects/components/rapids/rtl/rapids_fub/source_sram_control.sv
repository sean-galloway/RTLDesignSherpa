// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: source_sram_control
// Purpose: Source Sram Control module
//
// Documentation: projects/components/rapids_fub/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import monitor package for event codes
import monitor_pkg::*;

module source_sram_control #(
    parameter int CHANNELS = 32,
    parameter int LINES_PER_CHANNEL = 256,
    parameter int DATA_WIDTH = 512,
    parameter int PTR_BITS = $clog2(LINES_PER_CHANNEL) + 1,
    parameter int CHAN_BITS = $clog2(CHANNELS),
    parameter int COUNT_BITS = $clog2(LINES_PER_CHANNEL),
    parameter int SUBLINE_BITS = 4,
    parameter int NUM_CHUNKS = 16,
    parameter int PREALLOC_THRESHOLD = LINES_PER_CHANNEL - 16,
    parameter int OVERFLOW_MARGIN = 8,
    parameter int DEADLOCK_PREVENTION_MARGIN = 32,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h21,      // SRAM Control Agent ID
    parameter logic [3:0] MON_UNIT_ID = 4'h3,        // Unit identifier
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0      // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Enhanced Write Interface (From AXI Engine) with EOS only
    input  logic [CHANNELS-1:0]         wr_valid,
    output logic [CHANNELS-1:0]         wr_ready,
    input  logic [DATA_WIDTH-1:0]       wr_data [CHANNELS],
    input  logic [1:0]                  wr_type [CHANNELS],
    input  logic [CHANNELS-1:0]         wr_eos,
    input  logic [NUM_CHUNKS-1:0]       wr_chunk_valid [CHANNELS],
    input  logic [CHAN_BITS-1:0]        wr_channel [CHANNELS],

    // Enhanced Preallocation Interface (From AXI Engine)
    input  logic                        prealloc_valid,
    output logic                        prealloc_ready,
    input  logic [7:0]                  prealloc_beats,
    input  logic [1:0]                  prealloc_type,
    input  logic [CHAN_BITS-1:0]        prealloc_channel,

    // Enhanced Read Interface (To AXIS Master FUB Interface) with EOS only
    output logic                        rd_valid,
    input  logic                        rd_ready,
    output logic [DATA_WIDTH-1:0]       rd_data,
    output logic [1:0]                  rd_type,
    output logic                        rd_eos,
    output logic [NUM_CHUNKS-1:0]       rd_chunk_valid,
    output logic [CHAN_BITS-1:0]        rd_channel,
    output logic [COUNT_BITS-1:0]       rd_used_count,

    // NEW: Channel Data Availability for AXIS Master
    output logic [CHANNELS-1:0]         loaded_lines,

    // Sub-line Read Interface (for address alignment)
    input  logic [CHANNELS-1:0]         alignment_active,
    input  logic [5:0]                  alignment_size [CHANNELS],

    // Control and Status
    input  logic                        cfg_enable,
    input  logic [CHANNELS-1:0]         cfg_channel_enable,
    output logic [CHANNELS-1:0]         overflow_warning,
    output logic [CHANNELS-1:0]         underflow_error,
    output logic                        prealloc_blocked,

    // Channel Availability Interface (For AXI Read Engine Flow Control)
    output logic [COUNT_BITS-1:0]       available_lines [CHANNELS],
    output logic [CHANNELS-1:0]         channel_ready_for_prealloc,

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    // Monitor event codes - AXIS optimized
    localparam logic [3:0] MON_EOS_STORED = AXIS_COMPL_STREAM_END;        // Stream end completion
    localparam logic [3:0] MON_OVERFLOW_WARNING = CORE_THRESH_THROUGHPUT; // Buffer overflow warning
    localparam logic [3:0] MON_BACKPRESSURE = AXIS_CREDIT_BACKPRESSURE;   // AXIS backpressure event
    localparam logic [3:0] MON_PREALLOC_BLOCKED = CORE_ERR_OVERFLOW;

    //=========================================================================
    // UPDATED: SRAM Configuration (531 bits total - removed EOL/EOD)
    //=========================================================================

    // UPDATED: Reduced SRAM width - removed EOL/EOD
    // Format: {EOS[1], TYPE[2], CHUNK_VALID[16], DATA[512]}
    localparam int SRAM_WIDTH = DATA_WIDTH + NUM_CHUNKS + 3;  // 512 + 16 + 3 = 531 bits
    localparam int TOTAL_LINES = CHANNELS * LINES_PER_CHANNEL;
    localparam int SRAM_ADDR_WIDTH = $clog2(TOTAL_LINES);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // SRAM interface
    logic w_sram_wr_en;
    logic w_sram_rd_en;
    logic [SRAM_WIDTH-1:0] w_sram_wr_data;
    logic [SRAM_WIDTH-1:0] w_sram_rd_data;
    logic [SRAM_ADDR_WIDTH-1:0] w_sram_wr_addr;
    logic [SRAM_ADDR_WIDTH-1:0] w_sram_rd_addr;

    // Pointer management
    logic [PTR_BITS-1:0] r_wr_pointer [CHANNELS];
    logic [PTR_BITS-1:0] r_rd_pointer [CHANNELS];
    logic [COUNT_BITS-1:0] r_used_count [CHANNELS];
    logic [COUNT_BITS-1:0] r_prealloc_count [CHANNELS];

    // Write arbitration
    logic [CHAN_BITS-1:0] r_wr_arb_pointer;
    logic [CHANNELS-1:0] w_wr_request_mask;
    logic [CHANNELS-1:0] w_wr_grant;
    logic [CHAN_BITS-1:0] w_wr_grant_id;
    logic w_wr_grant_valid;

    // Read arbitration
    logic [CHAN_BITS-1:0] r_rd_arb_pointer;
    logic [CHANNELS-1:0] w_rd_request_mask;
    logic [CHANNELS-1:0] w_rd_data_available;

    // Flow control
    logic w_wr_accept;
    logic w_rd_grant;

    // UPDATED: Stream boundary tracking - EOS only
    logic [CHANNELS-1:0] r_eos_pending;
    logic [CHANNELS-1:0] r_eos_barrier_active;

    // Credit return tracking
    logic r_consumption_pending;
    logic [CHAN_BITS-1:0] r_consumption_channel;

    // Error and status tracking
    logic [CHANNELS-1:0] r_overflow_warning;
    logic [CHANNELS-1:0] r_underflow_error;
    logic r_prealloc_blocked;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    //=========================================================================
    // Channel Availability Calculation (For AXI Read Engine Flow Control)
    //=========================================================================

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_availability
            // Calculate available lines for each channel
            assign available_lines[i] = COUNT_BITS'(LINES_PER_CHANNEL) - r_used_count[i] - r_prealloc_count[i];

            // Channel ready for preallocation if it has sufficient margin
            assign channel_ready_for_prealloc[i] = cfg_channel_enable[i] &&
                                    (available_lines[i] > COUNT_BITS'(DEADLOCK_PREVENTION_MARGIN));
        end
    endgenerate

    //=========================================================================
    // NEW: Loaded Lines Signal for AXIS Master Channel Selection
    //=========================================================================

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_loaded_lines
            // Assert loaded_lines when channel has at least one line of data available
            assign loaded_lines[i] = (r_used_count[i] > 0) && cfg_channel_enable[i];
        end
    endgenerate

    //=========================================================================
    // Write Channel Arbitration - FIXED: Priority encoder without break
    //=========================================================================

    // Generate write requests
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_wr_requests
            assign w_wr_request_mask[i] = wr_valid[i] && cfg_channel_enable[i] &&
                            ((COUNT_BITS'(r_used_count[i]) + COUNT_BITS'(r_prealloc_count[i])) <
                                COUNT_BITS'(LINES_PER_CHANNEL - OVERFLOW_MARGIN));
        end
    endgenerate

    // FIXED: Synthesizable round-robin arbitration for write
    logic [CHAN_BITS-1:0] w_wr_selected_channel;
    logic w_wr_channel_found;

    /* verilator lint_off LATCH */
    always_comb begin
        w_wr_selected_channel = '0;
        w_wr_channel_found = 1'b0;

        // Priority encoder using modular arithmetic for round-robin
        if (w_wr_request_mask[r_wr_arb_pointer]) begin
            w_wr_selected_channel = r_wr_arb_pointer;
            w_wr_channel_found = 1'b1;
        end else begin
            // Search for next available channel using if-else chain
            for (int j = 1; j < CHANNELS; j++) begin
                automatic logic [CHAN_BITS-1:0] idx = CHAN_BITS'((int'(r_wr_arb_pointer) + j) % CHANNELS);
                if (!w_wr_channel_found && w_wr_request_mask[idx]) begin
                    w_wr_selected_channel = idx;
                    w_wr_channel_found = 1'b1;
                end
            end
        end
    end
    /* verilator lint_on LATCH */

    assign w_wr_grant_valid = w_wr_channel_found;
    assign w_wr_grant_id = w_wr_selected_channel;

    // Generate grant signals
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_wr_grants
            assign w_wr_grant[i] = w_wr_grant_valid && (w_wr_grant_id == CHAN_BITS'(i));
        end
    endgenerate

    // Update write arbitration pointer
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_wr_arb_pointer <= '0;
        end else begin
            if (w_wr_grant_valid) begin
                r_wr_arb_pointer <= (int'(r_wr_arb_pointer) == (CHANNELS-1)) ? '0 : (r_wr_arb_pointer + 1);
            end
        end
    end

    // Write acceptance logic
    assign w_wr_accept = w_wr_grant_valid;

    // Write ready signals
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_wr_ready
            assign wr_ready[i] = w_wr_grant[i];
        end
    endgenerate

    //=========================================================================
    // SRAM Instance (Single Large SRAM)
    //=========================================================================

    simple_sram #(
        .ADDR_WIDTH     (SRAM_ADDR_WIDTH),
        .DATA_WIDTH     (SRAM_WIDTH),
        .DEPTH          (TOTAL_LINES),
        .NUM_CHUNKS     (1)  // No chunk enables needed at SRAM level
    ) u_sram (
        .clk            (clk),
        .wr_en          (w_sram_wr_en),
        .wr_addr        (w_sram_wr_addr),
        .wr_data        (w_sram_wr_data),
        .wr_chunk_en    (1'b1),
        .rd_en          (w_sram_rd_en),
        .rd_addr        (w_sram_rd_addr),
        .rd_data        (w_sram_rd_data)
    );

    //=========================================================================
    // UPDATED: SRAM Write Interface - EOS only
    //=========================================================================

    // SRAM write enable
    assign w_sram_wr_en = w_wr_accept;

    // UPDATED: Write data composition (531 bits - removed EOL/EOD)
    // Format: {EOS[1], TYPE[2], CHUNK_VALID[16], DATA[512]}
    always_comb begin
        w_sram_wr_data = '0;
        w_sram_wr_addr = '0;

        if (w_wr_grant_valid) begin
            w_sram_wr_data = {wr_eos[w_wr_grant_id],                                    // Bit 530: EOS
                            wr_type[w_wr_grant_id],                                   // Bits 529:528: Type
                            wr_chunk_valid[w_wr_grant_id],                            // Bits 527:512: Chunk enables
                            wr_data[w_wr_grant_id]};                                  // Bits 511:0: Data

            // Write address calculation
            w_sram_wr_addr = SRAM_ADDR_WIDTH'((int'(w_wr_grant_id) * LINES_PER_CHANNEL) +
                                int'(r_wr_pointer[w_wr_grant_id][PTR_BITS-2:0]));
        end
    end

    //=========================================================================
    // Pointer Management
    //=========================================================================

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_pointers
            always_ff @(posedge clk) begin
                if (!rst_n) begin
                    r_wr_pointer[i] <= '0;
                    r_rd_pointer[i] <= '0;
                    r_used_count[i] <= '0;
                    r_prealloc_count[i] <= '0;
                end else begin
                    // Write pointer management
                    if (w_sram_wr_en && (w_wr_grant_id == CHAN_BITS'(i))) begin
                        r_wr_pointer[i] <= r_wr_pointer[i] + 1;
                        if (r_prealloc_count[i] > 0) begin
                            r_prealloc_count[i] <= r_prealloc_count[i] - 1;
                        end else begin
                            r_used_count[i] <= r_used_count[i] + 1;
                        end
                    end

                    // Read pointer management
                    if (w_sram_rd_en && (r_rd_arb_pointer == CHAN_BITS'(i))) begin
                        r_rd_pointer[i] <= r_rd_pointer[i] + 1;
                        if (r_used_count[i] > 0) begin
                            r_used_count[i] <= r_used_count[i] - 1;
                        end
                    end

                    // Preallocation management
                    if (prealloc_valid && prealloc_ready && (prealloc_channel == CHAN_BITS'(i))) begin
                        r_prealloc_count[i] <= r_prealloc_count[i] + prealloc_beats;
                    end
                end
            end
        end
    endgenerate

    //=========================================================================
    // Preallocation Interface
    //=========================================================================

    // Preallocation ready logic
    assign prealloc_ready = cfg_enable &&
                    (int'(prealloc_channel) < CHANNELS) &&
                    cfg_channel_enable[prealloc_channel] &&
                    ((COUNT_BITS'(r_used_count[prealloc_channel]) +
                        COUNT_BITS'(r_prealloc_count[prealloc_channel]) +
                        COUNT_BITS'(prealloc_beats)) <= COUNT_BITS'(PREALLOC_THRESHOLD));

    //=========================================================================
    // Read Arbitration - FIXED: Priority encoder without break
    //=========================================================================

    // Data availability check
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_data_avail
            assign w_rd_data_available[i] = (r_used_count[i] > 0) && cfg_channel_enable[i];
        end
    endgenerate

    // FIXED: Synthesizable round-robin arbitration for reads
    logic [CHAN_BITS-1:0] w_rd_selected_channel;
    logic w_rd_channel_found;

    always_comb begin
        w_rd_selected_channel = r_rd_arb_pointer;
        w_rd_channel_found = 1'b0;

        // Check current pointer first
        if (w_rd_data_available[r_rd_arb_pointer]) begin
            w_rd_channel_found = 1'b1;
        end else begin
            // Search for next available channel using if-else chain without automatic variables
            for (int j = 1; j < CHANNELS; j++) begin
                if (!w_rd_channel_found && w_rd_data_available[CHAN_BITS'((int'(r_rd_arb_pointer) + j) % CHANNELS)]) begin
                    w_rd_selected_channel = CHAN_BITS'((int'(r_rd_arb_pointer) + j) % CHANNELS);
                    w_rd_channel_found = 1'b1;
                end
            end
        end
    end

    assign w_rd_grant = w_rd_channel_found;

    // Update read arbitration pointer to the selected channel
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_rd_arb_pointer <= '0;
        end else begin
            // Update arbitration pointer when read granted
            if (w_rd_grant && rd_ready) begin
                r_rd_arb_pointer <= w_rd_selected_channel;
                // Advance for next time
                r_rd_arb_pointer <= (int'(w_rd_selected_channel) == (CHANNELS-1)) ? '0 : (w_rd_selected_channel + 1);
            end
        end
    end

    //=========================================================================
    // UPDATED: SRAM Read Interface - EOS only
    //=========================================================================

    // SRAM read enable
    assign w_sram_rd_en = w_rd_grant && rd_ready;

    // Read data valid
    assign rd_valid = w_rd_grant;

    // Read address calculation
    assign w_sram_rd_addr = SRAM_ADDR_WIDTH'((int'(w_rd_selected_channel) * LINES_PER_CHANNEL) +
                                        int'(r_rd_pointer[w_rd_selected_channel][PTR_BITS-2:0]));

    // UPDATED: Read data extraction (531 bits - removed EOL/EOD)
    // Format: {EOS[1], TYPE[2], CHUNK_VALID[16], DATA[512]}
    assign rd_data = w_sram_rd_data[DATA_WIDTH-1:0];                            // Bits 511:0: Data
    assign rd_chunk_valid = w_sram_rd_data[DATA_WIDTH+NUM_CHUNKS-1:DATA_WIDTH]; // Bits 527:512: Chunk enables
    assign rd_type = w_sram_rd_data[DATA_WIDTH+NUM_CHUNKS+1:DATA_WIDTH+NUM_CHUNKS]; // Bits 529:528: Type
    assign rd_eos = w_sram_rd_data[DATA_WIDTH+NUM_CHUNKS+2];                    // Bit 530: EOS

    // Output current reading channel and used count
    assign rd_channel = w_rd_selected_channel;
    assign rd_used_count = r_used_count[w_rd_selected_channel];

    //=========================================================================
    // UPDATED: Stream Boundary Management - EOS only
    //=========================================================================

    // EOS tracking only
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_eos_pending <= '0;
            r_eos_barrier_active <= '0;
        end else begin
            for (int i = 0; i < CHANNELS; i++) begin
                // Set EOS pending
                if (w_sram_wr_en && (int'(w_wr_grant_id) == i) && wr_eos[i]) begin
                    r_eos_pending[i] <= 1'b1;
                    r_eos_barrier_active[i] <= 1'b1;
                end

                // Clear EOS state when read
                if (rd_valid && rd_ready && (int'(w_rd_selected_channel) == i) && rd_eos) begin
                    r_eos_pending[i] <= 1'b0;
                    r_eos_barrier_active[i] <= 1'b0;
                end
            end
        end
    end

    //=========================================================================
    // Error Detection and Status
    //=========================================================================

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_status
            always_ff @(posedge clk) begin
                if (!rst_n) begin
                    r_overflow_warning[i] <= 1'b0;
                    r_underflow_error[i] <= 1'b0;
                end else begin
                    // Overflow warning
                    r_overflow_warning[i] <= (COUNT_BITS'(r_used_count[i]) + COUNT_BITS'(r_prealloc_count[i])) >=
                            COUNT_BITS'(LINES_PER_CHANNEL - OVERFLOW_MARGIN);

                    // Underflow error
                    r_underflow_error[i] <= rd_valid && rd_ready && (w_rd_selected_channel == CHAN_BITS'(i)) && (r_used_count[i] == 0);
                end
            end
        end
    endgenerate

    // Preallocation blocked
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_prealloc_blocked <= 1'b0;
        end else begin
            r_prealloc_blocked <= prealloc_valid && !prealloc_ready;
        end
    end

    assign overflow_warning = r_overflow_warning;
    assign underflow_error = r_underflow_error;
    assign prealloc_blocked = r_prealloc_blocked;

    //=========================================================================
    // UPDATED: Monitor Packet Generation - EOS only, FIXED: Priority encoder without break
    //=========================================================================

    // FIXED: Monitor event generation with synthesizable priority encoders
    logic [CHAN_BITS-1:0] w_overflow_channel_encoded;
    logic w_overflow_found;
    logic [CHANNELS-1:0] r_overflow_warning_prev;  // Previous state for edge detection

    // Register previous state for edge detection
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_overflow_warning_prev <= '0;
        end else begin
            r_overflow_warning_prev <= r_overflow_warning;
        end
    end

    // Priority encoder for overflow warning events (rising edge detection)
    always_comb begin
        w_overflow_channel_encoded = '0;
        w_overflow_found = 1'b0;

        if (r_overflow_warning[0] && !r_overflow_warning_prev[0]) begin
            w_overflow_channel_encoded = CHAN_BITS'(0);
            w_overflow_found = 1'b1;
        end else if (r_overflow_warning[1] && !r_overflow_warning_prev[1]) begin
            w_overflow_channel_encoded = CHAN_BITS'(1);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 2 && r_overflow_warning[2] && !r_overflow_warning_prev[2]) begin
            w_overflow_channel_encoded = CHAN_BITS'(2);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 3 && r_overflow_warning[3] && !r_overflow_warning_prev[3]) begin
            w_overflow_channel_encoded = CHAN_BITS'(3);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 4 && r_overflow_warning[4] && !r_overflow_warning_prev[4]) begin
            w_overflow_channel_encoded = CHAN_BITS'(4);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 5 && r_overflow_warning[5] && !r_overflow_warning_prev[5]) begin
            w_overflow_channel_encoded = CHAN_BITS'(5);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 6 && r_overflow_warning[6] && !r_overflow_warning_prev[6]) begin
            w_overflow_channel_encoded = CHAN_BITS'(6);
            w_overflow_found = 1'b1;
        end else if (CHANNELS > 7 && r_overflow_warning[7] && !r_overflow_warning_prev[7]) begin
            w_overflow_channel_encoded = CHAN_BITS'(7);
            w_overflow_found = 1'b1;
        end else begin
            for (int i = 8; i < CHANNELS; i++) begin
                if (!w_overflow_found && r_overflow_warning[i] && !r_overflow_warning_prev[i]) begin
                    w_overflow_channel_encoded = CHAN_BITS'(i);
                    w_overflow_found = 1'b1;
                end
            end
        end
    end

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            r_mon_valid <= 1'b0; // Default

            // EOS storage events (highest priority)
            if (w_sram_wr_en && w_wr_grant_valid && wr_eos[w_wr_grant_id]) begin
                r_mon_valid <= 1'b1;
                r_mon_packet <= create_monitor_packet(
                    PktTypeStream,
                    PROTOCOL_AXIS,
                    MON_EOS_STORED,
                    MON_CHANNEL_ID + w_wr_grant_id,
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    {17'h0, wr_type[w_wr_grant_id], 16'h0}  // FIXED: pad to 35 bits
                );
            end

            // Overflow warning events (use priority encoder result)
            if (!r_mon_valid && w_overflow_found) begin
                r_mon_valid <= 1'b1;
                r_mon_packet <= create_monitor_packet(
                    PktTypeThreshold,
                    PROTOCOL_CORE,
                    MON_OVERFLOW_WARNING,
                    MON_CHANNEL_ID + w_overflow_channel_encoded,
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    {27'h0, r_used_count[w_overflow_channel_encoded]}  // FIXED: pad to 35 bits (27+8=35)
                );
            end

            // Preallocation blocked events
            if (!r_mon_valid && r_prealloc_blocked) begin
                r_mon_valid <= 1'b1;
                r_mon_packet <= create_monitor_packet(
                    PktTypeError,
                    PROTOCOL_CORE,
                    MON_PREALLOC_BLOCKED,
                    MON_CHANNEL_ID + prealloc_channel,
                    MON_UNIT_ID,
                    MON_AGENT_ID,
                    {27'h0, prealloc_beats}  // FIXED: pad to 35 bits (27+8=35)
                );
            end
        end
    end

    //=========================================================================
    // Monitor Bus Output
    //=========================================================================

    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Pointer wraparound safety
    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : gen_assertions
            property pointer_bounds;
                @(posedge clk) disable iff (!rst_n)
                (r_wr_pointer[i][PTR_BITS-2:0] < LINES_PER_CHANNEL) &&
                (r_rd_pointer[i][PTR_BITS-2:0] < LINES_PER_CHANNEL);
            endproperty
            assert property (pointer_bounds);

            property count_consistency;
                @(posedge clk) disable iff (!rst_n)
                (r_used_count[i] + r_prealloc_count[i]) <= LINES_PER_CHANNEL;
            endproperty
            assert property (count_consistency);

            property availability_calculation;
                @(posedge clk) disable iff (!rst_n)
                available_lines[i] == (LINES_PER_CHANNEL - r_used_count[i] - r_prealloc_count[i]);
            endproperty
            assert property (availability_calculation);

            // NEW: loaded_lines property
            property loaded_lines_consistency;
                @(posedge clk) disable iff (!rst_n)
                loaded_lines[i] == ((r_used_count[i] > 0) && cfg_channel_enable[i]);
            endproperty
            assert property (loaded_lines_consistency);
        end
    endgenerate

    // Monitor parameter consistency
    property monitor_agent_id_consistency;
        @(posedge clk) disable iff (!rst_n)
        mon_valid |-> (get_agent_id(mon_packet) == MON_AGENT_ID);
    endproperty
    assert property (monitor_agent_id_consistency);
    `endif

endmodule : source_sram_control
