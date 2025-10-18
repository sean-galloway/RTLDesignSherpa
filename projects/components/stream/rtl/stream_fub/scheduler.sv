//////////////////////////////////////////////////////////////////////////////////
// Company:  Cornami, Inc.
//           Copyright (c) 2025 by Cornami, Inc. All rights reserved.
//
// Engineer: STREAM RTL v1.0
//
// Module Name   : scheduler
// Project Name  : STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
// Target Devices: ASIC/FPGA
// Tool versions : Verilator compatible
// Description   : STREAM Scheduler - Simplified from RAPIDS
//                 - Coordinates descriptor-based transfers (memory-to-memory only)
//                 - No credit management (simple transaction limits)
//                 - No address alignment fixup (aligned addresses required)
//                 - No control engines (ctrlrd/ctrlwr)
//                 - Configurable burst lengths via registers
//                 - 8 channels maximum
//
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"

module scheduler #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int TIMEOUT_CYCLES = 1000,
    // Monitor Bus Parameters
    parameter logic [7:0] MON_AGENT_ID = 8'h40,      // STREAM Scheduler Agent ID
    parameter logic [3:0] MON_UNIT_ID = 4'h1,        // Unit identifier
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0      // Base channel ID
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Configuration Interface
    input  logic                        cfg_channel_enable,     // Enable this channel
    input  logic                        cfg_channel_reset,      // Channel reset

    // Status Interface
    output logic                        scheduler_idle,         // Scheduler idle
    output logic [3:0]                  scheduler_state,        // Current state (for debug)

    // Descriptor Engine Interface
    input  logic                        descriptor_valid,
    output logic                        descriptor_ready,
    input  logic [DATA_WIDTH-1:0]       descriptor_packet,

    // Data Read Interface (to AXI Read Engine via Arbiter)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        datard_valid,           // Request read access
    input  logic                        datard_ready,           // Engine granted access
    output logic [ADDR_WIDTH-1:0]       datard_addr,            // Source address (aligned)
    output logic [31:0]                 datard_beats_remaining, // Total beats left to read
    output logic [3:0]                  datard_channel_id,      // Channel ID

    // Data Write Interface (to AXI Write Engine via Arbiter)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        datawr_valid,           // Request write access
    input  logic                        datawr_ready,           // Engine granted access
    output logic [ADDR_WIDTH-1:0]       datawr_addr,            // Destination address (aligned)
    output logic [31:0]                 datawr_beats_remaining, // Total beats left to write
    output logic [3:0]                  datawr_channel_id,      // Channel ID

    // Data Path Completion Strobes
    input  logic                        datard_done_strobe,     // Read engine completed beats
    input  logic [31:0]                 datard_beats_done,      // Number of beats completed
    input  logic                        datawr_done_strobe,     // Write engine completed beats
    input  logic [31:0]                 datawr_beats_done,      // Number of beats completed

    // Error Signals
    input  logic                        datard_error,           // Read engine error
    input  logic                        datawr_error,           // Write engine error

    // Monitor Bus Interface
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    // Descriptor field offsets (from stream_pkg.sv)
    localparam int DESC_SRC_ADDR_LO  = 0;
    localparam int DESC_SRC_ADDR_HI  = 63;
    localparam int DESC_DST_ADDR_LO  = 64;
    localparam int DESC_DST_ADDR_HI  = 127;
    localparam int DESC_LENGTH_LO    = 128;
    localparam int DESC_LENGTH_HI    = 159;
    localparam int DESC_NEXT_PTR_LO  = 160;
    localparam int DESC_NEXT_PTR_HI  = 191;
    localparam int DESC_VALID_BIT    = 192;
    localparam int DESC_INTERRUPT    = 193;
    localparam int DESC_LAST         = 194;

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Scheduler FSM (using STREAM package enum)
    channel_state_t r_current_state, w_next_state;

    // Channel reset management
    logic r_channel_reset_active;

    // Descriptor fields
    descriptor_t r_descriptor;
    logic r_descriptor_loaded;

    // Transfer tracking
    logic [ADDR_WIDTH-1:0] r_src_addr;
    logic [ADDR_WIDTH-1:0] r_dst_addr;
    logic [31:0] r_beats_remaining;
    logic [31:0] r_read_beats_remaining;
    logic [31:0] r_write_beats_remaining;

    // Timeout tracking
    logic [31:0] r_timeout_counter;
    logic w_timeout_expired;

    // Error tracking
    logic r_read_error_sticky;
    logic r_write_error_sticky;

    // Monitor packet generation
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    // Completion flags
    logic w_read_complete;
    logic w_write_complete;
    logic w_transfer_complete;

    //=========================================================================
    // Channel Reset Management
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_channel_reset_active <= 1'b0;
        end else begin
            r_channel_reset_active <= cfg_channel_reset;
        end
    end

    //=========================================================================
    // Scheduler FSM
    //=========================================================================

    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_current_state <= CH_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    end

    // Next state logic
    always_comb begin
        w_next_state = r_current_state;

        // Force idle during reset
        if (r_channel_reset_active) begin
            w_next_state = CH_IDLE;
        end else begin
            // Error handling
            if (datard_error || datawr_error || r_read_error_sticky || r_write_error_sticky || w_timeout_expired) begin
                w_next_state = CH_ERROR;
            end else begin
                case (r_current_state)
                    CH_IDLE: begin
                        // Wait for descriptor and channel enable
                        if (descriptor_valid && cfg_channel_enable) begin
                            w_next_state = CH_FETCH_DESC;
                        end
                    end

                    CH_FETCH_DESC: begin
                        // Descriptor fetched in one cycle
                        // Check for chained descriptor or start transfer
                        if (r_descriptor.valid) begin
                            w_next_state = CH_READ_DATA;
                        end else begin
                            w_next_state = CH_ERROR;  // Invalid descriptor
                        end
                    end

                    CH_READ_DATA: begin
                        // Reading source data
                        if (w_read_complete) begin
                            w_next_state = CH_WRITE_DATA;
                        end
                    end

                    CH_WRITE_DATA: begin
                        // Writing destination data
                        if (w_write_complete) begin
                            w_next_state = CH_COMPLETE;
                        end
                    end

                    CH_COMPLETE: begin
                        // Check for chained descriptor
                        if (r_descriptor.next_descriptor_ptr != 32'h0 && !r_descriptor.last) begin
                            w_next_state = CH_NEXT_DESC;
                        end else begin
                            w_next_state = CH_IDLE;
                        end
                    end

                    CH_NEXT_DESC: begin
                        // Fetch next chained descriptor
                        // Note: Descriptor engine will fetch based on next_descriptor_ptr
                        if (descriptor_valid) begin
                            w_next_state = CH_FETCH_DESC;
                        end
                    end

                    CH_ERROR: begin
                        // Error state - wait for reset or error clear
                        if (!datard_error && !datawr_error && !r_read_error_sticky && !r_write_error_sticky) begin
                            w_next_state = CH_IDLE;
                        end
                    end

                    default: begin
                        w_next_state = CH_ERROR;
                    end
                endcase
            end
        end
    end

    //=========================================================================
    // Descriptor Register Updates
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_descriptor <= '0;
            r_descriptor_loaded <= 1'b0;
            r_src_addr <= 64'h0;
            r_dst_addr <= 64'h0;
            r_beats_remaining <= 32'h0;
            r_read_beats_remaining <= 32'h0;
            r_write_beats_remaining <= 32'h0;
        end else begin
            case (r_current_state)
                CH_IDLE: begin
                    if (descriptor_valid && descriptor_ready) begin
                        // Latch descriptor
                        r_descriptor.src_addr <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
                        r_descriptor.dst_addr <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
                        r_descriptor.length <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
                        r_descriptor.next_descriptor_ptr <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
                        r_descriptor.valid <= descriptor_packet[DESC_VALID_BIT];
                        r_descriptor.interrupt <= descriptor_packet[DESC_INTERRUPT];
                        r_descriptor.last <= descriptor_packet[DESC_LAST];

                        r_descriptor_loaded <= 1'b1;
                    end
                end

                CH_FETCH_DESC: begin
                    // Initialize transfer tracking
                    r_src_addr <= r_descriptor.src_addr;
                    r_dst_addr <= r_descriptor.dst_addr;
                    r_beats_remaining <= r_descriptor.length;
                    r_read_beats_remaining <= r_descriptor.length;
                    r_write_beats_remaining <= r_descriptor.length;
                end

                CH_READ_DATA: begin
                    // Update on read completion strobe
                    if (datard_done_strobe) begin
                        r_read_beats_remaining <= (r_read_beats_remaining >= datard_beats_done) ?
                                                 (r_read_beats_remaining - datard_beats_done) : 32'h0;
                    end
                end

                CH_WRITE_DATA: begin
                    // Update on write completion strobe
                    if (datawr_done_strobe) begin
                        r_write_beats_remaining <= (r_write_beats_remaining >= datawr_beats_done) ?
                                                  (r_write_beats_remaining - datawr_beats_done) : 32'h0;
                    end
                end

                CH_COMPLETE: begin
                    r_descriptor_loaded <= 1'b0;
                end

                default: begin
                    // Maintain state
                end
            endcase

            // Reset tracking during channel reset
            if (r_channel_reset_active) begin
                r_descriptor_loaded <= 1'b0;
                r_read_beats_remaining <= 32'h0;
                r_write_beats_remaining <= 32'h0;
            end
        end
    end

    //=========================================================================
    // Completion Logic
    //=========================================================================

    assign w_read_complete = (r_read_beats_remaining == 32'h0);
    assign w_write_complete = (r_write_beats_remaining == 32'h0);
    assign w_transfer_complete = w_read_complete && w_write_complete;

    //=========================================================================
    // Data Read Interface Outputs
    //=========================================================================
    // Scheduler tells engine: "I need this many beats from this address"
    // Engine decides: "I'll do X beats per burst based on my config/design"
    // Engine reports back: "I moved X beats" via datard_done_strobe

    assign datard_valid = (r_current_state == CH_READ_DATA) && !w_read_complete;
    assign datard_addr = r_src_addr;
    assign datard_beats_remaining = r_read_beats_remaining;
    assign datard_channel_id = CHANNEL_ID[3:0];

    //=========================================================================
    // Data Write Interface Outputs
    //=========================================================================
    // Scheduler tells engine: "I need this many beats written to this address"
    // Engine decides: "I'll do X beats per burst based on my config/design"
    // Engine reports back: "I moved X beats" via datawr_done_strobe

    assign datawr_valid = (r_current_state == CH_WRITE_DATA) && !w_write_complete;
    assign datawr_addr = r_dst_addr;
    assign datawr_beats_remaining = r_write_beats_remaining;
    assign datawr_channel_id = CHANNEL_ID[3:0];

    //=========================================================================
    // Descriptor Engine Interface
    //=========================================================================

    assign descriptor_ready = (r_current_state == CH_IDLE) || (r_current_state == CH_NEXT_DESC);

    //=========================================================================
    // Timeout and Error Management
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_timeout_counter <= 32'h0;
            r_read_error_sticky <= 1'b0;
            r_write_error_sticky <= 1'b0;
        end else begin
            // Timeout counter
            if ((datard_valid && !datard_ready) || (datawr_valid && !datawr_ready)) begin
                r_timeout_counter <= r_timeout_counter + 1;
            end else begin
                r_timeout_counter <= 32'h0;
            end

            // Error tracking
            if (datard_error) r_read_error_sticky <= 1'b1;
            if (datawr_error) r_write_error_sticky <= 1'b1;

            // Clear errors on idle
            if (r_current_state == CH_IDLE) begin
                r_read_error_sticky <= 1'b0;
                r_write_error_sticky <= 1'b0;
            end
        end
    end

    assign w_timeout_expired = (r_timeout_counter >= TIMEOUT_CYCLES);

    //=========================================================================
    // Monitor Packet Generation
    //=========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            // Default: clear monitor packet
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;

            case (r_current_state)
                CH_FETCH_DESC: begin
                    // Log descriptor start
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeCompletion,
                        PROTOCOL_CORE,
                        STREAM_EVENT_DESC_START,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {3'h0, r_descriptor.length}  // Log transfer length
                    );
                end

                CH_READ_DATA: begin
                    if (w_read_complete) begin
                        // Log read phase complete
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_READ_COMPLETE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}
                        );
                    end
                end

                CH_WRITE_DATA: begin
                    if (w_write_complete) begin
                        // Log write phase complete
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_WRITE_COMPLETE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}
                        );
                    end
                end

                CH_COMPLETE: begin
                    // Log descriptor complete
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeCompletion,
                        PROTOCOL_CORE,
                        STREAM_EVENT_DESC_COMPLETE,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {3'h0, r_descriptor.length}
                    );
                end

                CH_ERROR: begin
                    // Log error
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeError,
                        PROTOCOL_CORE,
                        STREAM_EVENT_ERROR,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {r_write_error_sticky, r_read_error_sticky, 33'h0}
                    );
                end

                default: begin
                    // No monitor packet
                end
            endcase
        end
    end

    //=========================================================================
    // Status Outputs
    //=========================================================================

    assign scheduler_idle = (r_current_state == CH_IDLE) && !r_channel_reset_active;
    assign scheduler_state = r_current_state;

    // Monitor bus output
    assign mon_valid = r_mon_valid;
    assign mon_packet = r_mon_packet;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Descriptor valid check
    property descriptor_valid_check;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == CH_FETCH_DESC) |-> r_descriptor.valid;
    endproperty
    assert property (descriptor_valid_check);

    // Read before write ordering
    property read_before_write;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == CH_WRITE_DATA) |-> w_read_complete;
    endproperty
    assert property (read_before_write);

    // Aligned address requirement
    property address_aligned;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == CH_FETCH_DESC) |->
            (r_descriptor.src_addr[5:0] == 6'h0) &&
            (r_descriptor.dst_addr[5:0] == 6'h0);
    endproperty
    assert property (address_aligned);
    `endif

endmodule : scheduler
