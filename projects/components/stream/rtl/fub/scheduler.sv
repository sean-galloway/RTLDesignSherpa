// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler
// Purpose: STREAM Scheduler - Simple Memory-to-Memory DMA
//
// Description:
//   Coordinates descriptor-based memory-to-memory DMA transfers.
//   This is the STREAM version - simplified for tutorial purposes.
//
//   Transfer Flow:
//   1. Receives 256-bit descriptors from descriptor_engine
//   2. Reads data from source memory via AXI read engine
//   3. Writes data to destination memory via AXI write engine
//   4. Generates interrupt (if descriptor.gen_irq set)
//   5. Handles descriptor chaining (next_descriptor_ptr)
//   6. Monitors timeouts and errors
//
// STREAM Simplifications (vs RAPIDS):
//   ✓ Memory-to-memory only (no network, no producer/consumer)
//   ✓ No ctrl_rd/ctrl_wr fields (RAPIDS producer/consumer control)
//   ✓ No alignment fixup (addresses must be aligned)
//   ✓ Beat-based length (not chunks)
//   ✓ No credit management
//   ✓ IRQ event reporting via MonBus (descriptor.gen_irq flag)
//
// Key Features:
//   - Simple FSM: IDLE → FETCH_DESC → READ_DATA → WRITE_DATA → COMPLETE
//   - Beat-based tracking (length in data width units)
//   - Aligned addresses only (no fixup logic)
//   - MonBus event reporting at state transitions
//   - IRQ event generation via MonBus (STREAM_EVENT_IRQ)
//
// Interface Protocol:
//   - Scheduler tells engines "total beats remaining" (not burst length)
//   - Engines decide burst sizes autonomously
//   - Engines report back "beats completed" via done strobes
//   - Scheduler decrements counters until zero
//
// Documentation: projects/components/stream_fub/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"

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
    parameter logic [5:0] MON_CHANNEL_ID = 6'h0,     // Base channel ID
    // Descriptor Width (FIXED at 256-bit for STREAM)
    // NOTE: This scheduler is STREAM-only (simple memory-to-memory)
    //       For RAPIDS features (producer/consumer, ctrl_rd/ctrl_wr), use rapids_scheduler
    parameter int DESC_WIDTH = 256
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
    input  logic [DESC_WIDTH-1:0]       descriptor_packet,     // 256-bit STREAM descriptor
    input  logic                        descriptor_error,      // Error signal FROM descriptor engine

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

    // Parameter Validation - STREAM scheduler only supports 256-bit descriptors
    initial begin
        if (DESC_WIDTH != 256) begin
            $fatal(1, "scheduler (STREAM): DESC_WIDTH must be 256, got %0d. For RAPIDS, use rapids_scheduler.", DESC_WIDTH);
        end
    end

    // STREAM Descriptor Format (256-bit)
    // Layout matches stream_pkg.sv descriptor_t
    //
    //   [63:0]    - src_addr:            Source address (must be aligned to data width)
    //   [127:64]  - dst_addr:            Destination address (must be aligned to data width)
    //   [159:128] - length:              Transfer length in BEATS (not bytes!)
    //   [191:160] - next_descriptor_ptr: Address of next descriptor (0 = last)
    //   [192]     - valid:               Descriptor valid flag
    //   [193]     - gen_irq:             Generate interrupt on completion
    //   [194]     - last:                Last descriptor in chain flag
    //   [195]     - error:               Error flag
    //   [199:196] - channel_id:          Channel ID (informational, for MonBus/debug)
    //   [207:200] - desc_priority:       Transfer priority
    //   [255:208] - reserved:            Reserved for future use
    //
    localparam int DESC_SRC_ADDR_LO  = 0;
    localparam int DESC_SRC_ADDR_HI  = 63;
    localparam int DESC_DST_ADDR_LO  = 64;
    localparam int DESC_DST_ADDR_HI  = 127;
    localparam int DESC_LENGTH_LO    = 128;
    localparam int DESC_LENGTH_HI    = 159;
    localparam int DESC_NEXT_PTR_LO  = 160;
    localparam int DESC_NEXT_PTR_HI  = 191;
    localparam int DESC_VALID_BIT    = 192;
    localparam int DESC_GEN_IRQ      = 193;
    localparam int DESC_LAST         = 194;

    logic         w_pkt_error;                 // [195] Error flag
    logic         w_pkt_last;                  // [194] Last in chain
    logic         w_pkt_gen_irq;               // [193] Generate interrupt (renamed from 'interrupt' - C++ keyword)
    logic         w_pkt_valid;                 // [192] Valid descriptor
    logic [31:0]  w_pkt_next_descriptor_ptr;   // [191:160] Next descriptor address
    logic [31:0]  w_pkt_length;                // [159:128] Length in BEATS
    logic [63:0]  w_pkt_dst_addr;              // [127:64] Destination address
    logic [63:0]  w_pkt_src_addr;              // [63:0] Source address

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Scheduler FSM (using STREAM package enum)
    // States: CH_IDLE → CH_FETCH_DESC → CH_READ_DATA → CH_WRITE_DATA →
    //         CH_COMPLETE → CH_NEXT_DESC (if chained) or back to CH_IDLE
    channel_state_t r_current_state, w_next_state;

    // Channel reset management
    // Registered to cleanly handle cfg_channel_reset assertion
    logic r_channel_reset_active;

    // Descriptor fields
    // Latched from descriptor_packet in CH_IDLE state when descriptor_valid
    descriptor_t r_descriptor;
    logic r_descriptor_loaded;  // Flag indicating descriptor successfully loaded

    // Transfer tracking
    // Working copies of descriptor fields, updated as transfer progresses
    logic [ADDR_WIDTH-1:0] r_src_addr;            // Current source address
    logic [ADDR_WIDTH-1:0] r_dst_addr;            // Current destination address
    logic [31:0] r_beats_remaining;               // Total beats remaining (for reference)
    logic [31:0] r_read_beats_remaining;          // Beats left to read from source
    logic [31:0] r_write_beats_remaining;         // Beats left to write to destination

    // Timeout tracking
    // Counts clock cycles while waiting for engine grant (datard_ready/datawr_ready)
    // Prevents deadlock if engines don't respond
    logic [31:0] r_timeout_counter;
    logic w_timeout_expired;                      // Asserted when counter >= TIMEOUT_CYCLES

    // Interrupt generation
    // IRQ event is generated via MonBus when descriptor completes with gen_irq flag set

    // Error tracking
    // Sticky error flags - set on error, cleared on return to CH_IDLE
    logic r_read_error_sticky;                    // Read engine reported error
    logic r_write_error_sticky;                   // Write engine reported error
    logic r_descriptor_error;                     // Descriptor engine or internal error

    // Monitor packet generation
    // Registered outputs for MonBus interface
    logic r_mon_valid;
    logic [63:0] r_mon_packet;

    // Completion flags
    // Combinational checks for phase completion (beats_remaining == 0)
    logic w_read_complete;                        // All source data read
    logic w_write_complete;                       // All destination data written
    logic w_transfer_complete;                    // Both read and write complete

    //=========================================================================
    // Channel Reset Management
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_channel_reset_active <= 1'b0;
        end else begin
            r_channel_reset_active <= cfg_channel_reset;
        end
    )

    //=========================================================================
    // Scheduler FSM
    //=========================================================================

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_current_state <= CH_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    )

    // Next state logic
    // FSM Flow: IDLE → FETCH_DESC → READ_DATA → WRITE_DATA → COMPLETE → (chain?) → IDLE
    // Error transitions: Any error condition → CH_ERROR → (cleared?) → CH_IDLE
    always_comb begin
        w_next_state = r_current_state;  // Default: hold current state

        // Priority 1: Channel reset overrides all other transitions
        if (r_channel_reset_active) begin
            w_next_state = CH_IDLE;
        end else begin
            // Priority 2: Error handling - aggregate errors from all sources
            // Sources: descriptor_engine (descriptor_error)
            //          read_engine (datard_error)
            //          write_engine (datawr_error)
            //          scheduler internal (timeout, sticky errors)
            if (descriptor_error || datard_error || datawr_error ||
                r_read_error_sticky || r_write_error_sticky || w_timeout_expired) begin
                w_next_state = CH_ERROR;
            end else begin
                // Priority 3: Normal state machine transitions
                case (r_current_state)
                    CH_IDLE: begin
                        // Wait for:
                        // 1. descriptor_valid (descriptor engine has descriptor ready)
                        // 2. cfg_channel_enable (software has enabled this channel)
                        if (descriptor_valid && cfg_channel_enable) begin
                            w_next_state = CH_FETCH_DESC;
                        end
                    end

                    CH_FETCH_DESC: begin
                        // Descriptor latched from descriptor_packet in one cycle
                        // Validate descriptor.valid bit before proceeding
                        if (r_descriptor.valid) begin
                            w_next_state = CH_READ_DATA;  // Valid descriptor → start read phase
                        end else begin
                            w_next_state = CH_ERROR;      // Invalid descriptor → error
                        end
                    end

                    CH_READ_DATA: begin
                        // Read phase: Transfer data from source address to SRAM
                        // datard_valid asserted, engine reports progress via datard_done_strobe
                        // Transition when r_read_beats_remaining reaches 0
                        if (w_read_complete) begin
                            w_next_state = CH_WRITE_DATA;
                        end
                        // Note: Stays in READ_DATA until complete or error
                    end

                    CH_WRITE_DATA: begin
                        // Write phase: Transfer data from SRAM to destination address
                        // datawr_valid asserted, engine reports progress via datawr_done_strobe
                        // Transition when r_write_beats_remaining reaches 0
                        if (w_write_complete) begin
                            w_next_state = CH_COMPLETE;
                        end
                        // Note: Stays in WRITE_DATA until complete or error
                    end

                    CH_COMPLETE: begin
                        // Descriptor complete - check for chaining
                        // Chain if: next_descriptor_ptr != 0 AND last flag not set
                        if (r_descriptor.next_descriptor_ptr != 32'h0 && !r_descriptor.last) begin
                            w_next_state = CH_NEXT_DESC;  // Fetch next descriptor in chain
                        end else begin
                            w_next_state = CH_IDLE;       // Transfer complete, return to idle
                        end
                    end

                    CH_NEXT_DESC: begin
                        // Wait for descriptor engine to fetch next chained descriptor
                        // descriptor_engine uses r_descriptor.next_descriptor_ptr as fetch address
                        if (descriptor_valid) begin
                            w_next_state = CH_FETCH_DESC;  // Next descriptor ready
                        end
                        // Note: Stays in NEXT_DESC until descriptor_valid
                    end

                    CH_ERROR: begin
                        // Error state - wait for all error sources to clear
                        // Errors clear automatically on transition to CH_IDLE
                        if (!datard_error && !datawr_error &&
                            !r_read_error_sticky && !r_write_error_sticky) begin
                            w_next_state = CH_IDLE;
                        end
                        // Note: Timeout doesn't need explicit check (counter resets when not active)
                    end

                    default: begin
                        // Safety: undefined state → error
                        w_next_state = CH_ERROR;
                    end
                endcase
            end
        end
    end

    always_comb begin
        w_pkt_last = r_descriptor.last;
        w_pkt_gen_irq = r_descriptor.gen_irq;
        w_pkt_valid = r_descriptor.valid;
        w_pkt_next_descriptor_ptr = r_descriptor.next_descriptor_ptr;
        w_pkt_length = r_descriptor.length;
        w_pkt_dst_addr = r_descriptor.dst_addr;
        w_pkt_src_addr = r_descriptor.src_addr;
    end

    //=========================================================================
    // Descriptor Register Updates
    //=========================================================================
    // State-dependent register updates for descriptor fields and transfer tracking
    //
    // Key State Actions:
    //   CH_IDLE:      Latch incoming descriptor from descriptor_packet
    //   CH_FETCH_DESC: Initialize working registers from latched descriptor
    //   CH_READ_DATA:  Decrement read counter on datard_done_strobe
    //   CH_WRITE_DATA: Decrement write counter on datawr_done_strobe
    //   CH_COMPLETE:   Clear descriptor_loaded flag

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
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
                    // Descriptor capture: Sample descriptor_packet when both valid and ready
                    if (descriptor_valid && descriptor_ready) begin
                        // Extract fields from 256-bit STREAM descriptor
                        // - Addresses are pre-aligned (must match data width alignment)
                        // - Length is in BEATS (data width units)
                        // - No alignment metadata (STREAM simplification)
                        //
                        r_descriptor.src_addr <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
                        r_descriptor.dst_addr <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
                        r_descriptor.length <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
                        r_descriptor.next_descriptor_ptr <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
                        r_descriptor.valid <= descriptor_packet[DESC_VALID_BIT];
                        r_descriptor.gen_irq <= descriptor_packet[DESC_GEN_IRQ];
                        r_descriptor.last <= descriptor_packet[DESC_LAST];

                        r_descriptor_loaded <= 1'b1;
                    end
                end

                CH_FETCH_DESC: begin
                    // Transfer initialization: Copy descriptor fields to working registers
                    // These working registers will be updated as transfer progresses
                    r_src_addr <= r_descriptor.src_addr;
                    r_dst_addr <= r_descriptor.dst_addr;
                    r_beats_remaining <= r_descriptor.length;
                    r_read_beats_remaining <= r_descriptor.length;
                    r_write_beats_remaining <= r_descriptor.length;
                end

                CH_READ_DATA: begin
                    // Read progress tracking: Engine reports beats completed via strobe
                    // Engine may complete multiple beats per burst (burst length decided by engine)
                    if (datard_done_strobe) begin
                        // Decrement by number of beats engine completed
                        // Saturate at 0 (safety check, shouldn't underflow)
                        r_read_beats_remaining <= (r_read_beats_remaining >= datard_beats_done) ?
                                                (r_read_beats_remaining - datard_beats_done) : 32'h0;
                    end
                end

                CH_WRITE_DATA: begin
                    // Write progress tracking: Engine reports beats completed via strobe
                    // Engine may complete multiple beats per burst (burst length decided by engine)
                    if (datawr_done_strobe) begin
                        // Decrement by number of beats engine completed
                        // Saturate at 0 (safety check, shouldn't underflow)
                        r_write_beats_remaining <= (r_write_beats_remaining >= datawr_beats_done) ?
                                                (r_write_beats_remaining - datawr_beats_done) : 32'h0;
                    end
                end

                CH_COMPLETE: begin
                    // Transfer complete: Clear descriptor_loaded flag
                    // Ready to accept next descriptor (or chain to next)
                    r_descriptor_loaded <= 1'b0;
                end

                default: begin
                    // Other states: Maintain register values
                end
            endcase

            // Channel reset: Clear state regardless of FSM state
            if (r_channel_reset_active) begin
                r_descriptor_loaded <= 1'b0;
                r_read_beats_remaining <= 32'h0;
                r_write_beats_remaining <= 32'h0;
            end
        end
    )

    //=========================================================================
    // Interrupt Generation via MonBus
    //=========================================================================
    // IRQ events are generated in CH_COMPLETE state when r_descriptor.gen_irq is set
    // No separate IRQ flag needed - check descriptor directly in MonBus generation logic

    //=========================================================================
    // Completion Logic
    //=========================================================================

    assign w_read_complete = (r_read_beats_remaining == 32'h0);
    assign w_write_complete = (r_write_beats_remaining == 32'h0);
    assign w_transfer_complete = w_read_complete && w_write_complete;

    // Look-ahead completion detection:
    // De-assert valid on the SAME CYCLE that the completion strobe arrives
    // to prevent read/write engines from issuing extra transactions due to
    // the pipeline delay between strobe arrival and beats_remaining update.
    //
    // Without this, sequence is:
    //   Cycle N:   Engine completes last beat
    //   Cycle N+1: done_strobe asserted, BUT datard_valid still HIGH
    //   Cycle N+1: Engine sees valid+space+no_outstanding → issues SECOND transaction!
    //   Cycle N+2: Scheduler updates beats_remaining to 0
    //   Cycle N+3: Scheduler de-asserts datard_valid (too late!)
    //
    // With this fix:
    //   Cycle N+1: done_strobe asserted, datard_valid de-asserted immediately
    //   Cycle N+1: Engine sees !datard_valid → does NOT issue second transaction
    logic w_datard_completing_this_cycle;
    logic w_datawr_completing_this_cycle;

    assign w_datard_completing_this_cycle = datard_done_strobe &&
                                        (r_read_beats_remaining <= datard_beats_done);
    assign w_datawr_completing_this_cycle = datawr_done_strobe &&
                                        (r_write_beats_remaining <= datawr_beats_done);

    //=========================================================================
    // Data Read Interface Outputs
    //=========================================================================
    // Scheduler tells engine: "I need this many beats from this address"
    // Engine decides: "I'll do X beats per burst based on my config/design"
    // Engine reports back: "I moved X beats" via datard_done_strobe

    assign datard_valid = (r_current_state == CH_READ_DATA) &&
                        !w_read_complete &&
                        !w_datard_completing_this_cycle;
    assign datard_addr = r_src_addr;
    assign datard_beats_remaining = r_read_beats_remaining;
    assign datard_channel_id = CHANNEL_ID[3:0];

    //=========================================================================
    // Data Write Interface Outputs
    //=========================================================================
    // Scheduler tells engine: "I need this many beats written to this address"
    // Engine decides: "I'll do X beats per burst based on my config/design"
    // Engine reports back: "I moved X beats" via datawr_done_strobe

    assign datawr_valid = (r_current_state == CH_WRITE_DATA) &&
                        !w_write_complete &&
                        !w_datawr_completing_this_cycle;
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
    // Timeout: Prevents deadlock if AXI engines don't respond with ready/grant
    // Errors: Sticky flags capture transient errors for graceful FSM transition
    //
    // Error Sources:
    //   1. descriptor_error  - Descriptor engine fetch error (AXI R error, invalid descriptor)
    //   2. datard_error      - Read engine error (AXI R error, SRAM full)
    //   3. datawr_error      - Write engine error (AXI B error, SRAM empty)
    //   4. w_timeout_expired - Scheduler timeout (engines not granting access)
    //
    // Error Handling Flow:
    //   Error detected → sticky flag set → FSM transition to CH_ERROR
    //   CH_ERROR state → wait for external errors to clear → FSM to CH_IDLE
    //   CH_IDLE entry → clear all sticky flags

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_timeout_counter <= 32'h0;
            r_read_error_sticky <= 1'b0;
            r_write_error_sticky <= 1'b0;
            r_descriptor_error <= 1'b0;
        end else begin
            // Timeout counter: Increments while waiting for engine grant
            // Counts cycles where datard_valid or datawr_valid is high but ready is low
            // Prevents deadlock if arbiter/engine doesn't respond
            if ((datard_valid && !datard_ready) || (datawr_valid && !datawr_ready)) begin
                r_timeout_counter <= r_timeout_counter + 1;
            end else begin
                r_timeout_counter <= 32'h0;  // Reset when not waiting or grant received
            end

            // Error capture: Latch errors from external components
            // Sticky flags ensure errors aren't lost due to transient de-assertion
            if (descriptor_error) r_descriptor_error <= 1'b1;   // Descriptor engine error
            if (datard_error) r_read_error_sticky <= 1'b1;       // Read engine error
            if (datawr_error) r_write_error_sticky <= 1'b1;      // Write engine error

            // Also set descriptor_error flag for ANY scheduler-internal error
            // This ensures consistent error reporting via MonBus
            if (datard_error || datawr_error || w_timeout_expired) begin
                r_descriptor_error <= 1'b1;
            end

            // Error clearing: All sticky flags clear on transition to CH_IDLE
            // This prepares scheduler for next descriptor
            if (r_current_state == CH_IDLE) begin
                r_read_error_sticky <= 1'b0;
                r_write_error_sticky <= 1'b0;
                r_descriptor_error <= 1'b0;
            end
        end
    )


    // Timeout threshold: Compare counter to parameterized limit
    assign w_timeout_expired = (r_timeout_counter >= TIMEOUT_CYCLES);

    //=========================================================================
    // Monitor Packet Generation
    //=========================================================================
    // Generates 64-bit MonBus packets at key FSM state transitions
    //
    // MonBus Packet Format (from monitor_pkg.sv):
    //   [63:56] - agent_id:    STREAM Scheduler Agent ID (0x40)
    //   [55:52] - unit_id:     Unit identifier (0x1)
    //   [51:46] - channel_id:  Channel number (0-7)
    //   [45:42] - event_code:  STREAM-specific event code
    //   [41:40] - protocol:    PROTOCOL_CORE (0x0)
    //   [39:38] - pkt_type:    PktTypeCompletion (0x0) or PktTypeError (0x3)
    //   [37:0]  - payload:     Event-specific data
    //
    // STREAM Event Codes (from stream_pkg.sv):
    //   DESC_START:       Descriptor processing started
    //   READ_COMPLETE:    Read phase complete (all data in SRAM)
    //   WRITE_COMPLETE:   Write phase complete (all data written)
    //   DESC_COMPLETE:    Descriptor complete (ready for next/idle)
    //   ERROR:            Error detected (payload = error flags)
    //
    // Packet Generation Strategy:
    //   - Generate on state entry (registered in state)
    //   - One packet per state transition
    //   - Clear valid after one cycle (downstream must sample)

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;
        end else begin
            // Default: Clear monitor packet (single-cycle pulse)
            r_mon_valid <= 1'b0;
            r_mon_packet <= 64'h0;

            case (r_current_state)
                CH_FETCH_DESC: begin
                    // Event: Descriptor processing started
                    // Payload: Transfer length in beats
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeCompletion,
                        PROTOCOL_CORE,
                        STREAM_EVENT_DESC_START,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {3'h0, r_descriptor.length}  // Payload: 32-bit length
                    );
                end

                CH_READ_DATA: begin
                    // Event: Read phase complete (generate only when complete)
                    // Payload: Total beats transferred
                    if (w_read_complete) begin
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_READ_COMPLETE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}  // Payload: 32-bit length
                        );
                    end
                end

                CH_WRITE_DATA: begin
                    // Event: Write phase complete (generate only when complete)
                    // Payload: Total beats transferred
                    if (w_write_complete) begin
                        r_mon_valid <= 1'b1;
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_WRITE_COMPLETE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}  // Payload: 32-bit length
                        );
                    end
                end

                CH_COMPLETE: begin
                    // Event: Descriptor complete (ready for next descriptor or idle)
                    // Generate IRQ event if gen_irq flag set, otherwise completion event
                    r_mon_valid <= 1'b1;
                    if (r_descriptor.gen_irq) begin
                        // IRQ event: Descriptor completed with interrupt request
                        // Payload: Descriptor length (for context)
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_IRQ,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}  // Payload: 32-bit length
                        );
                    end else begin
                        // Normal completion event (no IRQ)
                        // Payload: Total beats transferred
                        r_mon_packet <= create_monitor_packet(
                            PktTypeCompletion,
                            PROTOCOL_CORE,
                            STREAM_EVENT_DESC_COMPLETE,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {3'h0, r_descriptor.length}  // Payload: 32-bit length
                        );
                    end
                end

                CH_ERROR: begin
                    // Event: Error detected (any source)
                    // Payload: Error flags [35] = write_error, [34] = read_error
                    r_mon_valid <= 1'b1;
                    r_mon_packet <= create_monitor_packet(
                        PktTypeError,
                        PROTOCOL_CORE,
                        STREAM_EVENT_ERROR,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {r_write_error_sticky, r_read_error_sticky, 33'h0}  // Error flags
                    );
                end

                default: begin
                    // No monitor packet for other states
                end
            endcase
        end
    )


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
