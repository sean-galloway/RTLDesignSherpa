//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: scheduler
        // Purpose: RAPIDS Scheduler - Network-to-Memory DMA (Phase 1)
        //
        // Description:
        //   Coordinates descriptor-based network-to-memory transfers.
        //   This is the RAPIDS Phase 1 version - simplified concurrent architecture.
        //
        //   Transfer Flow:
        //   1. Receives 256-bit descriptors from descriptor_engine
        //   2. CONCURRENTLY reads data from source AND writes to destination
        //      - Read engine: source memory → SRAM buffer
        //      - Write engine: SRAM buffer → destination memory
        //      - Both engines run simultaneously with natural backpressure
        //   3. Generates interrupt (if descriptor.gen_irq set)
        //   4. Handles descriptor chaining (next_descriptor_ptr)
        //   5. Monitors timeouts and errors
        //
        // CRITICAL DESIGN FEATURE - Concurrent Read/Write:
        //   The scheduler runs read and write engines CONCURRENTLY in CH_XFER_DATA state.
        //   This prevents deadlock when transfer size > SRAM buffer size:
        //     - Read fills SRAM → SRAM full → read pauses
        //     - Write drains SRAM → SRAM has space → read resumes
        //   Without concurrency, 100MB transfer with 2KB SRAM would deadlock!
        //
        // RAPIDS Phase 1 Simplifications:
        //   ✓ Network-to-memory via AXIS interfaces
        //   ✓ No ctrl_rd/ctrl_wr fields (Phase 2 feature)
        //   ✓ No alignment fixup (addresses must be aligned)
        //   ✓ Beat-based length (not chunks)
        //   ✓ No credit management (Phase 2 feature)
        //   ✓ IRQ event reporting via MonBus (descriptor.gen_irq flag)
        //
        // Key Features:
        //   - Simple FSM: IDLE → FETCH_DESC → XFER_DATA → COMPLETE
        //   - Concurrent read/write in XFER_DATA (prevents deadlock)
        //   - Beat-based tracking (length in data width units)
        //   - Aligned addresses only (no fixup logic)
        //   - MonBus event reporting at state transitions
        //   - IRQ event generation via MonBus (RAPIDS_EVENT_IRQ)
        //
        // Interface Protocol:
        //   - Scheduler tells engines "total beats remaining" (not burst length)
        //   - Engines decide burst sizes autonomously
        //   - Engines report back "beats completed" via done strobes
        //   - Scheduler decrements counters until zero (independently for read/write)
        //
        // Documentation: projects/components/rapids/PRD.md
        // Subsystem: rapids_fub
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        // Import common RAPIDS and monitor packages
        `include "rapids_imports.svh"
        `include "reset_defs.svh"
        
        module scheduler_beats #(
            parameter int CHANNEL_ID = 0,
            parameter int NUM_CHANNELS = 8,
            parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
            parameter int ADDR_WIDTH = 64,
            parameter int DATA_WIDTH = 512,
            // Monitor Bus Parameters
            parameter logic [7:0] MON_AGENT_ID = 8'h40,      // RAPIDS Scheduler Agent ID
            parameter logic [3:0] MON_UNIT_ID = 4'h1,        // Unit identifier
            parameter logic [5:0] MON_CHANNEL_ID = 6'h0,     // Base channel ID
            // Descriptor Width (FIXED at 256-bit for RAPIDS Phase 1)
            // NOTE: This scheduler is RAPIDS Phase 1 (simplified network-to-memory)
            //       Phase 2 will add credit management and control engines
            parameter int DESC_WIDTH = 256
        ) (
            // Clock and Reset
 013082     input  logic                        clk,
 000012     input  logic                        rst_n,
        
            // Configuration Interface
 000012     input  logic                        cfg_channel_enable,     // Enable this channel
%000002     input  logic                        cfg_channel_reset,      // Channel reset
%000000     input  logic [15:0]                 cfg_sched_timeout_cycles, // Timeout threshold (cycles)
 000012     input  logic                        cfg_sched_timeout_enable, // Enable timeout detection
        
            // Status Interface
 000072     output logic                        scheduler_idle,         // Scheduler idle
%000000     output logic [6:0]                  scheduler_state,        // Current state (for debug) - ONE-HOT
        
            // Descriptor Engine Interface
 000064     input  logic                        descriptor_valid,
 000076     output logic                        descriptor_ready,
%000000     input  logic [DESC_WIDTH-1:0]       descriptor_packet,     // 256-bit RAPIDS descriptor
%000002     input  logic                        descriptor_error,      // Error signal FROM descriptor engine
        
            // Data Read Interface (to AXI Read Engine)
            // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
 000092     output logic                        sched_rd_valid,         // Channel requests read
%000000     output logic [ADDR_WIDTH-1:0]       sched_rd_addr,          // Source address (aligned)
%000000     output logic [31:0]                 sched_rd_beats,         // Beats remaining to read
        
            // Data Write Interface (to AXI Write Engine)
            // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
 000098     output logic                        sched_wr_valid,         // Channel requests write
 000013     input  logic                        sched_wr_ready,         // Engine ready for channel (used for completion)
%000000     output logic [ADDR_WIDTH-1:0]       sched_wr_addr,          // Destination address (aligned)
%000000     output logic [31:0]                 sched_wr_beats,         // Beats remaining to write
        
            // Completion Interface (from Engines to Scheduler)
 000248     input  logic                        sched_rd_done_strobe,   // Read burst completed (pulsed)
%000000     input  logic [31:0]                 sched_rd_beats_done,    // Number of beats completed
 000232     input  logic                        sched_wr_done_strobe,   // Write burst completed (pulsed)
%000000     input  logic [31:0]                 sched_wr_beats_done,    // Number of beats completed
        
            // Error Signals (from Engines to Scheduler)
%000002     input  logic                        sched_rd_error,         // Read engine error
%000002     input  logic                        sched_wr_error,         // Write engine error
%000004     output logic                        sched_error,            // Scheduler error output (sticky)
        
            // Monitor Bus Interface
 000126     output logic                        mon_valid,
 000012     input  logic                        mon_ready,
%000000     output logic [63:0]                 mon_packet
        );
        
            //=========================================================================
            // Local Parameters
            //=========================================================================
        
            // Parameter Validation - RAPIDS Phase 1 scheduler only supports 256-bit descriptors
 000012     initial begin
 000012         if (DESC_WIDTH != 256) begin
                    $fatal(1, "scheduler (RAPIDS): DESC_WIDTH must be 256, got %0d.", DESC_WIDTH);
                end
            end
        
            // RAPIDS Descriptor Format (256-bit)
            // Layout matches rapids_pkg.sv descriptor_t
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
        
%000000     logic         w_pkt_error;                 // [195] Error flag
 000012     logic         w_pkt_last;                  // [194] Last in chain
%000001     logic         w_pkt_gen_irq;               // [193] Generate interrupt (renamed from 'interrupt' - C++ keyword)
 000012     logic         w_pkt_valid;                 // [192] Valid descriptor
%000000     logic [31:0]  w_pkt_next_descriptor_ptr;   // [191:160] Next descriptor address
%000000     logic [31:0]  w_pkt_length;                // [159:128] Length in BEATS
%000000     logic [63:0]  w_pkt_dst_addr;              // [127:64] Destination address
%000000     logic [63:0]  w_pkt_src_addr;              // [63:0] Source address
        
            //=========================================================================
            // Internal Signals
            //=========================================================================
        
            // Scheduler FSM (using RAPIDS package enum - ONE-HOT ENCODED)
            // States: CH_IDLE → CH_FETCH_DESC → CH_XFER_DATA →
            //         CH_COMPLETE → CH_NEXT_DESC (if chained) or back to CH_IDLE
            //
            // CRITICAL: CH_XFER_DATA runs read and write engines CONCURRENTLY
            //           to prevent deadlock when SRAM buffer < transfer size
%000000     channel_state_t r_current_state, w_next_state;
        
            // State decode wires (for debug/monitoring)
 000072     wire w_state_idle        = (r_current_state == CH_IDLE);
 000062     wire w_state_fetch_desc  = (r_current_state == CH_FETCH_DESC);
 000062     wire w_state_xfer_data   = (r_current_state == CH_XFER_DATA);
 000060     wire w_state_complete    = (r_current_state == CH_COMPLETE);
%000004     wire w_state_next_desc   = (r_current_state == CH_NEXT_DESC);
%000004     wire w_state_error       = (r_current_state == CH_ERROR);
        
            // Channel reset management
            // Registered to cleanly handle cfg_channel_reset assertion
%000002     logic r_channel_reset_active;
        
            // Descriptor fields
            // Latched from descriptor_packet in CH_IDLE state when descriptor_valid
            descriptor_t r_descriptor;
 000062     logic r_descriptor_loaded;  // Flag indicating descriptor successfully loaded
        
            // Transfer tracking
            // Working copies of descriptor fields, updated as transfer progresses
%000000     logic [ADDR_WIDTH-1:0] r_src_addr;            // Current source address
%000000     logic [ADDR_WIDTH-1:0] r_dst_addr;            // Current destination address
%000000     logic [31:0] r_beats_remaining;               // Total beats remaining (for reference)
%000000     logic [31:0] r_read_beats_remaining;          // Beats left to read from source
%000000     logic [31:0] r_write_beats_remaining;         // Beats left to write to destination
        
            // Timeout tracking
            // Counts clock cycles while waiting for engine grant (sched_wr_ready)
            // Prevents deadlock if engines don't respond
%000000     logic [31:0] r_timeout_counter;
%000002     logic w_timeout_expired;                      // Asserted when counter >= cfg_sched_timeout_cycles
        
            // Interrupt generation
            // IRQ event is generated via MonBus when descriptor completes with gen_irq flag set
        
            // Error tracking
            // Sticky error flags - set on error, cleared on return to CH_IDLE
%000001     logic r_read_error_sticky;                    // Read engine reported error
%000001     logic r_write_error_sticky;                   // Write engine reported error
%000004     logic r_descriptor_error;                     // Descriptor engine or internal error
        
            // Monitor packet generation
            // Registered outputs for MonBus interface
 000126     logic r_mon_valid;
%000000     logic [63:0] r_mon_packet;
        
            // Completion flags
            // Combinational checks for phase completion (beats_remaining == 0)
 000073     logic w_read_complete;                        // All source data read
 000073     logic w_write_complete;                       // All destination data written
 000073     logic w_transfer_complete;                    // Both read and write complete
        
            //=========================================================================
            // Channel Reset Management
            //=========================================================================
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_channel_reset_active <= 1'b0;
                end else begin
                    r_channel_reset_active <= cfg_channel_reset;
                end
 000131     )
        
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
 000131     )
        
            // Next state logic
            // FSM Flow: IDLE → FETCH_DESC → XFER_DATA → COMPLETE → (chain?) → IDLE
            // Error transitions: Any error condition → CH_ERROR → (cleared?) → CH_IDLE
            //
            // CRITICAL CHANGE: CH_XFER_DATA replaces separate CH_READ_DATA and CH_WRITE_DATA states
            //                  Both read and write engines run CONCURRENTLY to prevent deadlock
            //                  when SRAM buffer size < total transfer size
 039787     always_comb begin
 039787         w_next_state = r_current_state;  // Default: hold current state
        
                // Priority 1: Channel reset overrides all other transitions
 000061         if (r_channel_reset_active) begin
 000061             w_next_state = CH_IDLE;
 039726         end else begin
                    // Priority 2: Error handling - aggregate errors from all sources
                    // Sources: descriptor_engine (descriptor_error)
                    //          read_engine (sched_rd_error)
                    //          write_engine (sched_wr_error)
                    //          scheduler internal (timeout, sticky errors)
 003319             if (descriptor_error || sched_rd_error || sched_wr_error ||
 003319                 r_read_error_sticky || r_write_error_sticky || w_timeout_expired) begin
 003319                 w_next_state = CH_ERROR;
 036407             end else begin
                        // Priority 3: Normal state machine transitions
 036407                 case (r_current_state)
 017440                     CH_IDLE: begin
                                // Wait for:
                                // 1. descriptor_valid (descriptor engine has descriptor ready)
                                // 2. cfg_channel_enable (software has enabled this channel)
 000201                         if (descriptor_valid && cfg_channel_enable) begin
 000201                             w_next_state = CH_FETCH_DESC;
                                end
                            end
        
 000185                     CH_FETCH_DESC: begin
                                // Descriptor latched from descriptor_packet in one cycle
                                // Validate descriptor.valid bit before proceeding
%000000                         if (r_descriptor.valid) begin
 000185                             w_next_state = CH_XFER_DATA;  // Valid descriptor → start concurrent transfer
%000000                         end else begin
%000000                             w_next_state = CH_ERROR;      // Invalid descriptor → error
                                end
                            end
        
 012426                     CH_XFER_DATA: begin
                                // Transfer phase: Read and write engines run CONCURRENTLY
                                // - Read engine: Transfers source → SRAM
                                // - Write engine: Transfers SRAM → destination
                                // - Both report progress via done strobes
                                // - Natural backpressure via SRAM full/empty flags
                                //
                                // Exit when:
                                // 1. Transfer complete (both counters == 0)
                                // 2. Write engine signals ready (all transactions acknowledged)
 000210                         if (w_transfer_complete && sched_wr_ready) begin
 000210                             w_next_state = CH_COMPLETE;
                                end
                                // Note: Stays in XFER_DATA until both conditions met or error
                            end
        
 000180                     CH_COMPLETE: begin
                                // Descriptor complete - check for chaining
                                // Chain if: next_descriptor_ptr != 0 AND last flag not set
 000012                         if (r_descriptor.next_descriptor_ptr != 32'h0 && !r_descriptor.last) begin
 000012                             w_next_state = CH_NEXT_DESC;  // Fetch next descriptor in chain
 000168                         end else begin
 000168                             w_next_state = CH_IDLE;       // Transfer complete, return to idle
                                end
                            end
        
 006016                     CH_NEXT_DESC: begin
                                // Wait for descriptor engine to fetch next chained descriptor
                                // descriptor_engine uses r_descriptor.next_descriptor_ptr as fetch address
 000014                         if (descriptor_valid) begin
 000014                             w_next_state = CH_FETCH_DESC;  // Next descriptor ready
                                end
                                // Note: Stays in NEXT_DESC until descriptor_valid
                            end
        
 000124                     CH_ERROR: begin
                                // Error state - STICKY, stay here until reset
                                // Once in error, only way out is through reset
 000124                         w_next_state = CH_ERROR;
                            end
        
 000036                     default: begin
                                // Safety: undefined state → error
 000036                         w_next_state = CH_ERROR;
                            end
                        endcase
                    end
                end
            end
        
 000012     always_comb begin
 000012         w_pkt_last = r_descriptor.last;
 000012         w_pkt_gen_irq = r_descriptor.gen_irq;
 000012         w_pkt_valid = r_descriptor.valid;
 000012         w_pkt_next_descriptor_ptr = r_descriptor.next_descriptor_ptr;
 000012         w_pkt_length = r_descriptor.length;
 000012         w_pkt_dst_addr = r_descriptor.dst_addr;
 000012         w_pkt_src_addr = r_descriptor.src_addr;
            end
        
            //=========================================================================
            // Descriptor Register Updates
            //=========================================================================
            // State-dependent register updates for descriptor fields and transfer tracking
            //
            // Key State Actions:
            //   CH_IDLE/CH_NEXT_DESC: Sample descriptor_packet when descriptor_valid
            //   CH_FETCH_DESC: Initialize working registers from latched descriptor
            //   CH_XFER_DATA:  Decrement BOTH read and write counters independently (concurrent!)
            //   CH_COMPLETE:   Clear descriptor_loaded flag
            //
            // CRITICAL: Descriptor packet sampling happens when descriptor_valid && descriptor_ready
            //           (in CH_IDLE or CH_NEXT_DESC states). This ensures fresh descriptor data
            //           is captured for both the first descriptor and all chained descriptors.
            //
            // CRITICAL: In CH_XFER_DATA, both counters update independently based on their
            //           respective done strobes. This allows concurrent read/write operation.
        
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
                    // Descriptor capture: Sample descriptor_packet when handshake occurs
                    // This happens in either CH_IDLE (first descriptor) or CH_NEXT_DESC (chained)
                    if ((r_current_state == CH_IDLE || r_current_state == CH_NEXT_DESC) &&
                        descriptor_valid && descriptor_ready) begin
                        // Extract fields from 256-bit RAPIDS descriptor
                        // - Addresses are pre-aligned (must match data width alignment)
                        // - Length is in BEATS (data width units)
                        // - No alignment metadata (RAPIDS Phase 1 simplification)
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
        
                    case (r_current_state)
                        CH_FETCH_DESC: begin
                            // Transfer initialization: Copy descriptor fields to working registers
                            // These working registers will be updated as transfer progresses
                            r_src_addr <= r_descriptor.src_addr;
                            r_dst_addr <= r_descriptor.dst_addr;
                            r_beats_remaining <= r_descriptor.length;
                            r_read_beats_remaining <= r_descriptor.length;
                            r_write_beats_remaining <= r_descriptor.length;
                        end
        
                        CH_XFER_DATA: begin
                            // Concurrent transfer progress tracking:
                            // - Read engine and write engine operate INDEPENDENTLY
                            // - Each decrements its own counter when reporting completion
                            // - Both strobes can be active simultaneously
                            // - Natural backpressure via SRAM full (read) and empty (write)
                            //
                            // Read progress: Source → SRAM
                            if (sched_rd_done_strobe) begin
                                // Decrement by number of beats engine completed
                                // Saturate at 0 (safety check, shouldn't underflow)
                                r_read_beats_remaining <= (r_read_beats_remaining >= sched_rd_beats_done) ?
                                                        (r_read_beats_remaining - sched_rd_beats_done) : 32'h0;
        
                                // Increment source address by bytes transferred
                                // Address increment = beats_done << AXSIZE (where AXSIZE = log2(DATA_WIDTH/8))
                                r_src_addr <= r_src_addr + (ADDR_WIDTH'(sched_rd_beats_done) << $clog2(DATA_WIDTH/8));
                            end
        
                            // Write progress: SRAM → Destination (independent from read!)
                            if (sched_wr_done_strobe) begin
                                // Decrement by number of beats engine completed
                                // Saturate at 0 (safety check, shouldn't underflow)
                                r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done) ?
                                                        (r_write_beats_remaining - sched_wr_beats_done) : 32'h0;
        
                                // Increment destination address by bytes transferred
                                // Address increment = beats_done << AXSIZE (where AXSIZE = log2(DATA_WIDTH/8))
                                r_dst_addr <= r_dst_addr + (ADDR_WIDTH'(sched_wr_beats_done) << $clog2(DATA_WIDTH/8));
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
 000010     )
        
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
            //   Cycle N+1: done_strobe asserted, BUT sched_rd_valid still HIGH
            //   Cycle N+1: Engine sees valid+space+no_outstanding → issues SECOND transaction!
            //   Cycle N+2: Scheduler updates beats_remaining to 0
            //   Cycle N+3: Scheduler de-asserts sched_rd_valid (too late!)
            //
            // With this fix:
            //   Cycle N+1: done_strobe asserted, sched_rd_valid de-asserted immediately
            //   Cycle N+1: Engine sees !sched_rd_valid → does NOT issue second transaction
 000090     logic w_sched_rd_completing_this_cycle;
 000096     logic w_sched_wr_completing_this_cycle;
        
            assign w_sched_rd_completing_this_cycle = sched_rd_done_strobe &&
                                                (r_read_beats_remaining <= sched_rd_beats_done);
            assign w_sched_wr_completing_this_cycle = sched_wr_done_strobe &&
                                                (r_write_beats_remaining <= sched_wr_beats_done);
        
            //=========================================================================
            // Data Read Interface Outputs
            //=========================================================================
            // Scheduler tells engine: "I need this many beats from this address"
            // Engine decides: "I'll do X beats per burst based on my config/design"
            // Engine reports back: "I moved X beats" via sched_rd_done_strobe
            //
            // CONCURRENT OPERATION: sched_rd_valid asserted in CH_XFER_DATA (not CH_READ_DATA)
            //                       Runs simultaneously with write engine
        
            assign sched_rd_valid = (r_current_state == CH_XFER_DATA) &&
                                !w_read_complete &&
                                !w_sched_rd_completing_this_cycle;
            assign sched_rd_addr = r_src_addr;
            assign sched_rd_beats = r_read_beats_remaining;
        
            //=========================================================================
            // Data Write Interface Outputs
            //=========================================================================
            // Scheduler tells engine: "I need this many beats written to this address"
            // Engine decides: "I'll do X beats per burst based on my config/design"
            // Engine reports back: "I moved X beats" via sched_wr_done_strobe
            //
            // CONCURRENT OPERATION: sched_wr_valid asserted in CH_XFER_DATA (not CH_WRITE_DATA)
            //                       Runs simultaneously with read engine
        
            assign sched_wr_valid = (r_current_state == CH_XFER_DATA) &&
                                !w_write_complete &&
                                !w_sched_wr_completing_this_cycle;
            assign sched_wr_addr = r_dst_addr;
            assign sched_wr_beats = r_write_beats_remaining;
        
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
            //   2. sched_rd_error    - Read engine error (AXI R error, SRAM full)
            //   3. sched_wr_error    - Write engine error (AXI B error, SRAM empty)
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
                    // Timeout counter: Increments while waiting for write engine completion
                    // Counts cycles where sched_wr_valid is high but ready is low
                    // Prevents deadlock if write engine doesn't complete
                    if (sched_wr_valid && !sched_wr_ready) begin
                        r_timeout_counter <= r_timeout_counter + 1;
                    end else begin
                        r_timeout_counter <= 32'h0;  // Reset when not waiting or completion received
                    end
        
                    // Error capture: Latch errors from external components
                    // Sticky flags ensure errors aren't lost due to transient de-assertion
                    if (descriptor_error) r_descriptor_error <= 1'b1;   // Descriptor engine error
                    if (sched_rd_error) r_read_error_sticky <= 1'b1;    // Read engine error
                    if (sched_wr_error) r_write_error_sticky <= 1'b1;   // Write engine error
        
                    // Also set descriptor_error flag for ANY scheduler-internal error
                    // This ensures consistent error reporting via MonBus
                    if (sched_rd_error || sched_wr_error || w_timeout_expired) begin
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
%000005     )
        
        
            // Timeout threshold: Compare counter to configured limit (if enabled)
            assign w_timeout_expired = cfg_sched_timeout_enable &&
                                       (r_timeout_counter >= {16'h0, cfg_sched_timeout_cycles});
        
            //=========================================================================
            // Monitor Packet Generation
            //=========================================================================
            // Generates 64-bit MonBus packets at key FSM state transitions
            //
            // MonBus Packet Format (from monitor_pkg.sv):
            //   [63:56] - agent_id:    RAPIDS Scheduler Agent ID (0x40)
            //   [55:52] - unit_id:     Unit identifier (0x1)
            //   [51:46] - channel_id:  Channel number (0-7)
            //   [45:42] - event_code:  RAPIDS-specific event code
            //   [41:40] - protocol:    PROTOCOL_CORE (0x0)
            //   [39:38] - pkt_type:    PktTypeCompletion (0x0) or PktTypeError (0x3)
            //   [37:0]  - payload:     Event-specific data
            //
            // RAPIDS Event Codes (from rapids_pkg.sv):
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
                                RAPIDS_EVENT_DESC_START,
                                MON_CHANNEL_ID,
                                MON_UNIT_ID,
                                MON_AGENT_ID,
                                {3'h0, r_descriptor.length}  // Payload: 32-bit length
                            );
                        end
        
                        CH_XFER_DATA: begin
                            // No intermediate events during concurrent transfer
                            // Read and write happen simultaneously, only final completion matters
                            // This keeps MonBus traffic low and focuses on meaningful events
                        end
        
                        CH_COMPLETE: begin
                            // Event: Descriptor complete (ready for next descriptor or idle)
                            // Generate IRQ event if gen_irq flag set, otherwise completion event
                            //
                            // Note: With concurrent transfer, we only generate completion event
                            //       when BOTH read and write are done (cleaner semantics)
                            r_mon_valid <= 1'b1;
                            if (r_descriptor.gen_irq) begin
                                // IRQ event: Descriptor completed with interrupt request
                                // Payload: Descriptor length (for context)
                                r_mon_packet <= create_monitor_packet(
                                    PktTypeCompletion,
                                    PROTOCOL_CORE,
                                    RAPIDS_EVENT_IRQ,
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
                                    RAPIDS_EVENT_DESC_COMPLETE,
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
                                RAPIDS_EVENT_ERROR,
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
%000001     )
        
            //=========================================================================
            // Status Outputs
            //=========================================================================
        
            assign scheduler_idle = ((r_current_state == CH_IDLE) || (r_current_state == CH_ERROR))
                                        && !r_channel_reset_active;
            assign scheduler_state = r_current_state;
            assign sched_error = w_state_error;  // Sticky error output
        
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
        
            // Concurrent transfer completion: Exit CH_XFER_DATA only when BOTH complete
            property concurrent_transfer_complete;
                @(posedge clk) disable iff (!rst_n)
                (r_current_state == CH_XFER_DATA && w_next_state == CH_COMPLETE) |->
                    (w_read_complete && w_write_complete);
            endproperty
            assert property (concurrent_transfer_complete);
        
            // Aligned address requirement
            property address_aligned;
                @(posedge clk) disable iff (!rst_n)
                (r_current_state == CH_FETCH_DESC) |->
                    (r_descriptor.src_addr[5:0] == 6'h0) &&
                    (r_descriptor.dst_addr[5:0] == 6'h0);
            endproperty
            assert property (address_aligned);
            `endif
        
        endmodule : scheduler_beats
        
