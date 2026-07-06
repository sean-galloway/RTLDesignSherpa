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
// STREAM Simplifications (vs RAPIDS):
//   ✓ Memory-to-memory only (no network, no producer/consumer)
//   ✓ No ctrl_rd/ctrl_wr fields (RAPIDS producer/consumer control)
//   ✓ No alignment fixup (addresses must be aligned)
//   ✓ Beat-based length (not chunks)
//   ✓ No credit management
//   ✓ IRQ event reporting via MonBus (descriptor.gen_irq flag)
//
// Key Features:
//   - Simple FSM: IDLE → FETCH_DESC → XFER_DATA → COMPLETE
//   - Concurrent read/write in XFER_DATA (prevents deadlock)
//   - Beat-based tracking (length in data width units)
//   - Aligned addresses only (no fixup logic)
//   - MonBus event reporting at state transitions
//   - IRQ event generation via MonBus (STREAM_EVENT_IRQ)
//
// Interface Protocol:
//   - Scheduler tells engines "total beats remaining" (not burst length)
//   - Engines decide burst sizes autonomously
//   - Engines report back "beats completed" via done strobes
//   - Scheduler decrements counters until zero (independently for read/write)
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
    // 0 = omit the per-channel completion/error MonBus emitter (area savings;
    // see descriptor_engine.sv -- the perf characterization does not use this
    // trace, so synth strips the r_mon_* registers on the FPGA build).
    parameter bit GEN_MON = 1'b1,
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    // Monitor Bus Parameters
    parameter logic [15:0] MON_AGENT_ID = 16'h0040,  // STREAM Scheduler Agent ID
    parameter logic [7:0]  MON_UNIT_ID = 8'h01,      // Unit identifier
    parameter logic [8:0]  MON_CHANNEL_ID = 9'h000,  // Base channel ID
    // Descriptor Width (FIXED at 256-bit for STREAM)
    // NOTE: This scheduler is STREAM-only (simple memory-to-memory)
    //       For RAPIDS features (producer/consumer, ctrl_rd/ctrl_wr), use rapids_scheduler
    parameter int DESC_WIDTH = 256,
    // TASK-101 (STREAM Extended): when 1, EXT descriptors (desc_type=1) use two
    // dma_address_gen run-base generators (read + write) so a transfer can be
    // strided / 2D-tiled / circular / reverse / transpose. Legacy descriptors
    // and the whole param=0 build keep linear address accumulation verbatim.
    parameter bit USE_ROW_COL_MAJOR_ADDRESSING = 1'b0
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Configuration Interface
    input  logic                        cfg_channel_enable,     // Enable this channel
    input  logic                        cfg_channel_reset,      // Channel reset
    input  logic [31:0]                 cfg_sched_timeout_cycles, // Timeout threshold (cycles)
    input  logic [7:0]                  cfg_sched_timeout_limit,  // Consecutive-timeout windows before fatal escalation (0=never)
    input  logic                        cfg_sched_timeout_enable, // Enable timeout detection

    // Status Interface
    output logic                        scheduler_idle,         // Scheduler idle
    output logic [6:0]                  scheduler_state,        // Current state (for debug) - ONE-HOT

    // Descriptor Engine Interface
    input  logic                        descriptor_valid,
    output logic                        descriptor_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_packet,     // 256-bit STREAM descriptor (chunk 0)
    input  logic [255:0]                descriptor_ext_packet, // Extended chunk 1 (TASK-101; ignored unless desc_type=EXT)
    input  logic                        descriptor_error,      // Error signal FROM descriptor engine

    // Data Read Interface (to AXI Read Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_rd_valid,         // Channel requests read
    output logic [ADDR_WIDTH-1:0]       sched_rd_addr,          // Source address (aligned)
    output logic [31:0]                 sched_rd_beats,         // Beats remaining to read

    // Data Write Interface (to AXI Write Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_wr_valid,         // Channel requests write
    input  logic                        sched_wr_ready,         // Engine ready for channel (used for completion)
    output logic [ADDR_WIDTH-1:0]       sched_wr_addr,          // Destination address (aligned)
    output logic [31:0]                 sched_wr_beats,         // Beats remaining to write

    // Completion Interface (from Engines to Scheduler)
    input  logic                        sched_rd_done_strobe,   // Read burst completed (pulsed)
    input  logic [31:0]                 sched_rd_beats_done,    // Number of beats completed
    input  logic                        sched_wr_done_strobe,   // Write burst ISSUED - AW handshake (pulsed) - advances dst address
    input  logic [31:0]                 sched_wr_beats_done,    // Number of beats issued this pulse
    input  logic                        sched_wr_commit_strobe, // Write burst COMMITTED - B response (pulsed) - gates completion
    input  logic [31:0]                 sched_wr_commit_beats,  // Number of beats committed this pulse

    // Error Signals (from Engines to Scheduler)
    input  logic                        sched_rd_error,         // Read engine error
    input  logic                        sched_wr_error,         // Write engine error
    output logic                        sched_error,            // Scheduler error output (sticky)

    // Sticky/latched error visibility — these survive a transient pulse so
    // the host can decode *which* error tripped CH_ERROR. Cleared on
    // CH_IDLE entry alongside the internal stickies. Exposed for OBS only.
    output logic                        dbg_descriptor_error,   // r_descriptor_error
    output logic                        dbg_read_error_sticky,  // r_read_error_sticky
    output logic                        dbg_write_error_sticky, // r_write_error_sticky
    output logic                        dbg_timeout_expired,    // w_timeout_expired (live)

    // Free-running monitor-time broadcast (sampled on packet emit)
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Interface (128-bit packet + 64-bit side-band timestamp)
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp
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

    // Scheduler FSM (using STREAM package enum - ONE-HOT ENCODED)
    // States: CH_IDLE → CH_FETCH_DESC → CH_XFER_DATA →
    //         CH_COMPLETE → CH_NEXT_DESC (if chained) or back to CH_IDLE
    //
    // CRITICAL: CH_XFER_DATA runs read and write engines CONCURRENTLY
    //           to prevent deadlock when SRAM buffer < transfer size
    channel_state_t r_current_state, w_next_state;

    // State decode wires (for debug/monitoring)
    wire w_state_idle        = (r_current_state == CH_IDLE);
    wire w_state_fetch_desc  = (r_current_state == CH_FETCH_DESC);
    wire w_state_xfer_data   = (r_current_state == CH_XFER_DATA);
    wire w_state_complete    = (r_current_state == CH_COMPLETE);
    wire w_state_next_desc   = (r_current_state == CH_NEXT_DESC);
    wire w_state_error       = (r_current_state == CH_ERROR);

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
    logic [31:0] r_write_beats_remaining;         // Beats left to ISSUE to destination (drives engine + dst address)
    logic [31:0] r_write_beats_to_commit;         // Beats left to COMMIT (B responses) - gates completion

    //=========================================================================
    // TASK-101 Extended-addressing state (run-contiguous)
    //=========================================================================
    // r_descriptor_ext holds chunk 1 (addr-gen cfg) for the current descriptor.
    // w_is_ext gates every extended path: it can only be 1 when the build enables
    // the feature AND the loaded descriptor is EXT -> at param=0 it is a constant
    // 0 and all logic below synthesizes away (legacy linear accumulation).
    descriptor_ext_t r_descriptor_ext;
    logic w_is_ext;
    assign w_is_ext = USE_ROW_COL_MAJOR_ADDRESSING &&
                      (r_descriptor.desc_type == DESC_TYPE_EXT);

    // Per-direction "beats left in the current contiguous run". Capped onto
    // sched_*_beats so the engine never bursts across a run boundary.
    logic [31:0] r_rd_run_remaining;
    logic [31:0] r_wr_run_remaining;

    // Run-base generator interfaces (driven by the generate block below; tied
    // off to 0 when the feature is disabled).
    logic                  w_rd_base_valid, w_rd_base_ready;
    logic [ADDR_WIDTH-1:0] w_rd_base_addr;
    logic                  w_wr_base_valid, w_wr_base_ready;
    logic [ADDR_WIDTH-1:0] w_wr_base_addr;

    // "Between runs" - current run drained, more beats remain, need next base.
    logic w_rd_need_base, w_wr_need_base;
    assign w_rd_need_base = w_is_ext && (r_rd_run_remaining == 32'h0) &&
                            (r_read_beats_remaining != 32'h0);
    assign w_wr_need_base = w_is_ext && (r_wr_run_remaining == 32'h0) &&
                            (r_write_beats_remaining != 32'h0);

    // Pop a base the cycle we both need one and have one prefetched.
    assign w_rd_base_ready = w_rd_need_base;
    assign w_wr_base_ready = w_wr_need_base;

    // One-cycle start pulse to the run-base generators on entry to CH_FETCH_DESC.
    logic r_fetch_desc_d;
    logic w_addrgen_start;
    assign w_addrgen_start = w_state_fetch_desc && !r_fetch_desc_d;

    // Per-direction addressing mode: stride_0 == beat_size -> contiguous inner
    // (run-contiguous bursts); stride_0 != beat_size -> per-beat 2-D (single-beat
    // AXI, e.g. transpose/scatter). beat_size = DATA_WIDTH/8 bytes.
    localparam logic signed [STREAM_ADDRGEN_STRIDE_WIDTH-1:0] BEAT_BYTES =
                    STREAM_ADDRGEN_STRIDE_WIDTH'(DATA_WIDTH/8);
    logic w_rd_per_beat, w_wr_per_beat;
    assign w_rd_per_beat = w_is_ext && (r_descriptor_ext.rd_stride_0 != BEAT_BYTES);
    assign w_wr_per_beat = w_is_ext && (r_descriptor_ext.wr_stride_0 != BEAT_BYTES);

    // Effective run size = beats the engine bursts per run. Per-beat mode forces
    // 1 (single beat); run-contiguous uses inner_count (guarded 0 -> 1).
    logic [31:0] w_rd_inner_beats, w_wr_inner_beats;
    assign w_rd_inner_beats = (r_descriptor_ext.rd_inner_count == '0) ? 32'd1
                                : {16'h0, r_descriptor_ext.rd_inner_count};
    assign w_wr_inner_beats = (r_descriptor_ext.wr_inner_count == '0) ? 32'd1
                                : {16'h0, r_descriptor_ext.wr_inner_count};

    logic [31:0] w_rd_run_size, w_wr_run_size;
    assign w_rd_run_size = w_rd_per_beat ? 32'd1 : w_rd_inner_beats;
    assign w_wr_run_size = w_wr_per_beat ? 32'd1 : w_wr_inner_beats;

    // Initial run size = min(run_size, total length). For legacy the run is the
    // whole transfer, so no boundary occurs before completion.
    logic [31:0] w_rd_run_init, w_wr_run_init;
    assign w_rd_run_init = !w_is_ext ? r_descriptor.length
        : ((w_rd_run_size < r_descriptor.length) ? w_rd_run_size : r_descriptor.length);
    assign w_wr_run_init = !w_is_ext ? r_descriptor.length
        : ((w_wr_run_size < r_descriptor.length) ? w_wr_run_size : r_descriptor.length);

    // Timeout tracking
    // Counts clock cycles while waiting for engine grant (sched_wr_ready)
    // Prevents deadlock if engines don't respond
    logic [31:0] r_timeout_counter;
    logic w_timeout_expired;                      // Pulses when counter >= cfg_sched_timeout_cycles (one per window)

    // Recoverable-timeout escalation.
    // A write-progress timeout is a *liveness* fault, not a data fault: it is
    // reported and the channel keeps waiting (soft timeout), re-arming each window.
    // Only after cfg_sched_timeout_limit consecutive windows with no write progress
    // does it escalate to a fatal, sticky CH_ERROR. cfg_sched_timeout_limit == 0
    // means never escalate (pure soft timeout). Any write progress clears the strikes.
    logic [7:0] r_timeout_strikes;                // Consecutive expired windows
    logic       w_hard_error;                     // Fatal fault -> sticky CH_ERROR
    logic       w_timeout_escalate;               // Soft timeout promoted to fatal

    // Interrupt generation
    // IRQ event is generated via MonBus when descriptor completes with gen_irq flag set

    // Error tracking
    // Sticky error flags - set on error, cleared on return to CH_IDLE
    logic r_read_error_sticky;                    // Read engine reported error
    logic r_write_error_sticky;                   // Write engine reported error
    logic r_descriptor_error;                     // Descriptor engine or internal error

    // Monitor packet generation
    // Registered outputs for MonBus interface (128-bit packet + side-band ts)
    logic                                       r_mon_valid;
    monitor_common_pkg::monitor_packet_t        r_mon_packet;
    monitor_common_pkg::monbus_timestamp_t      r_mon_timestamp;

    // CH_ERROR is sticky-until-reset; without this gate the packet generator
    // would emit STREAM_EVENT_ERROR every cycle and drown DAXMON/RDMON/WRMON
    // traffic in the monbus trace. Latch on first emit, clear on CH_IDLE.
    logic                                       r_error_pkt_sent;

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
    // FSM Flow: IDLE → FETCH_DESC → XFER_DATA → COMPLETE → (chain?) → IDLE
    // Error transitions: Any error condition → CH_ERROR → (cleared?) → CH_IDLE
    //
    // CRITICAL CHANGE: CH_XFER_DATA replaces separate CH_READ_DATA and CH_WRITE_DATA states
    //                  Both read and write engines run CONCURRENTLY to prevent deadlock
    //                  when SRAM buffer size < total transfer size
    always_comb begin
        w_next_state = r_current_state;  // Default: hold current state

        // Priority 1: Channel reset overrides all other transitions
        if (r_channel_reset_active) begin
            w_next_state = CH_IDLE;
        end else begin
            // Priority 2: Error handling. Fatal faults (engine/descriptor errors)
            // wedge into sticky CH_ERROR. A write-progress timeout is recoverable
            // and does NOT wedge here — it only reaches CH_ERROR once it has
            // escalated (cfg_sched_timeout_limit consecutive windows).
            if (w_hard_error || w_timeout_escalate) begin
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
                            w_next_state = CH_XFER_DATA;  // Valid descriptor → start concurrent transfer
                        end else begin
                            w_next_state = CH_ERROR;      // Invalid descriptor → error
                        end
                    end

                    CH_XFER_DATA: begin
                        // Transfer phase: Read and write engines run CONCURRENTLY
                        // - Read engine: Transfers source → SRAM
                        // - Write engine: Transfers SRAM → destination
                        // - Both report progress via done strobes
                        // - Natural backpressure via SRAM full/empty flags
                        //
                        // Exit when the transfer is complete: all source beats read
                        // AND all destination beats COMMITTED (B responses received, via
                        // r_write_beats_to_commit). Committed already implies the write
                        // engine has acknowledged every transaction, so the previous
                        // sched_wr_ready gate is unnecessary here (and would deadlock,
                        // since sched_wr_ready drops once issue finishes, well before the
                        // final B responses arrive).
                        if (w_transfer_complete) begin
                            w_next_state = CH_COMPLETE;
                        end
                        // Note: Stays in XFER_DATA until both conditions met or error
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
                        // Error state - STICKY, stay here until reset
                        // Once in error, only way out is through reset
                        w_next_state = CH_ERROR;
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
            r_descriptor_ext <= '0;
            r_descriptor_loaded <= 1'b0;
            r_src_addr <= 64'h0;
            r_dst_addr <= 64'h0;
            r_beats_remaining <= 32'h0;
            r_read_beats_remaining <= 32'h0;
            r_write_beats_remaining <= 32'h0;
            r_write_beats_to_commit <= 32'h0;
            r_rd_run_remaining <= 32'h0;
            r_wr_run_remaining <= 32'h0;
            r_fetch_desc_d <= 1'b0;
        end else begin
            // Track CH_FETCH_DESC for the one-cycle addr-gen start pulse
            r_fetch_desc_d <= w_state_fetch_desc;

            // Descriptor capture: Sample descriptor_packet when handshake occurs
            // This happens in either CH_IDLE (first descriptor) or CH_NEXT_DESC (chained)
            if ((r_current_state == CH_IDLE || r_current_state == CH_NEXT_DESC) &&
                descriptor_valid && descriptor_ready) begin
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
                // TASK-101: descriptor type (bits [210:208]) + extended chunk 1.
                // For legacy descriptors desc_type=0 and chunk 1 is ignored.
                r_descriptor.desc_type <= desc_type_e'(descriptor_packet[210:208]);
                r_descriptor_ext <= descriptor_ext_packet;

                r_descriptor_loaded <= 1'b1;
            end

            case (r_current_state)
                CH_FETCH_DESC: begin
                    // Transfer initialization: Copy descriptor fields to working registers
                    // These working registers will be updated as transfer progresses
                    r_src_addr <= r_descriptor.src_addr;   // run 0 base (read)
                    r_dst_addr <= r_descriptor.dst_addr;   // run 0 base (write)
                    r_beats_remaining <= r_descriptor.length;
                    r_read_beats_remaining <= r_descriptor.length;
                    r_write_beats_remaining <= r_descriptor.length;
                    r_write_beats_to_commit <= r_descriptor.length;
                    // TASK-101: seed the contiguous-run counters (whole transfer
                    // for legacy, min(inner_count, length) for EXT).
                    r_rd_run_remaining <= w_rd_run_init;
                    r_wr_run_remaining <= w_wr_run_init;
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

                        // Increment source address by bytes transferred (contiguous
                        // WITHIN a run for both legacy and EXT).
                        // Address increment = beats_done << AXSIZE (AXSIZE = log2(DATA_WIDTH/8))
                        r_src_addr <= r_src_addr + (ADDR_WIDTH'(sched_rd_beats_done) << $clog2(DATA_WIDTH/8));

                        // TASK-101: drain the current run (EXT only; legacy run
                        // == total so it never reaches a boundary early).
                        if (w_is_ext) begin
                            r_rd_run_remaining <= (r_rd_run_remaining >= sched_rd_beats_done) ?
                                                (r_rd_run_remaining - sched_rd_beats_done) : 32'h0;
                        end
                    end

                    // TASK-101: run boundary - jump to the next run's base address
                    // and reload the run counter. Occurs the cycle after a run
                    // drains (mutually exclusive with the done-strobe above).
                    if (w_rd_need_base && w_rd_base_valid) begin
                        r_src_addr <= w_rd_base_addr;
                        r_rd_run_remaining <= (r_read_beats_remaining >= w_rd_run_size) ?
                                                w_rd_run_size : r_read_beats_remaining;
                    end

                    // Write ISSUE progress: SRAM → Destination (independent from read!)
                    // Fires on AW handshake. Decrements the ISSUE counter (drives the
                    // engine's next-burst sizing) and advances the destination address
                    // so the next (pipelined) AW targets the right location.
                    if (sched_wr_done_strobe) begin
                        // Decrement by number of beats issued this burst
                        // Saturate at 0 (safety check, shouldn't underflow)
                        r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done) ?
                                                (r_write_beats_remaining - sched_wr_beats_done) : 32'h0;

                        // Increment destination address by bytes transferred (contiguous
                        // WITHIN a run for both legacy and EXT).
                        // Address increment = beats_done << AXSIZE (AXSIZE = log2(DATA_WIDTH/8))
                        r_dst_addr <= r_dst_addr + (ADDR_WIDTH'(sched_wr_beats_done) << $clog2(DATA_WIDTH/8));

                        // TASK-101: drain the current write run (EXT only).
                        if (w_is_ext) begin
                            r_wr_run_remaining <= (r_wr_run_remaining >= sched_wr_beats_done) ?
                                                (r_wr_run_remaining - sched_wr_beats_done) : 32'h0;
                        end
                    end

                    // TASK-101: write run boundary - jump to the next run base.
                    if (w_wr_need_base && w_wr_base_valid) begin
                        r_dst_addr <= w_wr_base_addr;
                        r_wr_run_remaining <= (r_write_beats_remaining >= w_wr_run_size) ?
                                                w_wr_run_size : r_write_beats_remaining;
                    end

                    // Write COMMIT progress: fires on B response (data actually written
                    // to the destination). Decrements the COMMIT counter, which gates
                    // completion (w_write_complete) so a channel is not reported done
                    // until every issued write has been acknowledged.
                    if (sched_wr_commit_strobe) begin
                        r_write_beats_to_commit <= (r_write_beats_to_commit >= sched_wr_commit_beats) ?
                                                (r_write_beats_to_commit - sched_wr_commit_beats) : 32'h0;
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
    // Write is complete only when all issued beats have been COMMITTED (B responses),
    // not merely issued (r_write_beats_remaining). This prevents the channel from
    // signalling done/interrupt while write data is still draining to memory.
    assign w_write_complete = (r_write_beats_to_commit == 32'h0);
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
    logic w_sched_rd_completing_this_cycle;
    logic w_sched_wr_completing_this_cycle;

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
                        !w_sched_rd_completing_this_cycle &&
                        !w_rd_need_base;   // TASK-101: stall reads between runs
    assign sched_rd_addr = r_src_addr;
    // TASK-101: EXT caps the request at the current run so the engine never
    // bursts across a (possibly non-contiguous) run boundary.
    assign sched_rd_beats = w_is_ext ? r_rd_run_remaining : r_read_beats_remaining;

    //=========================================================================
    // Data Write Interface Outputs
    //=========================================================================
    // Scheduler tells engine: "I need this many beats written to this address"
    // Engine decides: "I'll do X beats per burst based on my config/design"
    // Engine reports back: "I moved X beats" via sched_wr_done_strobe
    //
    // CONCURRENT OPERATION: sched_wr_valid asserted in CH_XFER_DATA (not CH_WRITE_DATA)
    //                       Runs simultaneously with read engine

    // Request writes only while there are beats left to ISSUE. This gate used to be
    // implicit in !w_write_complete (which was write_beats_remaining==0), but
    // w_write_complete now tracks COMMITs (r_write_beats_to_commit); without the
    // explicit issue-count gate the engine would keep sched_wr_valid high through the
    // commit-wait and, seeing sched_wr_beats==0, issue a spurious garbage AW
    // (transfer-size underflow -> awlen=0xFF). The scheduler still stays in
    // CH_XFER_DATA waiting for commits; it just stops requesting new writes.
    assign sched_wr_valid = (r_current_state == CH_XFER_DATA) &&
                        (r_write_beats_remaining != 32'h0) &&
                        !w_write_complete &&
                        !w_sched_wr_completing_this_cycle &&
                        !w_wr_need_base;   // TASK-101: stall writes between runs
    assign sched_wr_addr = r_dst_addr;
    // TASK-101: EXT caps the request at the current run (see read side).
    assign sched_wr_beats = w_is_ext ? r_wr_run_remaining : r_write_beats_remaining;

    //=========================================================================
    // TASK-101 Run-base Address Generators (read + write, EXT descriptors)
    //=========================================================================
    // Each generator emits the base address of runs 1..N-1 (run 0 = descriptor
    // src/dst addr, loaded directly). Independent read/write instances give the
    // separate src/dst iteration that transpose and gather/scatter require.
    generate
    if (USE_ROW_COL_MAJOR_ADDRESSING) begin : g_addrgen
        stream_run_addr_gen #(
            .ADDR_WIDTH   (ADDR_WIDTH),
            .STRIDE_WIDTH (STREAM_ADDRGEN_STRIDE_WIDTH),
            .INDEX_WIDTH  (STREAM_ADDRGEN_INDEX_WIDTH),
            .FIFO_DEPTH   (4),
            .BEATS_WIDTH  (32)
        ) u_rd_addr_gen (
            .clk             (clk),
            .rst_n           (rst_n),
            .start           (w_addrgen_start),
            .cfg_per_beat    (w_rd_per_beat),
            .cfg_base_addr   (r_descriptor.src_addr[ADDR_WIDTH-1:0]),
            .cfg_stride_0    (r_descriptor_ext.rd_stride_0),
            .cfg_stride_1    (r_descriptor_ext.rd_stride_1),
            .cfg_wrap_mask_0 (wrap_log2_to_mask(r_descriptor_ext.rd_wrap0_log2)),
            .cfg_wrap_mask_1 (wrap_log2_to_mask(r_descriptor_ext.rd_wrap1_log2)),
            .cfg_inner_count (r_descriptor_ext.rd_inner_count),
            .cfg_total_beats (r_descriptor.length),
            .o_base_valid    (w_rd_base_valid),
            .i_base_ready    (w_rd_base_ready),
            .o_base_addr     (w_rd_base_addr)
        );
        stream_run_addr_gen #(
            .ADDR_WIDTH   (ADDR_WIDTH),
            .STRIDE_WIDTH (STREAM_ADDRGEN_STRIDE_WIDTH),
            .INDEX_WIDTH  (STREAM_ADDRGEN_INDEX_WIDTH),
            .FIFO_DEPTH   (4),
            .BEATS_WIDTH  (32)
        ) u_wr_addr_gen (
            .clk             (clk),
            .rst_n           (rst_n),
            .start           (w_addrgen_start),
            .cfg_per_beat    (w_wr_per_beat),
            .cfg_base_addr   (r_descriptor.dst_addr[ADDR_WIDTH-1:0]),
            .cfg_stride_0    (r_descriptor_ext.wr_stride_0),
            .cfg_stride_1    (r_descriptor_ext.wr_stride_1),
            .cfg_wrap_mask_0 (wrap_log2_to_mask(r_descriptor_ext.wr_wrap0_log2)),
            .cfg_wrap_mask_1 (wrap_log2_to_mask(r_descriptor_ext.wr_wrap1_log2)),
            .cfg_inner_count (r_descriptor_ext.wr_inner_count),
            .cfg_total_beats (r_descriptor.length),
            .o_base_valid    (w_wr_base_valid),
            .i_base_ready    (w_wr_base_ready),
            .o_base_addr     (w_wr_base_addr)
        );
    end else begin : g_no_addrgen
        assign w_rd_base_valid = 1'b0;
        assign w_rd_base_addr  = '0;
        assign w_wr_base_valid = 1'b0;
        assign w_wr_base_addr  = '0;
    end
    endgenerate

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
            r_timeout_strikes <= 8'h0;
            r_read_error_sticky <= 1'b0;
            r_write_error_sticky <= 1'b0;
            r_descriptor_error <= 1'b0;
        end else begin
            // Timeout counter: Increments while waiting for write engine completion
            // Counts cycles where sched_wr_valid is high but ready is low
            // Any write progress resets the timeout: an AW issue (done strobe) OR a
            // B response (commit strobe). This matters because completion is now gated
            // on commits: sched_wr_valid stays high through the commit-wait while
            // sched_wr_ready is low (engine done issuing), so without treating commits
            // as progress the counter would falsely time out a slow-draining transfer.
            // On expiry the counter RE-ARMS (soft timeout): it emits a one-cycle
            // w_timeout_expired pulse per elapsed window rather than latching.
            if (sched_wr_done_strobe || sched_wr_commit_strobe) begin
                r_timeout_counter <= 32'h0;  // write progress -> not stalled
            end else if (w_timeout_expired) begin
                r_timeout_counter <= 32'h0;  // window elapsed -> re-arm, keep waiting
            end else if (sched_wr_valid && !sched_wr_ready) begin
                r_timeout_counter <= r_timeout_counter + 1;
            end else begin
                r_timeout_counter <= 32'h0;  // Reset when not waiting or completion received
            end

            // Consecutive-timeout strikes: one per elapsed window with no write
            // progress. Cleared by real progress or on return to CH_IDLE. Saturates.
            if (r_channel_reset_active || (r_current_state == CH_IDLE)) begin
                r_timeout_strikes <= 8'h0;
            end else if (sched_wr_done_strobe || sched_wr_commit_strobe) begin
                r_timeout_strikes <= 8'h0;
            end else if (w_timeout_expired && !(&r_timeout_strikes)) begin
                r_timeout_strikes <= r_timeout_strikes + 8'h1;
            end

            // Error capture: Latch errors from external components
            // Sticky flags ensure errors aren't lost due to transient de-assertion
            if (descriptor_error) r_descriptor_error <= 1'b1;   // Descriptor engine error
            if (sched_rd_error) r_read_error_sticky <= 1'b1;    // Read engine error
            if (sched_wr_error) r_write_error_sticky <= 1'b1;   // Write engine error

            // Latch a fatal descriptor_error for genuine faults OR an ESCALATED
            // timeout (cfg_sched_timeout_limit consecutive windows). A bare timeout
            // window is recoverable and deliberately NOT latched here.
            if (sched_rd_error || sched_wr_error || w_timeout_escalate) begin
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


    // Timeout threshold: Compare counter to configured limit (if enabled)
    assign w_timeout_expired = cfg_sched_timeout_enable &&
                               (r_timeout_counter >= cfg_sched_timeout_cycles);

    // Escalate a recoverable timeout to a fatal fault only after cfg_sched_timeout_limit
    // consecutive windows (0 = never escalate: pure soft timeout).
    assign w_timeout_escalate = (cfg_sched_timeout_limit != 8'd0) &&
                                (r_timeout_strikes >= cfg_sched_timeout_limit);

    // Fatal faults: data-path integrity compromised -> sticky CH_ERROR until reset.
    // (A bare timeout window is a recoverable liveness fault, not included here.)
    assign w_hard_error = descriptor_error || sched_rd_error || sched_wr_error ||
                          r_read_error_sticky || r_write_error_sticky;

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
            r_mon_valid       <= 1'b0;
            r_mon_packet      <= '0;
            r_mon_timestamp   <= '0;
            r_error_pkt_sent  <= 1'b0;
        end else begin
            // Default: Clear monitor packet (single-cycle pulse)
            r_mon_valid  <= 1'b0;
            r_mon_packet <= '0;
            // Sample i_mon_time on emit; hold previous between pulses.

            // Clear the one-shot when the FSM leaves CH_ERROR (CH_IDLE on
            // recovery / reset path); next CH_ERROR visit will emit again.
            if (r_current_state == CH_IDLE) begin
                r_error_pkt_sent <= 1'b0;
            end

            case (r_current_state)
                CH_FETCH_DESC: begin
                    // Event: Descriptor processing started
                    // Payload: Transfer length in beats
                    r_mon_valid     <= 1'b1;
                    r_mon_timestamp <= i_mon_time;
                    r_mon_packet    <= create_monitor_packet(
                        PktTypeCompletion,
                        PROTOCOL_CORE,
                        STREAM_EVENT_DESC_START,
                        MON_CHANNEL_ID,
                        MON_UNIT_ID,
                        MON_AGENT_ID,
                        {32'h0, r_descriptor.length}  // Payload: 32-bit length zero-extended to 64
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
                    r_mon_valid     <= 1'b1;
                    r_mon_timestamp <= i_mon_time;
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
                            {32'h0, r_descriptor.length}  // Payload: 32-bit length zero-extended to 64
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
                            {32'h0, r_descriptor.length}  // Payload: 32-bit length zero-extended to 64
                        );
                    end
                end

                CH_ERROR: begin
                    // Event: Error detected (any source)
                    // Payload: Error flags packed in upper bits of the 64-bit field.
                    // Position preserved to match the original 35-bit layout —
                    // write_error at bit [34], read_error at bit [33]; remainder
                    // is zero padded to 64 bits.
                    //
                    // One-shot: CH_ERROR is sticky, so guard against re-emitting
                    // the same error packet every cycle (it would otherwise drown
                    // the trace SRAM).
                    if (!r_error_pkt_sent) begin
                        r_mon_valid      <= 1'b1;
                        r_mon_timestamp  <= i_mon_time;
                        r_mon_packet     <= create_monitor_packet(
                            PktTypeError,
                            PROTOCOL_CORE,
                            STREAM_EVENT_ERROR,
                            MON_CHANNEL_ID,
                            MON_UNIT_ID,
                            MON_AGENT_ID,
                            {29'h0, r_write_error_sticky, r_read_error_sticky, 33'h0}
                        );
                        r_error_pkt_sent <= 1'b1;
                    end
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

    // Only CH_IDLE is "idle". CH_ERROR is a faulted channel and must NOT report
    // idle — reporting CH_ERROR as idle is what let CHANNEL_IDLE read '1' on a
    // wedged channel. A faulted channel is surfaced via sched_error/CHANNEL_ERROR.
    assign scheduler_idle = (r_current_state == CH_IDLE) && !r_channel_reset_active;
    assign scheduler_state = r_current_state;
    assign sched_error = w_state_error;  // Sticky error output

    // Stickies + live timeout exposed for the channel-observation mux.
    assign dbg_descriptor_error   = r_descriptor_error;
    assign dbg_read_error_sticky  = r_read_error_sticky;
    assign dbg_write_error_sticky = r_write_error_sticky;
    assign dbg_timeout_expired    = w_timeout_expired;

    // Monitor bus output (GEN_MON=0 ties off so synth strips the r_mon_* regs)
    assign mon_valid     = GEN_MON ? r_mon_valid     : 1'b0;
    assign mon_packet    = GEN_MON ? r_mon_packet    : '0;
    assign mon_timestamp = GEN_MON ? r_mon_timestamp : '0;

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

endmodule : scheduler
