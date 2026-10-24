// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler
// Purpose: STREAM Scheduler - Simple Memory-to-Memory DMA
//
// Structure (stream TASK-020, as rapids TASK-034 did for RAPIDS): this module
// is the channel FSM and the two EXT run-base generators wrapped around
// scheduler_core, which holds the datapath (descriptor skid and latch,
// counters, the read-ahead prefetch, commit accounting, timeouts, errors,
// MonBus). The gatling-sequenced scheduler_g (fub_g/) wraps the same core and
// takes the state, the edges and the run bases from firmware instead.
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
// Documentation: projects/components/dma-ip/stream_fub/PRD.md
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
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 1
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

    // Read-ahead descriptor prefetch enable (runtime, default enabled via regmap
    // SCHED_CONFIG.RD_PREFETCH_EN). When set, on a CHAINED LEGACY descriptor the
    // read side loads the next descriptor's read flops (src_addr / read-beats)
    // from the descriptor-FIFO head *without draining the FIFO* -- so reads keep
    // filling SRAM with descriptor N+1 while the write side is still draining N.
    // The write side later reloads its flops and drains the FIFO, catching up.
    // The SRAM is an in-order FIFO between the two directions, so racing reads
    // ahead is safe (N+1's data queues behind N's). Clearing it forces the
    // lockstep single-descriptor behavior (for on-silicon A/B on one bitstream).
    // EXT (TASK-101) descriptors always run lockstep regardless (their run-base
    // addr-gens are single-descriptor). See r_rd_ahead below.
    input  logic                        cfg_rd_prefetch_enable,

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
    input  ocelus_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Interface (128-bit packet + 64-bit side-band timestamp)
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output ocelus_common_pkg::monitor_packet_t     mon_packet,
    output ocelus_common_pkg::monbus_timestamp_t   mon_timestamp
);

    //=========================================================================
    // Datapath (shared with scheduler_g)
    //=========================================================================

    channel_state_t        r_current_state, w_next_state;
    descriptor_t           w_desc;
    descriptor_ext_t       w_desc_ext;
    logic                  w_desc_head_valid, w_desc_is_ext, w_rd_per_beat, w_wr_per_beat;
    logic                  w_wr_advance, w_rd_ahead, w_exec_complete, w_write_complete;
    logic                  w_hard_error, w_timeout_escalate, w_channel_reset_active;
    logic                  w_desc_take, w_launch, w_addrgen_start;
    logic                  w_rd_base_valid, w_rd_base_ready, w_wr_base_valid, w_wr_base_ready;
    logic [ADDR_WIDTH-1:0] w_rd_base_addr, w_wr_base_addr;

    scheduler_core #(
        .CHANNEL_ID                  (CHANNEL_ID),
        .GEN_MON                     (GEN_MON),
        .NUM_CHANNELS                (NUM_CHANNELS),
        .CHAN_WIDTH                  (CHAN_WIDTH),
        .ADDR_WIDTH                  (ADDR_WIDTH),
        .DATA_WIDTH                  (DATA_WIDTH),
        .MON_AGENT_ID                (MON_AGENT_ID),
        .MON_UNIT_ID                 (MON_UNIT_ID),
        .MON_CHANNEL_ID              (MON_CHANNEL_ID),
        .DESC_WIDTH                  (DESC_WIDTH),
        .USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING)
    ) u_core (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .cfg_channel_enable      (cfg_channel_enable),
        .cfg_channel_reset       (cfg_channel_reset),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit (cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        .cfg_rd_prefetch_enable  (cfg_rd_prefetch_enable),
        .scheduler_idle          (scheduler_idle),
        .descriptor_valid        (descriptor_valid),
        .descriptor_ready        (descriptor_ready),
        .descriptor_packet       (descriptor_packet),
        .descriptor_ext_packet   (descriptor_ext_packet),
        .descriptor_error        (descriptor_error),
        .sched_rd_valid          (sched_rd_valid),
        .sched_rd_addr           (sched_rd_addr),
        .sched_rd_beats          (sched_rd_beats),
        .sched_wr_valid          (sched_wr_valid),
        .sched_wr_ready          (sched_wr_ready),
        .sched_wr_addr           (sched_wr_addr),
        .sched_wr_beats          (sched_wr_beats),
        .sched_rd_done_strobe    (sched_rd_done_strobe),
        .sched_rd_beats_done     (sched_rd_beats_done),
        .sched_wr_done_strobe    (sched_wr_done_strobe),
        .sched_wr_beats_done     (sched_wr_beats_done),
        .sched_wr_commit_strobe  (sched_wr_commit_strobe),
        .sched_wr_commit_beats   (sched_wr_commit_beats),
        .sched_rd_error          (sched_rd_error),
        .sched_wr_error          (sched_wr_error),
        .sched_error             (sched_error),
        .dbg_descriptor_error    (dbg_descriptor_error),
        .dbg_read_error_sticky   (dbg_read_error_sticky),
        .dbg_write_error_sticky  (dbg_write_error_sticky),
        .dbg_timeout_expired     (dbg_timeout_expired),
        .i_mon_time              (i_mon_time),
        .mon_valid               (mon_valid),
        .mon_ready               (mon_ready),
        .mon_packet              (mon_packet),
        .mon_timestamp           (mon_timestamp),
        .state                   (r_current_state),
        .desc_take               (w_desc_take),
        .launch                  (w_launch),
        .rd_beats_total          (w_desc.length),      // length is in beats
        .wr_beats_total          (w_desc.length),
        .head_ok                 (1'b1),               // the FSM prefetches any head
        .rd_base_valid           (w_rd_base_valid),
        .rd_base_addr            (w_rd_base_addr),
        .rd_base_ready           (w_rd_base_ready),
        .wr_base_valid           (w_wr_base_valid),
        .wr_base_addr            (w_wr_base_addr),
        .wr_base_ready           (w_wr_base_ready),
        .addrgen_start           (w_addrgen_start),
        .desc_head_valid         (w_desc_head_valid),
        /* verilator lint_off PINCONNECTEMPTY */
        .desc_head_packet        (),                   // only scheduler_g pre-validates
        /* verilator lint_on PINCONNECTEMPTY */
        .desc_latched            (w_desc),
        .desc_ext_latched        (w_desc_ext),
        .desc_is_ext             (w_desc_is_ext),
        .desc_rd_per_beat        (w_rd_per_beat),
        .desc_wr_per_beat        (w_wr_per_beat),
        .wr_advance              (w_wr_advance),
        .rd_ahead                (w_rd_ahead),
        .exec_complete           (w_exec_complete),
        .write_complete          (w_write_complete),
        .hard_error              (w_hard_error),
        .timeout_escalate        (w_timeout_escalate),
        .channel_reset_active    (w_channel_reset_active)
    );

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
    // FSM Flow: IDLE -> FETCH_DESC -> XFER_DATA -> COMPLETE -> (chain?) -> IDLE
    // Error transitions: any fatal fault -> CH_ERROR, sticky until a channel reset
    always_comb begin
        w_next_state = r_current_state;  // Default: hold current state

        // Priority 1: Channel reset overrides all other transitions
        if (w_channel_reset_active) begin
            w_next_state = CH_IDLE;
        end else begin
            // Priority 2: Error handling. Fatal faults (engine/descriptor errors)
            // wedge into sticky CH_ERROR. A write-progress timeout is recoverable
            // and does NOT wedge here -- it only reaches CH_ERROR once it has
            // escalated (cfg_sched_timeout_limit consecutive windows).
            if (w_hard_error || w_timeout_escalate) begin
                w_next_state = CH_ERROR;
            end else begin
                // Priority 3: Normal state machine transitions
                case (r_current_state)
                    CH_IDLE: begin
                        // A current-epoch descriptor at the skid head and the
                        // channel enabled
                        if (w_desc_head_valid && cfg_channel_enable) begin
                            w_next_state = CH_FETCH_DESC;
                        end
                    end

                    CH_FETCH_DESC: begin
                        // Descriptor latched in one cycle; validate its valid bit
                        if (w_desc.valid) begin
                            w_next_state = CH_XFER_DATA;  // Valid descriptor -> start concurrent transfer
                        end else begin
                            w_next_state = CH_ERROR;      // Invalid descriptor -> error
                        end
                    end

                    CH_XFER_DATA: begin
                        // Read and write engines run CONCURRENTLY in the core.
                        // A read-ahead in-place advance (chained legacy
                        // descriptor, cfg_rd_prefetch_enable) stays in XFER_DATA;
                        // otherwise leave when the core reports reads done and
                        // writes issued (and the read side is not ahead).
                        if (w_wr_advance) begin
                            w_next_state = CH_XFER_DATA;  // in-place descriptor advance
                        end else if (w_exec_complete) begin
                            w_next_state = CH_COMPLETE;
                        end
                    end

                    CH_COMPLETE: begin
                        // Chained: advance IMMEDIATELY (this descriptor's writes were
                        // only ISSUED; they commit in the background while the next
                        // descriptor streams). Last: HOLD here until every write has
                        // COMMITTED so the channel is not reported done before data lands.
                        if (w_desc.next_descriptor_ptr != 32'h0 && !w_desc.last) begin
                            w_next_state = CH_NEXT_DESC;  // chained -> advance now (issue-based)
                        end else if (w_write_complete) begin
                            w_next_state = CH_IDLE;       // last -> done only after all commits land
                        end
                    end

                    CH_NEXT_DESC: begin
                        // Wait for the chained descriptor to reach the skid head
                        if (w_desc_head_valid) begin
                            w_next_state = CH_FETCH_DESC;
                        end
                    end

                    CH_ERROR: begin
                        // Error state - STICKY, stay here until a channel reset
                        w_next_state = CH_ERROR;
                    end

                    default: begin
                        // Safety: undefined state -> error
                        w_next_state = CH_ERROR;
                    end
                endcase
            end
        end
    end

    // The skid head is taken in CH_IDLE (channel enabled) and CH_NEXT_DESC; the
    // core adds the read-ahead in-place advance itself. CH_IDLE pops only while
    // the channel is enabled: a disabled channel used to pop and discard every
    // descriptor reaching its queue (found in RAPIDS 2026-10-17).
    assign w_desc_take = ((r_current_state == CH_IDLE) && cfg_channel_enable) ||
                         (r_current_state == CH_NEXT_DESC);
    // A descriptor launches on the FETCH_DESC -> XFER_DATA edge (the commit
    // accumulator adds its length then)
    assign w_launch = (r_current_state == CH_FETCH_DESC) && (w_next_state == CH_XFER_DATA);

    assign scheduler_state = r_current_state;

    //=========================================================================
    // TASK-101 Run-base Address Generators (read + write, EXT descriptors)
    //=========================================================================
    // Each generator emits the base address of runs 1..N-1 (run 0 = descriptor
    // src/dst addr, loaded directly). Independent read/write instances give the
    // separate src/dst iteration that transpose and gather/scatter require.
    // scheduler_g replaces them with firmware-filled FIFOs on the same ports.
    generate
    if (USE_ROW_COL_MAJOR_ADDRESSING != 0) begin : g_addrgen
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
            .flush           (w_channel_reset_active),   // a channel reset empties it (rapids BUG-017)
            .cfg_per_beat    (w_rd_per_beat),
            .cfg_base_addr   (w_desc.src_addr[ADDR_WIDTH-1:0]),
            .cfg_stride_0    (w_desc_ext.rd_stride_0),
            .cfg_stride_1    (w_desc_ext.rd_stride_1),
            .cfg_wrap_mask_0 (ADDR_WIDTH'(wrap_log2_to_mask(w_desc_ext.rd_wrap0_log2))),
            .cfg_wrap_mask_1 (ADDR_WIDTH'(wrap_log2_to_mask(w_desc_ext.rd_wrap1_log2))),
            .cfg_inner_count (w_desc_ext.rd_inner_count),
            .cfg_total_beats (w_desc.length),
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
            .flush           (w_channel_reset_active),   // a channel reset empties it (rapids BUG-017)
            .cfg_per_beat    (w_wr_per_beat),
            .cfg_base_addr   (w_desc.dst_addr[ADDR_WIDTH-1:0]),
            .cfg_stride_0    (w_desc_ext.wr_stride_0),
            .cfg_stride_1    (w_desc_ext.wr_stride_1),
            .cfg_wrap_mask_0 (ADDR_WIDTH'(wrap_log2_to_mask(w_desc_ext.wr_wrap0_log2))),
            .cfg_wrap_mask_1 (ADDR_WIDTH'(wrap_log2_to_mask(w_desc_ext.wr_wrap1_log2))),
            .cfg_inner_count (w_desc_ext.wr_inner_count),
            .cfg_total_beats (w_desc.length),
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
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Concurrent transfer completion: Exit CH_XFER_DATA only when the core
    // reports reads done AND all writes ISSUED (advance is issue-based so
    // chained descriptors stream; write COMMITs gate only CH_COMPLETE -> CH_IDLE).
    property concurrent_transfer_complete;
        @(posedge clk) disable iff (!rst_n)
        (r_current_state == CH_XFER_DATA && w_next_state == CH_COMPLETE) |-> w_exec_complete;
    endproperty
    assert property (concurrent_transfer_complete);
    `endif

endmodule : scheduler
