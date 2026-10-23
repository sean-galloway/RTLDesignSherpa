// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler
// Purpose: RAPIDS Scheduler - byte-granular DMA (rapids TASK-019)
//
// Structure (rapids TASK-034): this module is the channel FSM, the
// bytes-to-beats ceiling and the two EXT run-base generators wrapped around
// scheduler_core, which holds the datapath. The gatling-sequenced
// scheduler_g (fub_g/) wraps the same core and takes those three from
// firmware instead.
//
// Byte granularity: descriptor length is in BYTES, src/dst are byte addresses.
// The scheduler derives the beat counts the engines work in
// (ceil((offset + length) / BYTE_LANES)), advances addresses on beat
// boundaries after the first burst, and hands each DATA descriptor's
// {bytes, offset} to the data paths as a packet record so the sink ingress
// can place bytes and the source egress can mark the partial last beat.
// The beat-granular predecessor is fub_beats/scheduler_beats.sv.
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
//   The scheduler runs read and write engines CONCURRENTLY in rapids_pkg::CH_XFER_DATA state.
//   This prevents deadlock when transfer size > SRAM buffer size:
//     - Read fills SRAM → SRAM full → read pauses
//     - Write drains SRAM → SRAM has space → read resumes
//   Without concurrency, 100MB transfer with 2KB SRAM would deadlock!
//
// RAPIDS descriptor opcodes (rapids_pkg desc_op_e):
//   OK DATA       - concurrent read/write engines (network-to-memory via AXIS)
//   OK CTRL_READ  - consumer gate: poll ctrlrd_addr until (rd & mask)==expected,
//                  bounded by CTRL_CONFIG.CTRLRD_MAX_TRY (drives the ctrlrd_engine)
//   OK CTRL_WRITE - producer doorbell: single-beat write of ctrlwr_data to
//                  ctrlwr_addr, then continue (drives the ctrlwr_engine)
// Simplifications retained:
//   OK No alignment fixup (addresses must be aligned)
//   OK Beat-based length (not chunks)
//   OK No credit management
//   OK IRQ event reporting via MonBus (descriptor.gen_irq flag)
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
// Documentation: projects/components/dma-ip/rapids/PRD.md
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common RAPIDS and monitor packages
`include "rapids_imports.svh"
`include "reset_defs.svh"

module scheduler #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    // Monitor Bus Parameters
    parameter logic [15:0] MON_AGENT_ID  = 16'h0040,  // 16-bit agent ID (128-bit packet)
    parameter logic [7:0]  MON_UNIT_ID   = 8'h01,     // 8-bit unit ID
    parameter logic [8:0]  MON_CHANNEL_ID = 9'h000,   // 9-bit base channel ID
    // Descriptor Width (FIXED at 256-bit for RAPIDS Phase 1)
    // NOTE: This scheduler is RAPIDS Phase 1 (simplified network-to-memory)
    //       Phase 2 will add credit management and control engines
    parameter int DESC_WIDTH = 256,
    // Direction enables for DATA descriptors. Default (both=1) preserves the
    // original mem-to-mem behavior. A directional half sets exactly one:
    //   SOURCE half (mem -> AXIS): EN_READ=1, EN_WRITE=0 (read-only)
    //   SINK   half (AXIS -> mem): EN_READ=0, EN_WRITE=1 (write-only)
    // Loading 0 beats in the disabled direction makes its sched_*_valid
    // self-gate and collapses completion onto the active direction.
    parameter bit EN_READ  = 1'b1,
    parameter bit EN_WRITE = 1'b1,
    // Extended (row/col-major) addressing. When 1, an EXT descriptor uses two
    // stream_run_addr_gen run-base generators (read + write) so a transfer can
    // be strided / 2-D tiled / circular / reverse / transpose. Legacy
    // descriptors and the whole param=0 build keep linear accumulation.
    // Default ON, matching STREAM.
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 1,
    // Byte-granular RAPIDS (rapids TASK-019): the descriptor length is in
    // BYTES and src/dst addresses carry a byte offset within the first beat.
    parameter int BYTE_LANES = DATA_WIDTH / 8,
    parameter int OFF_W = (BYTE_LANES > 1) ? $clog2(BYTE_LANES) : 1,
    // Tile packet header (TILE_SPEC 11.5). When 1, a source descriptor's
    // ptype / op / dst_addr ride the packet record (sched_rd_pkt_tile) and
    // op = 1 (read request) moves no memory: the packet is the header alone.
    parameter int TILE_HDR = 0,
    // End-to-end tile credits (TILE_SPEC 11.9, 11.10; needs TILE_HDR = 1).
    // When 1, a tile descriptor waits in CH_FETCH_DESC until the
    // advertisement window closes, then is refused as invalid if its
    // destination is not legal.
    parameter int TILE_CREDITS = 0
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

    // Tile credits (TILE_CREDITS): the advertisement window has closed, and
    // the saved legal-destination mask (rapids_tile_credits)
    input  logic                        tile_adv_done,
    input  logic [rapids_pkg::TILE_NUM_DEST-1:0] tile_dest_legal,

    // Status Interface
    output logic                        scheduler_idle,         // Scheduler idle
    output logic [6:0]                  scheduler_state,        // Current state (for debug) - ONE-HOT

    // Descriptor Engine Interface
    input  logic                        descriptor_valid,
    output logic                        descriptor_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_packet,     // 256-bit RAPIDS descriptor
    input  logic [255:0]                descriptor_ext_packet, // Extended chunk 1 (ignored unless type=EXT)
    input  logic                        descriptor_error,      // Error signal FROM descriptor engine

    // Data Read Interface (to AXI Read Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_rd_valid,         // Channel requests read
    output logic [ADDR_WIDTH-1:0]       sched_rd_addr,          // Source address (aligned)
    output logic [31:0]                 sched_rd_beats,         // Beats remaining to read
    // Packet record to the source egress (TASK-019): one pulse per DATA
    // descriptor as it leaves CH_FETCH_DESC, carrying the byte length and the
    // source byte offset within the first beat. Held in FETCH_DESC while the
    // data path's record queue is full.
    output logic                        sched_rd_pkt_valid,
    input  logic                        sched_rd_pkt_ready,
    output logic [31:0]                 sched_rd_pkt_bytes,
    output logic [OFF_W-1:0]            sched_rd_pkt_offset,
    // {op, ptype, dst_addr} of the descriptor, for the tile header (TILE_HDR)
    output logic [rapids_pkg::TILE_PKT_W-1:0] sched_rd_pkt_tile,

    // Data Write Interface (to AXI Write Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_wr_valid,         // Channel requests write
    input  logic                        sched_wr_ready,         // Engine ready for channel (used for completion)
    output logic [ADDR_WIDTH-1:0]       sched_wr_addr,          // Destination address (aligned)
    output logic [31:0]                 sched_wr_beats,         // Beats remaining to write
    // Packet record to the sink ingress (TASK-019): byte length and the
    // destination byte offset of this descriptor.
    output logic                        sched_wr_pkt_valid,
    input  logic                        sched_wr_pkt_ready,
    output logic [31:0]                 sched_wr_pkt_bytes,
    output logic [OFF_W-1:0]            sched_wr_pkt_offset,

    // Completion Interface (from Engines to Scheduler)
    input  logic                        sched_rd_done_strobe,   // Read burst completed (pulsed)
    input  logic [31:0]                 sched_rd_beats_done,    // Number of beats completed
    input  logic                        sched_wr_done_strobe,   // Write burst ISSUED - AW handshake (pulsed) - advances dst address
    input  logic [31:0]                 sched_wr_beats_done,    // Number of beats issued this pulse
    input  logic                        sched_wr_commit_strobe, // Write burst COMMITTED - B response (pulsed) - gates completion
    input  logic [31:0]                 sched_wr_commit_beats,  // Number of beats committed this pulse

    // Control Read Engine Interface (Phase 2 producer/consumer GATE)
    // Driven only for a CTRL_READ descriptor: request the engine poll ctrlrd_addr
    // until (read & mask)==data; the chain is held off until it matches or errors.
    output logic                        ctrlrd_valid,           // Request valid (to ctrlrd_engine)
    input  logic                        ctrlrd_ready,           // Engine accepted the request
    output logic [ADDR_WIDTH-1:0]       ctrlrd_addr,            // Poll address (descriptor src_addr slot)
    output logic [31:0]                 ctrlrd_data,            // Expected value
    output logic [31:0]                 ctrlrd_mask,            // Compare mask
    input  logic                        ctrlrd_error,           // Engine error (max-retries / AXI error)
    input  logic                        ctrlrd_idle,            // ctrlrd_engine_idle (completion when high post-issue)

    // Control Write Engine Interface (Phase 2 producer/consumer DOORBELL)
    // Driven only for a CTRL_WRITE descriptor: write ctrlwr_data to ctrlwr_addr.
    output logic                        ctrlwr_valid,           // Request valid (to ctrlwr_engine)
    input  logic                        ctrlwr_ready,           // Engine accepted the request
    output logic [ADDR_WIDTH-1:0]       ctrlwr_addr,            // Doorbell address (descriptor src_addr slot)
    output logic [31:0]                 ctrlwr_data,            // Doorbell data
    input  logic                        ctrlwr_error,           // Engine error (AXI error)
    input  logic                        ctrlwr_idle,            // ctrlwr_engine_idle (completion when high post-issue)

    // Error Signals (from Engines to Scheduler)
    input  logic                        sched_rd_error,         // Read engine error
    input  logic                        sched_wr_error,         // Write engine error
    output logic                        sched_error,            // Scheduler error output (sticky)

    // Debug/observability outputs (parity with STREAM scheduler)
    output logic                        dbg_descriptor_error,   // r_descriptor_error
    output logic                        dbg_read_error_sticky,  // r_read_error_sticky
    output logic                        dbg_write_error_sticky, // r_write_error_sticky
    output logic                        dbg_timeout_expired,    // w_timeout_expired (live)

    // Monitor Bus Interface (128-bit packet + 64-bit side-band timestamp)
    input  ocelus_common_pkg::monbus_timestamp_t  i_mon_time,
    output logic                                   mon_valid,
    input  logic                                   mon_ready,
    output ocelus_common_pkg::monitor_packet_t    mon_packet,
    output ocelus_common_pkg::monbus_timestamp_t  mon_timestamp
);

    //=========================================================================
    // Datapath (shared with scheduler_g)
    //=========================================================================

    rapids_pkg::channel_state_t  r_current_state, w_next_state;
    rapids_pkg::descriptor_t     w_desc;
    rapids_pkg::descriptor_ext_t w_desc_ext;
    logic [1:0]                  w_desc_opcode;
    logic                        w_desc_head_valid, w_desc_is_ext, w_desc_hdr_only;
    logic                        w_rd_per_beat, w_wr_per_beat;
    logic                        w_tile_bad, w_pkt_ok, w_exec_complete;
    logic                        w_hard_error, w_timeout_escalate, w_channel_reset_active;
    logic                        w_desc_take;
    logic [31:0]                 w_rd_beats_total, w_wr_beats_total;
    logic                        w_rd_base_valid, w_rd_base_ready, w_wr_base_valid, w_wr_base_ready;
    logic [ADDR_WIDTH-1:0]       w_rd_base_addr, w_wr_base_addr;
    logic                        w_addrgen_start;

    scheduler_core #(
        .CHANNEL_ID                  (CHANNEL_ID),
        .NUM_CHANNELS                (NUM_CHANNELS),
        .CHAN_WIDTH                  (CHAN_WIDTH),
        .ADDR_WIDTH                  (ADDR_WIDTH),
        .DATA_WIDTH                  (DATA_WIDTH),
        .MON_AGENT_ID                (MON_AGENT_ID),
        .MON_UNIT_ID                 (MON_UNIT_ID),
        .MON_CHANNEL_ID              (MON_CHANNEL_ID),
        .DESC_WIDTH                  (DESC_WIDTH),
        .EN_READ                     (EN_READ),
        .EN_WRITE                    (EN_WRITE),
        .USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING),
        .BYTE_LANES                  (BYTE_LANES),
        .OFF_W                       (OFF_W),
        .TILE_HDR                    (TILE_HDR),
        .TILE_CREDITS                (TILE_CREDITS)
    ) u_core (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .cfg_channel_enable      (cfg_channel_enable),
        .cfg_channel_reset       (cfg_channel_reset),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit (cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        .tile_adv_done           (tile_adv_done),
        .tile_dest_legal         (tile_dest_legal),
        .scheduler_idle          (scheduler_idle),
        .descriptor_valid        (descriptor_valid),
        .descriptor_ready        (descriptor_ready),
        .descriptor_packet       (descriptor_packet),
        .descriptor_ext_packet   (descriptor_ext_packet),
        .descriptor_error        (descriptor_error),
        .sched_rd_valid          (sched_rd_valid),
        .sched_rd_addr           (sched_rd_addr),
        .sched_rd_beats          (sched_rd_beats),
        .sched_rd_pkt_valid      (sched_rd_pkt_valid),
        .sched_rd_pkt_ready      (sched_rd_pkt_ready),
        .sched_rd_pkt_bytes      (sched_rd_pkt_bytes),
        .sched_rd_pkt_offset     (sched_rd_pkt_offset),
        .sched_rd_pkt_tile       (sched_rd_pkt_tile),
        .sched_wr_valid          (sched_wr_valid),
        .sched_wr_ready          (sched_wr_ready),
        .sched_wr_addr           (sched_wr_addr),
        .sched_wr_beats          (sched_wr_beats),
        .sched_wr_pkt_valid      (sched_wr_pkt_valid),
        .sched_wr_pkt_ready      (sched_wr_pkt_ready),
        .sched_wr_pkt_bytes      (sched_wr_pkt_bytes),
        .sched_wr_pkt_offset     (sched_wr_pkt_offset),
        .sched_rd_done_strobe    (sched_rd_done_strobe),
        .sched_rd_beats_done     (sched_rd_beats_done),
        .sched_wr_done_strobe    (sched_wr_done_strobe),
        .sched_wr_beats_done     (sched_wr_beats_done),
        .sched_wr_commit_strobe  (sched_wr_commit_strobe),
        .sched_wr_commit_beats   (sched_wr_commit_beats),
        .ctrlrd_valid            (ctrlrd_valid),
        .ctrlrd_ready            (ctrlrd_ready),
        .ctrlrd_addr             (ctrlrd_addr),
        .ctrlrd_data             (ctrlrd_data),
        .ctrlrd_mask             (ctrlrd_mask),
        .ctrlrd_error            (ctrlrd_error),
        .ctrlrd_idle             (ctrlrd_idle),
        .ctrlwr_valid            (ctrlwr_valid),
        .ctrlwr_ready            (ctrlwr_ready),
        .ctrlwr_addr             (ctrlwr_addr),
        .ctrlwr_data             (ctrlwr_data),
        .ctrlwr_error            (ctrlwr_error),
        .ctrlwr_idle             (ctrlwr_idle),
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
        .desc_alg_max            (8'd0),             // the FSM runs selector 0 only (rapids TASK-035)
        .start_req               (1'b1),
        .rd_beats_total          (w_rd_beats_total),
        .wr_beats_total          (w_wr_beats_total),
        .rd_base_valid           (w_rd_base_valid),
        .rd_base_addr            (w_rd_base_addr),
        .rd_base_ready           (w_rd_base_ready),
        .wr_base_valid           (w_wr_base_valid),
        .wr_base_addr            (w_wr_base_addr),
        .wr_base_ready           (w_wr_base_ready),
        .addrgen_start           (w_addrgen_start),
        .desc_head_valid         (w_desc_head_valid),
        /* verilator lint_off PINCONNECTEMPTY */
        .desc_head_packet        (),             // only scheduler_g pre-validates
        /* verilator lint_on PINCONNECTEMPTY */
        .desc_latched            (w_desc),
        .desc_ext_latched        (w_desc_ext),
        .desc_opcode             (w_desc_opcode),
        .desc_alg                (),
        .desc_is_ext             (w_desc_is_ext),
        .desc_hdr_only           (w_desc_hdr_only),
        .desc_rd_per_beat        (w_rd_per_beat),
        .desc_wr_per_beat        (w_wr_per_beat),
        .tile_bad                (w_tile_bad),
        .pkt_ok                  (w_pkt_ok),
        .exec_complete           (w_exec_complete),
        .hard_error              (w_hard_error),
        .timeout_escalate        (w_timeout_escalate),
        .channel_reset_active    (w_channel_reset_active)
    );

    //=========================================================================
    // Scheduler FSM
    //=========================================================================
    // FSM Flow: IDLE -> FETCH_DESC -> XFER_DATA -> COMPLETE -> (chain?) -> IDLE
    // Read and write engines run CONCURRENTLY in CH_XFER_DATA, so a transfer
    // larger than the SRAM buffer cannot deadlock.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_current_state <= rapids_pkg::CH_IDLE;
        end else begin
            r_current_state <= w_next_state;
        end
    )

    always_comb begin
        w_next_state = r_current_state;  // Default: hold current state

        // Priority 1: Channel reset overrides all other transitions
        if (w_channel_reset_active) begin
            w_next_state = rapids_pkg::CH_IDLE;
        // Priority 2: fatal faults (descriptor / engine / control errors) and an
        // escalated timeout wedge into sticky CH_ERROR. A soft timeout does not.
        end else if (w_hard_error || w_timeout_escalate) begin
            w_next_state = rapids_pkg::CH_ERROR;
        end else begin
            // Priority 3: Normal state machine transitions
            case (r_current_state)
                rapids_pkg::CH_IDLE: begin
                    if (w_desc_head_valid && cfg_channel_enable) begin
                        w_next_state = rapids_pkg::CH_FETCH_DESC;
                    end
                end

                rapids_pkg::CH_FETCH_DESC: begin
                    // Validate the latched descriptor, then start once the data
                    // paths can take its packet record (TASK-019); the record
                    // fires the cycle we leave.
                    if (w_desc.valid && !w_tile_bad) begin
                        if (w_pkt_ok) begin
                            w_next_state = rapids_pkg::CH_XFER_DATA;
                        end
                    end else begin
                        w_next_state = rapids_pkg::CH_ERROR;      // Invalid descriptor -> error
                    end
                end

                rapids_pkg::CH_XFER_DATA: begin
                    // All source beats read AND all destination beats committed
                    // (B responses), or the control operation finished.
                    if (w_exec_complete) begin
                        w_next_state = rapids_pkg::CH_COMPLETE;
                    end
                end

                rapids_pkg::CH_COMPLETE: begin
                    // Chain if next_descriptor_ptr != 0 AND last is not set
                    if (w_desc.next_descriptor_ptr != 32'h0 && !w_desc.last) begin
                        w_next_state = rapids_pkg::CH_NEXT_DESC;
                    end else begin
                        w_next_state = rapids_pkg::CH_IDLE;
                    end
                end

                rapids_pkg::CH_NEXT_DESC: begin
                    // The descriptor engine fetches next_descriptor_ptr
                    if (w_desc_head_valid) begin
                        w_next_state = rapids_pkg::CH_FETCH_DESC;
                    end
                end

                rapids_pkg::CH_ERROR: begin
                    // STICKY until a channel reset
                    w_next_state = rapids_pkg::CH_ERROR;
                end

                default: begin
                    w_next_state = rapids_pkg::CH_ERROR;
                end
            endcase
        end
    end

    // The skid head is taken in IDLE (channel enabled) and NEXT_DESC
    assign w_desc_take = ((r_current_state == rapids_pkg::CH_IDLE) && cfg_channel_enable) ||
                         (r_current_state == rapids_pkg::CH_NEXT_DESC);

    assign scheduler_state = r_current_state;

    //=========================================================================
    // Bytes -> beats (TASK-019)
    //=========================================================================
    // A direction moves ceil((offset + length) / BYTE_LANES) whole beats,
    // offset = the address's low bits. A zero-length descriptor moves no
    // beats whatever its offset, and a tile read request (header only) reads
    // no memory.
    logic [32:0] w_rd_span, w_wr_span;
    assign w_rd_span = 33'(w_desc.src_addr[OFF_W-1:0]) + 33'(w_desc.length) + 33'(BYTE_LANES - 1);
    assign w_wr_span = 33'(w_desc.dst_addr[OFF_W-1:0]) + 33'(w_desc.length) + 33'(BYTE_LANES - 1);
    assign w_rd_beats_total = ((w_desc.length == 32'd0) || w_desc_hdr_only) ? 32'd0
                                                                         : 32'(w_rd_span >> OFF_W);
    assign w_wr_beats_total = (w_desc.length == 32'd0) ? 32'd0 : 32'(w_wr_span >> OFF_W);

    //=========================================================================
    // Extended addressing: run-base generators
    //=========================================================================
    // Started once, on entry to CH_FETCH_DESC with an EXT descriptor
    // (w_addrgen_start): starting them for a legacy descriptor would push
    // bogus bases into the generator FIFO, which only clears on reset.
    generate
    if (USE_ROW_COL_MAJOR_ADDRESSING != 0) begin : g_addrgen
        stream_run_addr_gen #(
            .ADDR_WIDTH   (ADDR_WIDTH),
            .STRIDE_WIDTH (rapids_pkg::RAPIDS_ADDRGEN_STRIDE_WIDTH),
            .INDEX_WIDTH  (rapids_pkg::RAPIDS_ADDRGEN_INDEX_WIDTH),
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
            .cfg_wrap_mask_0 (ADDR_WIDTH'(rapids_pkg::rapids_wrap_log2_to_mask(w_desc_ext.rd_wrap0_log2))),
            .cfg_wrap_mask_1 (ADDR_WIDTH'(rapids_pkg::rapids_wrap_log2_to_mask(w_desc_ext.rd_wrap1_log2))),
            .cfg_inner_count (w_desc_ext.rd_inner_count),
            .cfg_total_beats (w_rd_beats_total),
            .o_base_valid    (w_rd_base_valid),
            .i_base_ready    (w_rd_base_ready),
            .o_base_addr     (w_rd_base_addr)
        );
        stream_run_addr_gen #(
            .ADDR_WIDTH   (ADDR_WIDTH),
            .STRIDE_WIDTH (rapids_pkg::RAPIDS_ADDRGEN_STRIDE_WIDTH),
            .INDEX_WIDTH  (rapids_pkg::RAPIDS_ADDRGEN_INDEX_WIDTH),
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
            .cfg_wrap_mask_0 (ADDR_WIDTH'(rapids_pkg::rapids_wrap_log2_to_mask(w_desc_ext.wr_wrap0_log2))),
            .cfg_wrap_mask_1 (ADDR_WIDTH'(rapids_pkg::rapids_wrap_log2_to_mask(w_desc_ext.wr_wrap1_log2))),
            .cfg_inner_count (w_desc_ext.wr_inner_count),
            .cfg_total_beats (w_wr_beats_total),
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

endmodule : scheduler
