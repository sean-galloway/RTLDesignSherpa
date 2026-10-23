// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_g
// Purpose: RAPIDS scheduler sequenced by gatling firmware (rapids-g, rapids
//          TASK-034).  Same ports as fub/scheduler.sv plus a sequencer
//          register window; the datapath is the same scheduler_core.
//
// What the firmware does, through the window (rapids_seq_g serves 4 or 8 of
// these from one gatling):
//   - the channel policy: take a descriptor, validate it, start it, finish
//     it, chain (next_ptr != 0 && !last) or go idle;
//   - the EXT run bases, pushed ahead into a 4-deep FIFO per direction
//     (the depth of stream_run_addr_gen's own FIFO).
// What stays hardware: everything at cycle rate (scheduler_core); the beat
// totals each direction moves (the FSM's bytes -> beats ceiling, loaded from
// the skid head on the cycle it is taken -- the firmware only reads them);
// and two
// interlocks that are not policy -- a channel reset forces CH_IDLE and a
// fatal fault (engine / descriptor / control error, escalated timeout, or
// the serving hart halted) forces CH_ERROR, both in the same cycle the FSM
// scheduler would take them, so the engine valids drop just as fast.
//
// Commands.  A CMD write names the next state.  An edge the table below does
// not allow is ignored and counted (CMD_ERR, sticky cmd_err in STATUS):
//   IDLE      -> FETCH_DESC  channel enabled and a descriptor at the skid
//                            head; the head is taken on the same edge
//   NEXT_DESC -> FETCH_DESC  a descriptor at the skid head; taken
//   FETCH     -> XFER_DATA   descriptor valid and not tile_bad: a PENDING
//                            request, taken the cycle pkt_ok holds, which is
//                            also the cycle the packet records fire
//   XFER      -> COMPLETE    exec_complete
//   COMPLETE  -> IDLE | NEXT_DESC
//   FETCH | XFER | COMPLETE | NEXT_DESC -> ERROR
// CH_ERROR is left only by a channel reset, as in the FSM scheduler.
//
// Register window (word index; reads combinational, the sequencer registers):
//   R 0  STATUS   [6:0] state  [7] attn  [8] desc at head  [9] channel enable
//                 [10] channel reset  [11] desc valid  [13:12] opcode
//                 [14] last  [15] gen_irq  [16] chain (next_ptr != 0)
//                 [17] tile_bad  [18] pkt_ok  [19] exec_complete
//                 [20] start pending  [21] cmd_err  [22] EXT  [23] header only
//                 [24] rd per-beat  [25] wr per-beat  [26] rd bases done
//                 [27] wr bases done
//   R 1-6  SRC_LO SRC_HI DST_LO DST_HI LENGTH NEXT_PTR
//   R 7-12 EXT chunk-1 words 0..5 (rd_stride_0, rd_stride_1,
//          {rd_wrap1, rd_wrap0, rd_inner}, wr_stride_0, wr_stride_1,
//          {wr_wrap1, wr_wrap0, wr_inner}), rapids_pkg::descriptor_ext_t
//   R 13 FIFO     [2:0] rd bases queued  [6:4] wr bases queued
//                 [15:8] CMD_ERR count (saturating)  [16] firmware packet pending
//   R 14 CFG      [15:0] BYTE_LANES  [19:16] OFF_W  [20] EN_READ
//                 [21] EN_WRITE  [22] USE_ROW_COL_MAJOR_ADDRESSING
//   R 15-18 the skid head: src low, dst low, length, descriptor [223:192]
//   R 19-20 the beat totals in use (read, write)
//   R 21 HEAD_SUM [0] head valid  [1] head last  [2] head next_ptr != 0
//                 [3] head open: a head not yet staged or declined, in a
//                 state where STAGE / DECLINE are legal
//   W 0  CMD      [6:0] next state (0 = none)  [8] rd bases done
//                 [9] wr bases done  [10] STAGE the head  [11] ARM this
//                 descriptor  [12] its ARM_NEXT  [13] run bases set up
//                 [14] DECLINE the head  [15] STAGE_ARM: take the staged
//                 head already armed  [16] its ARM_NEXT (both need [10])
//   W 1  FW_ERROR  send a firmware error packet: PktTypeError,
//                  RAPIDS_EVENT_FW_ERROR, data {this word, PKT_LO}
//   W 7  PKT_LO    the low payload word of the next firmware packet
//   W 8  FW_DEBUG  send a firmware debug packet: PktTypeDebug,
//                  RAPIDS_EVENT_FW_DEBUG, data {this word, PKT_LO}
//   W 2  reserved
// A firmware packet leaves on this channel's MonBus port in the first cycle
// scheduler_core sends none and mon_ready holds; one waits at a time, and a
// send while one waits is dropped and counted in CMD_ERR.
//   W 3  RD_BASE_LO  W 4 RD_BASE_HI    the HI write pushes {HI, LO}
//   W 5  WR_BASE_LO  W 6 WR_BASE_HI
// The bases FIFOs hold only while the channel is in FETCH_DESC or XFER_DATA;
// anywhere else (and on a channel reset) they are empty, so a stale base can
// never reach a later descriptor.  A push to a full FIFO is dropped and
// counted.
//
// attn (also the sequencer's per-slot event) is high when the firmware has
// something to do: IDLE with a descriptor (channel enabled), NEXT_DESC with
// a descriptor, FETCH_DESC not yet started (or turned tile_bad), XFER_DATA
// complete or wanting bases, COMPLETE.
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_mas (rapids-g)
// Subsystem: rapids fub_g
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module scheduler_g #(
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

    // Sequencer port (rapids_seq_g): one word-addressed register window.
    // Reads are combinational here; the sequencer registers them.
    input  logic                        seq_wr_en,
    input  logic [4:0]                  seq_wr_addr,            // word index
    input  logic [31:0]                 seq_wr_data,
    input  logic [4:0]                  seq_rd_addr,            // word index
    output logic [31:0]                 seq_rd_data,
    output logic                        seq_attn,               // needs the firmware
    input  logic                        seq_fault,              // the serving hart halted: fatal

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

    localparam int BASE_DEPTH = 4;

    //=========================================================================
    // Datapath (shared with the FSM scheduler)
    //=========================================================================

    rapids_pkg::channel_state_t  r_state;
    rapids_pkg::descriptor_t     w_desc;
    rapids_pkg::descriptor_ext_t w_desc_ext;
    logic [1:0]                  w_desc_opcode;
    logic                        w_desc_head_valid, w_desc_is_ext, w_desc_hdr_only;
    logic                        w_rd_per_beat, w_wr_per_beat;
    logic                        w_tile_bad, w_pkt_ok, w_exec_complete;
    logic                        w_hard_error, w_timeout_escalate, w_channel_reset_active;
    logic                        w_desc_take;
    logic [31:0]                 r_rd_beats_total, r_wr_beats_total;
    logic                        w_rd_base_valid, w_rd_base_ready, w_wr_base_valid, w_wr_base_ready;
    logic [ADDR_WIDTH-1:0]       w_rd_base_addr, w_wr_base_addr;
    logic                        r_start_pending;
    logic [255:0]                w_head_pkt;         // the skid head, before it is taken

    // Pre-validation (owner 2026-10-21): while a descriptor transfers, the
    // firmware validates the next one at the skid head and stages it
    // (STAGE), and decides this one's chain outcome (ARM). On completion the
    // hardware then takes the approved edges itself --
    // XFER -> COMPLETE -> IDLE/NEXT -> FETCH (the staged head) -> XFER -- in the FSM's own cycles. Anything not approved stops the
    // sequence and raises attention.
    // STAGE_ARM stages the head with its own chain outcome, so it is taken
    // already armed: a chain then runs with one firmware write per
    // descriptor, made any time before its predecessor completes, instead
    // of an ARM inside its own XFER_DATA, which a short descriptor outruns.
    logic                        r_armed, r_arm_next;    // this descriptor: complete on exec_complete, then IDLE / NEXT
    logic                        r_staged, r_declined;   // the head: validated and staged / refused
    logic                        r_stage_arm, r_stage_arm_next;  // the staged head: arm it on the take, and how
    logic                                   w_core_mon_valid;  // scheduler_core's MonBus, before the
    ocelus_common_pkg::monitor_packet_t     w_core_mon_packet; // firmware packets merge in
    ocelus_common_pkg::monbus_timestamp_t   w_core_mon_timestamp;
    logic                                   r_fw_valid;        // a firmware packet waiting
    logic                        r_gen_need;             // an EXT descriptor taken: its run bases are not set up yet
    logic                        r_rd_bases_done, r_wr_bases_done;   // the firmware has pushed every base

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
        .mon_valid               (w_core_mon_valid),
        .mon_ready               (mon_ready),
        .mon_packet              (w_core_mon_packet),
        .mon_timestamp           (w_core_mon_timestamp),
        .state                   (r_state),
        .desc_take               (w_desc_take),
        .start_req               (r_start_pending),
        .rd_beats_total          (r_rd_beats_total),
        .wr_beats_total          (r_wr_beats_total),
        .rd_base_valid           (w_rd_base_valid),
        .rd_base_addr            (w_rd_base_addr),
        .rd_base_ready           (w_rd_base_ready),
        .wr_base_valid           (w_wr_base_valid),
        .wr_base_addr            (w_wr_base_addr),
        .wr_base_ready           (w_wr_base_ready),
        .addrgen_start           (),
        .desc_head_valid         (w_desc_head_valid),
        .desc_head_packet        (w_head_pkt),
        .desc_latched            (w_desc),
        .desc_ext_latched        (w_desc_ext),
        .desc_opcode             (w_desc_opcode),
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

    assign scheduler_state = r_state;

    //=========================================================================
    // Commands
    //=========================================================================

    wire w_in_idle     = (r_state == rapids_pkg::CH_IDLE);
    wire w_in_fetch    = (r_state == rapids_pkg::CH_FETCH_DESC);
    wire w_in_xfer     = (r_state == rapids_pkg::CH_XFER_DATA);
    wire w_in_complete = (r_state == rapids_pkg::CH_COMPLETE);
    wire w_in_next     = (r_state == rapids_pkg::CH_NEXT_DESC);
    wire w_in_error    = (r_state == rapids_pkg::CH_ERROR);
    wire w_active      = w_in_fetch || w_in_xfer;       // the bases FIFOs hold only here

    wire       w_cmd_wr  = seq_wr_en && (seq_wr_addr == 5'd0);
    wire [6:0] w_cmd_st  = seq_wr_data[6:0];
    wire       w_cmd_go  = w_cmd_wr && (w_cmd_st != 7'd0);
    // CMD flag bits beside the state: [10] STAGE the head, [11] ARM this
    // descriptor ([12] = 1: then NEXT_DESC, 0: IDLE), [13] run bases set up,
    // [14] DECLINE the head (the normal path will take and judge it)
    wire       w_cmd_stage   = w_cmd_wr && seq_wr_data[10];
    wire       w_cmd_arm     = w_cmd_wr && seq_wr_data[11];
    wire       w_cmd_gen_ok  = w_cmd_wr && seq_wr_data[13];
    wire       w_cmd_decline = w_cmd_wr && seq_wr_data[14];
    // [15] STAGE_ARM ([16] its ARM_NEXT): with STAGE, the head is armed when taken
    wire       w_cmd_stage_arm = w_cmd_wr && seq_wr_data[15];

    wire w_fault = w_hard_error || w_timeout_escalate || seq_fault;

    logic w_cmd_legal;
    always_comb begin
        case (w_cmd_st)
            rapids_pkg::CH_FETCH_DESC: w_cmd_legal = w_desc_head_valid &&
                                                     ((w_in_idle && cfg_channel_enable) || w_in_next);
            rapids_pkg::CH_XFER_DATA:  w_cmd_legal = w_in_fetch && !r_start_pending &&
                                                     w_desc.valid && !w_tile_bad;
            rapids_pkg::CH_COMPLETE:   w_cmd_legal = w_in_xfer && w_exec_complete;
            rapids_pkg::CH_IDLE,
            rapids_pkg::CH_NEXT_DESC:  w_cmd_legal = w_in_complete;
            rapids_pkg::CH_ERROR:      w_cmd_legal = w_in_fetch || w_in_xfer || w_in_complete || w_in_next;
            default:                   w_cmd_legal = 1'b0;
        endcase
    end

    // Flags: ARM in XFER_DATA, once; STAGE / DECLINE while a descriptor is at
    // the head and not yet judged, before it is taken; run bases set up in
    // FETCH_DESC / XFER_DATA.
    wire w_head_open  = w_desc_head_valid && !r_staged && !r_declined &&
                        (w_in_xfer || w_in_complete || w_in_idle || w_in_next);
    wire w_flag_bad   = (w_cmd_arm && !(w_in_xfer && !r_armed)) ||
                        ((w_cmd_stage || w_cmd_decline) && !w_head_open) ||
                        (w_cmd_stage_arm && !w_cmd_stage) ||
                        (w_cmd_gen_ok && !w_active);
    wire w_live       = !w_channel_reset_active && !w_fault;

    wire w_cmd_ok  = w_cmd_go && w_cmd_legal && w_live;
    wire w_cmd_bad = ((w_cmd_go && !w_cmd_legal) || w_flag_bad) && w_live;

    // The automatic edges, in order: complete an armed descriptor, leave
    // COMPLETE the way the firmware armed, take a staged head.
    // An EXT descriptor completes automatically only once the firmware has
    // marked all its run bases out: it writes "done" after its last push, so
    // nothing of this descriptor (a push, a done bit) can land after the
    // hardware has taken the next one. Without it a fast descriptor finished
    // inside the firmware's refill, and its late done bit starved the next.
    wire w_bases_out     = !w_desc_is_ext ||
                           ((!EN_READ || r_rd_bases_done) && (!EN_WRITE || r_wr_bases_done));
    wire w_auto_complete = w_in_xfer && r_armed && w_exec_complete && w_bases_out;
    wire w_auto_leave    = w_in_complete && r_armed;
    wire w_auto_take     = r_staged && w_desc_head_valid &&
                           ((w_in_idle && cfg_channel_enable) || w_in_next);

    // The skid head is taken by the FETCH command or the automatic take, on
    // the edge the state leaves IDLE / NEXT_DESC.
    assign w_desc_take = (w_cmd_ok && (w_cmd_st == rapids_pkg::CH_FETCH_DESC)) ||
                         (w_live && !(w_in_fetch && r_start_pending) && w_auto_take);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state         <= rapids_pkg::CH_IDLE;
            r_start_pending <= 1'b0;
        end else if (w_channel_reset_active) begin
            r_state         <= rapids_pkg::CH_IDLE;          // interlock 1
            r_start_pending <= 1'b0;
        end else if (w_fault) begin
            r_state         <= rapids_pkg::CH_ERROR;         // interlock 2
            r_start_pending <= 1'b0;
        end else if (w_in_fetch && r_start_pending && w_pkt_ok && w_desc.valid && !w_tile_bad) begin
            r_state         <= rapids_pkg::CH_XFER_DATA;     // the records fire this cycle
            r_start_pending <= 1'b0;
        end else if (w_auto_complete) begin
            r_state         <= rapids_pkg::CH_COMPLETE;
        end else if (w_auto_leave) begin
            r_state         <= r_arm_next ? rapids_pkg::CH_NEXT_DESC : rapids_pkg::CH_IDLE;
        end else if (w_auto_take) begin
            r_state         <= rapids_pkg::CH_FETCH_DESC;    // validated: start at once
            r_start_pending <= 1'b1;
        end else if (w_cmd_ok) begin
            if (w_cmd_st == rapids_pkg::CH_XFER_DATA) begin
                r_start_pending <= 1'b1;
            end else begin
                r_state         <= rapids_pkg::channel_state_t'(w_cmd_st);
                r_start_pending <= 1'b0;
            end
        end
    )

    // Pre-validation state
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_armed        <= 1'b0;
            r_arm_next     <= 1'b0;
            r_staged       <= 1'b0;
            r_declined     <= 1'b0;
            r_gen_need     <= 1'b0;
            r_stage_arm      <= 1'b0;
            r_stage_arm_next <= 1'b0;
        end else if (!w_live) begin
            r_armed    <= 1'b0;
            r_staged   <= 1'b0;
            r_declined <= 1'b0;
            r_gen_need <= 1'b0;
            r_stage_arm <= 1'b0;
        end else begin
            if (w_cmd_arm && !w_flag_bad) begin
                r_armed    <= 1'b1;
                r_arm_next <= seq_wr_data[12];
            end else if (w_auto_leave) begin
                r_armed    <= 1'b0;
            end
            if (w_desc_take) begin
                r_staged    <= 1'b0;
                r_declined  <= 1'b0;
                // a head staged with STAGE_ARM starts armed (only the
                // automatic take can find it staged)
                r_armed     <= r_staged && r_stage_arm;
                r_arm_next  <= r_stage_arm_next;
                r_stage_arm <= 1'b0;
                r_gen_need  <= 1'b1;             // read as EXT && gen_need
            end else begin
                if (w_cmd_stage && !w_flag_bad) begin
                    r_staged         <= 1'b1;
                    r_stage_arm      <= w_cmd_stage_arm;
                    r_stage_arm_next <= seq_wr_data[16];
                end
                if (w_cmd_decline && !w_flag_bad) r_declined <= 1'b1;
                if (w_cmd_gen_ok && !w_flag_bad)  r_gen_need <= 1'b0;
            end
        end
    )

    // Illegal commands and dropped pushes: sticky flag plus a saturating count
    logic       r_cmd_err;
    logic [7:0] r_cmd_err_cnt;
    logic       w_push_drop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cmd_err     <= 1'b0;
            r_cmd_err_cnt <= 8'h0;
        end else if (w_channel_reset_active) begin
            r_cmd_err     <= 1'b0;
            r_cmd_err_cnt <= 8'h0;
        end else if (w_cmd_bad || w_push_drop) begin
            r_cmd_err     <= 1'b1;
            if (!(&r_cmd_err_cnt)) r_cmd_err_cnt <= r_cmd_err_cnt + 8'h1;
        end
    )

    //=========================================================================
    // Beat totals (hardware) and the firmware's bases-done flags
    //=========================================================================
    // A direction moves ceil((offset + length) / BYTE_LANES) whole beats,
    // offset = the address's low bits -- fub/scheduler.sv's formula, applied
    // to the skid head and loaded on the edge the head is taken (by the
    // FETCH command or the automatic take), so the totals are in place when
    // the latched descriptor is. A zero-length descriptor moves nothing, a
    // tile read request (header only) reads no memory, and a disabled
    // direction moves nothing.
    localparam int H_SRC_LO = 0;
    localparam int H_DST_LO = 64;
    localparam int H_LEN_LO = 128;

    logic [31:0] w_head_len;
    logic        w_head_hdr_only;
    logic [32:0] w_head_rd_span, w_head_wr_span;
    logic [31:0] w_head_rd_beats, w_head_wr_beats;

    assign w_head_len      = w_head_pkt[H_LEN_LO +: 32];
    assign w_head_hdr_only = (TILE_HDR != 0) && w_head_pkt[rapids_pkg::DESC_TILE_OP];
    assign w_head_rd_span  = 33'(w_head_pkt[H_SRC_LO +: OFF_W]) + 33'(w_head_len) + 33'(BYTE_LANES - 1);
    assign w_head_wr_span  = 33'(w_head_pkt[H_DST_LO +: OFF_W]) + 33'(w_head_len) + 33'(BYTE_LANES - 1);
    assign w_head_rd_beats = (!EN_READ || (w_head_len == 32'd0) || w_head_hdr_only) ? 32'd0
                                                                                  : 32'(w_head_rd_span >> OFF_W);
    assign w_head_wr_beats = (!EN_WRITE || (w_head_len == 32'd0)) ? 32'd0 : 32'(w_head_wr_span >> OFF_W);


    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_beats_total <= 32'h0;
            r_wr_beats_total <= 32'h0;
            r_rd_bases_done  <= 1'b0;
            r_wr_bases_done  <= 1'b0;
        end else begin
            if (w_desc_take) begin
                r_rd_beats_total <= w_head_rd_beats;
                r_wr_beats_total <= w_head_wr_beats;
            end
            if (!w_active || w_channel_reset_active) begin
                r_rd_bases_done <= 1'b0;
                r_wr_bases_done <= 1'b0;
            end else if (w_cmd_wr) begin
                if (seq_wr_data[8]) r_rd_bases_done <= 1'b1;
                if (seq_wr_data[9]) r_wr_bases_done <= 1'b1;
            end
        end
    )

    //=========================================================================
    // EXT run-base FIFOs (firmware -> scheduler_core)
    //=========================================================================

    logic [2:0] w_rd_cnt, w_wr_cnt;
    logic       w_rd_drop, w_wr_drop;
    wire        w_flush = !w_active || w_channel_reset_active;

    scheduler_g_base_fifo #(.ADDR_WIDTH(ADDR_WIDTH), .DEPTH(BASE_DEPTH)) u_rd_bases (
        .clk       (clk),
        .rst_n     (rst_n),
        .flush     (w_flush),
        .lo_wr     (seq_wr_en && (seq_wr_addr == 5'd3)),
        .hi_wr     (seq_wr_en && (seq_wr_addr == 5'd4)),
        .wr_data   (seq_wr_data),
        .drop      (w_rd_drop),
        .count     (w_rd_cnt),
        .rd_valid  (w_rd_base_valid),
        .rd_ready  (w_rd_base_ready),
        .rd_addr   (w_rd_base_addr)
    );

    scheduler_g_base_fifo #(.ADDR_WIDTH(ADDR_WIDTH), .DEPTH(BASE_DEPTH)) u_wr_bases (
        .clk       (clk),
        .rst_n     (rst_n),
        .flush     (w_flush),
        .lo_wr     (seq_wr_en && (seq_wr_addr == 5'd5)),
        .hi_wr     (seq_wr_en && (seq_wr_addr == 5'd6)),
        .wr_data   (seq_wr_data),
        .drop      (w_wr_drop),
        .count     (w_wr_cnt),
        .rd_valid  (w_wr_base_valid),
        .rd_ready  (w_wr_base_ready),
        .rd_addr   (w_wr_base_addr)
    );

    //=========================================================================
    // Firmware packets (FW_DEBUG / FW_ERROR), merged onto the MonBus port
    //=========================================================================
    // scheduler_core's packets are one-cycle pulses and always win the cycle;
    // a firmware packet waits for a cycle with none and mon_ready.

    ocelus_common_pkg::monitor_packet_t     r_fw_packet;
    ocelus_common_pkg::monbus_timestamp_t   r_fw_timestamp;
    logic [31:0]                            r_fw_lo;

    wire w_fw_err  = seq_wr_en && (seq_wr_addr == 5'd1);
    wire w_fw_dbg  = seq_wr_en && (seq_wr_addr == 5'd8);
    wire w_fw_out  = r_fw_valid && !w_core_mon_valid && mon_ready;
    wire w_fw_take = (w_fw_err || w_fw_dbg) && (!r_fw_valid || w_fw_out);
    wire w_fw_drop = (w_fw_err || w_fw_dbg) && !w_fw_take;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_fw_valid     <= 1'b0;
            r_fw_packet    <= '0;
            r_fw_timestamp <= '0;
            r_fw_lo        <= 32'h0;
        end else begin
            if (seq_wr_en && (seq_wr_addr == 5'd7)) r_fw_lo <= seq_wr_data;
            if (w_fw_take) begin
                r_fw_valid     <= 1'b1;
                r_fw_packet    <= ocelus_common_pkg::create_monitor_packet(
                                      w_fw_err ? ocelus_common_pkg::PktTypeError : ocelus_common_pkg::PktTypeDebug,
                                      ocelus_common_pkg::PROTOCOL_CORE,
                                      w_fw_err ? rapids_pkg::RAPIDS_EVENT_FW_ERROR : rapids_pkg::RAPIDS_EVENT_FW_DEBUG,
                                      MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID,
                                      {seq_wr_data, r_fw_lo});
                r_fw_timestamp <= i_mon_time;
            end else if (w_fw_out) begin
                r_fw_valid     <= 1'b0;
            end
        end
    )

    assign mon_valid     = w_core_mon_valid || w_fw_out;
    assign mon_packet    = w_core_mon_valid ? w_core_mon_packet    : r_fw_packet;
    assign mon_timestamp = w_core_mon_valid ? w_core_mon_timestamp : r_fw_timestamp;

    assign w_push_drop = w_rd_drop || w_wr_drop || w_fw_drop;

    //=========================================================================
    // Attention and the read window
    //=========================================================================

    wire w_base_want = w_desc_is_ext &&
                       ((EN_READ  && !r_rd_bases_done && (w_rd_cnt < 3'(BASE_DEPTH))) ||
                        (EN_WRITE && !r_wr_bases_done && (w_wr_cnt < 3'(BASE_DEPTH))));

    wire w_gen_need = r_gen_need && w_desc_is_ext;

    assign seq_attn = w_live &&
                      ((w_in_idle  && cfg_channel_enable && w_desc_head_valid && !r_staged) ||
                       (w_in_next  && w_desc_head_valid && !r_staged) ||
                       (w_in_fetch && (!r_start_pending || w_tile_bad)) ||
                       (w_in_xfer  && (!r_armed || w_gen_need || (w_base_want && !w_gen_need) ||
                                       (w_desc_head_valid && !r_staged && !r_declined))) ||
                       (w_in_complete && !r_armed));

    logic [31:0] w_status;
    assign w_status = {r_declined, w_gen_need, r_staged, r_armed,
                        r_wr_bases_done, r_rd_bases_done, w_wr_per_beat, w_rd_per_beat,
                        w_desc_hdr_only, w_desc_is_ext, r_cmd_err, r_start_pending,
                        w_exec_complete, w_pkt_ok, w_tile_bad,
                        (w_desc.next_descriptor_ptr != 32'h0),
                        w_desc.gen_irq, w_desc.last, w_desc_opcode, w_desc.valid,
                        w_channel_reset_active, cfg_channel_enable, w_desc_head_valid,
                        seq_attn, r_state};

    logic [255:0] w_ext_raw;
    assign w_ext_raw = w_desc_ext;

    always_comb begin
        case (seq_rd_addr)
            5'd0:    seq_rd_data = w_status;
            5'd1:    seq_rd_data = w_desc.src_addr[31:0];
            5'd2:    seq_rd_data = w_desc.src_addr[63:32];
            5'd3:    seq_rd_data = w_desc.dst_addr[31:0];
            5'd4:    seq_rd_data = w_desc.dst_addr[63:32];
            5'd5:    seq_rd_data = w_desc.length;
            5'd6:    seq_rd_data = w_desc.next_descriptor_ptr;
            5'd7:    seq_rd_data = w_ext_raw[ 31:  0];
            5'd8:    seq_rd_data = w_ext_raw[ 63: 32];
            5'd9:    seq_rd_data = w_ext_raw[ 95: 64];
            5'd10:   seq_rd_data = w_ext_raw[127: 96];
            5'd11:   seq_rd_data = w_ext_raw[159:128];
            5'd12:   seq_rd_data = w_ext_raw[191:160];
            5'd13:   seq_rd_data = {15'h0, r_fw_valid, r_cmd_err_cnt, 1'b0, w_wr_cnt, 1'b0, w_rd_cnt};
            5'd14:   seq_rd_data = {8'h0, (TILE_HDR != 0), (USE_ROW_COL_MAJOR_ADDRESSING != 0), EN_WRITE, EN_READ,
                                    4'(OFF_W), 16'(BYTE_LANES)};
            5'd15:   seq_rd_data = w_head_pkt[ 31:  0];    // the head: src low word
            5'd16:   seq_rd_data = w_head_pkt[ 95: 64];    // dst low word
            5'd17:   seq_rd_data = w_head_pkt[159:128];    // length
            5'd18:   seq_rd_data = w_head_pkt[223:192];    // valid, gen_irq, last, ..., opcode, type, ptype, op
            5'd19:   seq_rd_data = r_rd_beats_total;       // the beat totals in use
            5'd20:   seq_rd_data = r_wr_beats_total;
            5'd21:   seq_rd_data = {28'h0, w_head_open,                                       // HEAD_SUM: open,
                                    (w_head_pkt[191:160] != 32'h0),                       // chain,
                                    w_head_pkt[194], w_head_pkt[192]};                    // last, valid
            default: seq_rd_data = 32'h0;
        endcase
    end

endmodule : scheduler_g
